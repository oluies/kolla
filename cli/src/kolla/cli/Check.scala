package kolla.cli

import cats.effect.IO
import fs2.Stream
import kolla.kernel.{KernelProfile, Name}
import kolla.leanexport.*

/** The driver loop: `Replay` plus the yielding and the output.
  *
  * The same loop serves the JVM and the native binary. `IO.cede` between
  * batches keeps a long file interruptible, which on the JVM also lets the
  * runtime keep its promises about fairness.
  */
object Check:

  /** Declarations per `IO.cede`. */
  val cedeEvery: Int = 32

  final case class Result(
      tally: ReplayTally,
      wallNanos: Long,
      lateAmbient: List[Name] = Nil,
      admittedUnchecked: Int = 0,
      reusedFromCache: Int = 0,
      /** The environment the replay ended with, which `--eval` reduces against. */
      environment: kolla.kernel.Environment = kolla.kernel.Environment.empty
  )

  /** Why a file produced no verdict.
    *
    * `Exhausted` is kept apart from `Unreadable` because a script can act on
    * it: the file is well formed and kolla ran out of room, which is a
    * different thing from a file it cannot parse. See docs/semantics.md F8.
    */
  enum Failure:
    case Unreadable(reason: String)
    case Exhausted(reason: String)

    def message: String = this match
      case Unreadable(m) => m
      case Exhausted(m)  => m

  /** How far a run has got, for the periodic note on stderr. */
  final case class Progress(declarations: Long, bytesRead: Long)

  /** Declarations between progress notes. */
  val progressEvery: Long = 25000L

  /** Carries an `OutOfMemoryError` out as an ordinary failure.
    *
    * `IO.attempt` does not catch an `OutOfMemoryError`: cats-effect treats it
    * as fatal and takes it straight to the runtime, which prints it and exits
    * 1 — the code for a rejected declaration. So it is caught in the frame
    * that throws it and rethrown as this, which is `NonFatal` and therefore
    * visible to `attempt`. No stack trace is captured, since the heap is
    * already full. See docs/semantics.md F8.
    */
  private final class OutOfRoom(val declarations: Long)
      extends RuntimeException("exhausted", null, false, false)

  /** Checks one already-read export.
    *
    * `emit` receives each declaration's line, so the caller decides whether
    * that is a JSON object, a name, or nothing at all.
    */
  def run(
      items: Vector[ExportItem],
      profile: KernelProfile,
      abortOnReject: Boolean,
      emit: (Name, ReplayOutcome, Long) => IO[Unit],
      check: Name => Boolean = _ => true
  ): IO[Result] =
    IO.monotonic.flatMap { start =>
      val replay = new Replay(profile, true, Int.MaxValue, check)
      items.foreach(replay.feed)
      replay.finish()
      var tally  = ReplayTally()

      def loop(n: Int): IO[Unit] =
        if !replay.hasNext then IO.unit
        else if abortOnReject && tally.rejected > 0 then
          IO {
            tally = tally.addNotReached(replay.skipRest().map(_.length).sum)
          }
        else
          val yieldNow = if n % cedeEvery == 0 then IO.cede else IO.unit
          yieldNow *> IO {
            val t0   = System.nanoTime()
            val step = replay.next()
            (step, System.nanoTime() - t0)
          }.flatMap { (step, took) =>
            tally = tally.add(step)
            step.names.traverse_(d => emit(d, step.outcome, took)) *> loop(n + 1)
          }

      loop(0) *> IO.monotonic.map(end =>
        Result(tally, (end - start).toNanos, Nil, replay.admittedUnchecked, 0, replay.environment)
      )
    }

  extension [A](xs: List[A])
    private def traverse_(f: A => IO[Unit]): IO[Unit] =
      xs.foldLeft(IO.unit)((acc, a) => acc *> f(a))

  /** Checks an export as it is read, holding no more than the hoisting window.
    *
    * The reader already streams; this feeds `Replay` from it rather than
    * materialising the file, which is what makes a Mathlib-scale export
    * checkable at all. See docs/semantics.md P13.
    */
  def stream(
      name: String,
      bytes: Stream[IO, Byte],
      profile: KernelProfile,
      abortOnReject: Boolean,
      emit: (Name, ReplayOutcome, Long) => IO[Unit],
      progress: Option[Progress => IO[Unit]] = None,
      check: Name => Boolean = _ => true,
      cache: Option[ReplayCache] = None,
      /** Run periodically and once at the end, so that a run which dies
        * partway leaves behind the digests it did accept.
        */
      checkpoint: Option[IO[Unit]] = None,
      /** Called with a step's names before it is taken, and again with the
        * time it took once it returns. A step that never returns is reported
        * only by the first call, which is the point. See docs/semantics.md K20.
        */
      trace: Option[(List[Name], Option[Long]) => IO[Unit]] = None,
      maxSteps: Long = kolla.kernel.TypeChecker.defaultMaxSteps,
      /** The environment to check on top of; see `Serve`. */
      initial: kolla.kernel.Environment = kolla.kernel.Environment.empty
  ): IO[Either[Failure, Result]] =
    IO.monotonic.flatMap { start =>
      val replay  = new Replay(profile, true, Replay.defaultHoistWindow, check, cache, maxSteps, initial)
      var tally   = ReplayTally()
      var read    = 0L
      var seen    = 0L
      var noted   = 0L
      var batches = 0

      // Both of these read state the surrounding `IO`s mutate, so each has to
      // be built at run time: `IO(...) *> drain()` would call `drain()` while
      // the first effect was still unevaluated and always see an empty buffer.
      def note: IO[Unit] = IO.defer {
        if seen - noted < progressEvery then IO.unit
        else
          noted = seen
          progress.fold(IO.unit)(f => f(Progress(seen, read))) *> checkpoint.getOrElse(IO.unit)
      }

      def drain(): IO[Unit] = IO.defer {
        if abortOnReject && tally.rejected > 0 then
          // `lean4checker` aborts, so the rest is not reached rather than
          // accepted. The stream keeps running to count what was skipped.
          IO { tally = tally.addNotReached(replay.skipRest().map(_.length).sum) }
        else if !replay.hasNext then IO.unit
        else
          batches += 1
          val yieldNow = if batches % cedeEvery == 0 then IO.cede else IO.unit
          val announce = trace.fold(IO.unit)(f => IO(replay.peekNames).flatMap(ns => f(ns, None)))
          yieldNow *> announce *> IO {
            try
              val t0 = System.nanoTime()
              val st = replay.next()
              (st, System.nanoTime() - t0)
            catch case _: OutOfMemoryError => throw new OutOfRoom(seen)
          }.flatMap { (st, took) =>
            val done = trace.fold(IO.unit)(f => f(st.names, Some(took)))
            tally = tally.add(st)
            seen += st.names.length
            done *> st.names.traverse_(d => emit(d, st.outcome, took)) *> drain()
          }
      }

      // The reader is driven here rather than through `ExportReader.pipe` for
      // one reason: the export's index tables are the largest thing a run
      // allocates, so that is where it runs out of memory, and inside `pipe`
      // the throw happens in fs2's frame where it cannot be caught. The three
      // lines of wiring are the price of being able to report exhaustion.
      val reader = new ExportReader(None, retainItems = false)

      val lines =
        bytes.chunks
          .evalTap(c => IO { read += c.size })
          .unchunks
          .through(fs2.text.utf8.decode)
          .through(fs2.text.lines)

      lines.chunks
        .evalMap { chunk =>
          IO {
            try
              chunk.foreach(reader.feed)
              reader.drain().foreach(replay.feed)
            catch case _: OutOfMemoryError => throw new OutOfRoom(seen)
          } *> drain() *> note
        }
        .compile
        .drain
        .flatMap(_ =>
          IO {
            try
              reader.finish()
              reader.drain().foreach(replay.feed)
              replay.finish()
            catch case _: OutOfMemoryError => throw new OutOfRoom(seen)
          } *> drain()
        )
        // The checkpoint runs whether or not the body succeeded, so an
        // exhausted run still keeps what it accepted.
        .guarantee(checkpoint.getOrElse(IO.unit))
        .attempt
        .flatMap {
          case Right(_) =>
            IO.monotonic.map(end =>
              Right(
                Result(
                  tally, (end - start).toNanos, replay.lateAmbientConstants,
                  replay.admittedUnchecked, replay.reusedFromCache, replay.environment
                )
              )
            )
          case Left(e: OutOfRoom) =>
            IO.pure(Left(Failure.Exhausted(s"$name: ran out of memory after ${e.declarations} declarations")))
          case Left(_: OutOfMemoryError) =>
            IO.pure(Left(Failure.Exhausted(s"$name: ran out of memory after $seen declarations")))
          case Left(e) =>
            IO.pure(Left(Failure.Unreadable(s"$name: ${e.getMessage}")))
        }
    }

  /** Reads an export and checks it, turning a read failure into a left. */
  def file(
      name: String,
      contents: String,
      profile: KernelProfile,
      abortOnReject: Boolean,
      emit: (Name, ReplayOutcome, Long) => IO[Unit]
  ): IO[Either[String, Result]] =
    IO(ExportReader.fromString(contents)).attempt.flatMap {
      case Left(e)    => IO.pure(Left(s"$name: ${e.getMessage}"))
      case Right(env) => run(env.items, profile, abortOnReject, emit, _ => true).map(Right(_))
    }
