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
      admittedUnchecked: Int = 0
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

      loop(0) *> IO.monotonic.map(end => Result(tally, (end - start).toNanos, Nil, replay.admittedUnchecked))
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
      check: Name => Boolean = _ => true
  ): IO[Either[Failure, Result]] =
    IO.monotonic.flatMap { start =>
      val replay  = new Replay(profile, true, Replay.defaultHoistWindow, check)
      var tally   = ReplayTally()
      var read    = 0L
      var seen    = 0L
      var noted   = 0L
      var batches = 0

      // Both of these read state the surrounding `IO`s mutate, so each has to
      // be built at run time: `IO(...) *> drain()` would call `drain()` while
      // the first effect was still unevaluated and always see an empty buffer.
      def note: IO[Unit] = IO.defer {
        progress match
          case Some(f) if seen - noted >= progressEvery =>
            noted = seen
            f(Progress(seen, read))
          case _ => IO.unit
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
          yieldNow *> IO {
            val t0 = System.nanoTime()
            val st = replay.next()
            (st, System.nanoTime() - t0)
          }.flatMap { (st, took) =>
            tally = tally.add(st)
            seen += st.names.length
            st.names.traverse_(d => emit(d, st.outcome, took)) *> drain()
          }
      }

      val items =
        bytes.chunks
          .evalTap(c => IO { read += c.size })
          .unchunks
          .through(fs2.text.utf8.decode)
          .through(fs2.text.lines)
          .through(ExportReader.pipe[IO]())

      items.chunks
        .evalMap(chunk => IO(chunk.foreach(replay.feed)) *> drain() *> note)
        .compile
        .drain
        .flatMap(_ => IO(replay.finish()) *> drain())
        .attempt
        .flatMap {
          case Right(_) =>
            IO.monotonic.map(end =>
              Right(Result(tally, (end - start).toNanos, replay.lateAmbientConstants, replay.admittedUnchecked))
            )
          case Left(e: OutOfMemoryError) =>
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
