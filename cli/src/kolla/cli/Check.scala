package kolla.cli

import cats.effect.IO
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

  final case class Result(tally: ReplayTally, wallNanos: Long)

  /** Checks one already-read export.
    *
    * `emit` receives each declaration's line, so the caller decides whether
    * that is a JSON object, a name, or nothing at all.
    */
  def run(
      items: Vector[ExportItem],
      profile: KernelProfile,
      abortOnReject: Boolean,
      emit: (Name, ReplayOutcome, Long) => IO[Unit]
  ): IO[Result] =
    IO.monotonic.flatMap { start =>
      val replay = new Replay(items, profile)
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

      loop(0) *> IO.monotonic.map(end => Result(tally, (end - start).toNanos))
    }

  extension [A](xs: List[A])
    private def traverse_(f: A => IO[Unit]): IO[Unit] =
      xs.foldLeft(IO.unit)((acc, a) => acc *> f(a))

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
      case Right(env) => run(env.items, profile, abortOnReject, emit).map(Right(_))
    }
