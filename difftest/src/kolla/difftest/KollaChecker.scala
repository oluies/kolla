package kolla.difftest

import cats.effect.IO
import kolla.kernel.*
import kolla.leanexport.*

/** Runs kolla over an export and records a verdict per declaration.
  *
  * The checking is `Replay`, which is pure and shared with `cli` and `web`; this
  * is the driver loop around it. `IO` appears only here: it yields with
  * `IO.cede` between declarations so a long corpus stays interruptible.
  */
object KollaChecker:

  val name = "kolla"

  /** Declarations per `IO.cede`. */
  val cedeEvery: Int = 32

  /** The verdict a replay outcome amounts to.
    *
    * `CarriedOver` is `NotChecked`, never agreement: the export file supplied
    * the constant and the kernel did not re-derive it. See docs/semantics.md K8.
    * A `Cached` outcome is `NotChecked` for the same reason, and the platform
    * does not pass a cache in the first place.
    */
  def verdictOf(outcome: ReplayOutcome): Verdict = outcome match
    case ReplayOutcome.Checked            => Verdict.Accepted
    case ReplayOutcome.CarriedOver(r)     => Verdict.NotChecked(r)
    // The platform never caches: a comparison has to be this run's own
    // verdict, or it is comparing a reference against a stored answer.
    case ReplayOutcome.Cached(d)          => Verdict.NotChecked(s"cached, digest $d")
    case ReplayOutcome.Rejected(r, _)     => Verdict.Rejected(r)
    case ReplayOutcome.Failed(r)          => Verdict.Error(r)

  def check(
      items: Vector[ExportItem],
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      platform: String = "jvm",
      stopOnFirstRejection: Boolean = false,
      expectRejection: Boolean = false,
      hoist: Boolean = true
  ): IO[CheckerRun] =
    IO.monotonic.flatMap { start =>
      val replay  = new Replay(items, profile, hoist)
      val results = Vector.newBuilder[DeclResult]
      var peak     = 0L
      var rejected = false

      def observeHeap(): Unit =
        val rt   = Runtime.getRuntime
        val used = rt.totalMemory() - rt.freeMemory()
        if used > peak then peak = used

      def loop(n: Int): IO[Unit] =
        if !replay.hasNext then IO.unit
        else if stopOnFirstRejection && rejected then
          // `lean4checker` aborts on the first rejection, so in comparison mode
          // the remaining declarations are not reached rather than accepted.
          IO {
            replay
              .skipRest()
              .foreach(
                _.foreach(d =>
                  results += DeclResult(d, Verdict.NotChecked("not reached: an earlier declaration was rejected"), 0L)
                )
              )
          }
        else
          val yieldNow = if n % cedeEvery == 0 then IO.cede else IO.unit
          yieldNow *> IO {
            val t0   = System.nanoTime()
            val step = replay.next()
            val took = System.nanoTime() - t0
            val v    = verdictOf(step.outcome)
            val trace = step.outcome match
              case ReplayOutcome.Rejected(_, t) => t
              case _                            => Nil
            step.names.foreach(d => results += DeclResult(d, v, took, trace))
            if step.outcome.isRejection then rejected = true
            observeHeap()
          }.flatMap(_ => loop(n + 1))

      loop(0).flatMap { _ =>
        IO.monotonic.map { end =>
          CheckerRun(
            name, toolchain, corpus, platform,
            results.result(), (end - start).toNanos, peak,
            expectRejection = expectRejection
          )
        }
      }
    }

  /** Reads an export file and checks it. */
  def checkFile(
      path: java.nio.file.Path,
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      platform: String = "jvm",
      stopOnFirstRejection: Boolean = false,
      expectRejection: Boolean = false
  ): IO[CheckerRun] =
    IO.blocking(Layout.readFile(path)).flatMap { contents =>
      IO(ExportReader.fromString(contents)).attempt.flatMap {
        case Left(e) =>
          IO.pure(CheckerRun(name, toolchain, corpus, platform, Vector.empty, 0L, 0L, Some(e.getMessage)))
        case Right(env) =>
          check(env.items, profile, toolchain, corpus, platform, stopOnFirstRejection, expectRejection)
      }
    }
