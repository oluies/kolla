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
      hoist: Boolean = true,
      /** Declarations checked at once. Above one, the checks a step can defer
        * (K30) run on that many fibers against the environment from before the
        * step, and the results are put back in file order; the verdicts and
        * their order are the sequential run's. With `stopOnFirstRejection`
        * the results are cut at the first rejection afterwards, which is the
        * same report the sequential stop gives, at the cost of having checked
        * what follows it.
        */
      jobs: Int = 1
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

      def resultsOf(names: List[Name], outcome: ReplayOutcome, took: Long): List[DeclResult] =
        val v = verdictOf(outcome)
        val trace = outcome match
          case ReplayOutcome.Rejected(_, t) => t
          case _                            => Nil
        names.map(d => DeclResult(d, v, took, trace))

      /** The reader takes every step now, deferring what it can; the deferred
        * checks then run `jobs` at a time, and `parTraverseN` keeps their order.
        * In comparison mode the steps after the first rejection are then
        * reported as not reached, as `skipRest` reports them.
        */
      def parallel: IO[Unit] =
        import cats.effect.implicits.*
        val deferred = Vector.newBuilder[ReplayDeferred]
        def collect(n: Int): IO[Unit] =
          if !replay.hasNext then IO.unit
          else
            val yieldNow = if n % cedeEvery == 0 then IO.cede else IO.unit
            yieldNow *> IO { deferred += replay.nextDeferred() }.flatMap(_ => collect(n + 1))
        collect(0).flatMap { _ =>
          deferred.result().parTraverseN(jobs) { d =>
            IO.blocking {
              val t0      = System.nanoTime()
              val outcome = d.run()
              val took    = System.nanoTime() - t0
              observeHeap()
              (d.names, outcome, took)
            }
          }.map { steps =>
            steps.foreach { (names, outcome, took) =>
              if stopOnFirstRejection && rejected then
                names.foreach(d =>
                  results += DeclResult(d, Verdict.NotChecked("not reached: an earlier declaration was rejected"), 0L)
                )
              else
                results ++= resultsOf(names, outcome, took)
                if outcome.isRejection then rejected = true
            }
          }
        }

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

      val run = if jobs > 1 then parallel else loop(0)
      run.flatMap { _ =>
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
