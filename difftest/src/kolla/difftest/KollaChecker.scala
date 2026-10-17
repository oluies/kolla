package kolla.difftest

import cats.effect.IO
import kolla.kernel.*
import kolla.leanexport.*
import scala.collection.mutable

/** Runs kolla over an export and records a verdict per declaration.
  *
  * The driver loop is the only place `IO` appears: it yields with `IO.cede`
  * between declarations so a long corpus stays interruptible, and each
  * declaration gets its own `TypeChecker`, as `environment::add_*` does.
  */
object KollaChecker:

  val name = "kolla"

  /** Declarations per `IO.cede`. */
  val cedeEvery: Int = 32

  def check(
      items: Vector[ExportItem],
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      platform: String = "jvm",
      stopOnFirstRejection: Boolean = false
  ): IO[CheckerRun] =
    IO.monotonic.flatMap { start =>
      val results = Vector.newBuilder[DeclResult]
      val dc      = new DeclarationChecker(profile)
      var env        = Environment.empty
      var peak       = 0L
      var rejectedAt = -1

      def observeHeap(): Unit =
        val rt   = Runtime.getRuntime
        val used = rt.totalMemory() - rt.freeMemory()
        if used > peak then peak = used

      /** One declaration, timed. Rejection is a verdict, not a failure.
        *
        * A rejected declaration is still carried into the environment, unchecked,
        * by `recover`. Leaving it out would make every later declaration that
        * mentions it fail with an unknown constant, turning one disagreement into
        * a cascade of spurious ones. See docs/semantics.md T2.
        */
      def one(
          step: () => (Environment, CheckOutcome),
          names: List[Name],
          recover: Environment => Environment = identity
      ): Boolean =
        val t0 = System.nanoTime()
        val (verdict, nextEnv, trace) =
          try
            val (e, outcome) = step()
            val v = outcome match
              case CheckOutcome.Checked  => Verdict.Accepted
              case CheckOutcome.TypeOnly => Verdict.NotChecked("carried over from the export file")
            (v, Some(e), Nil)
          catch
            case e: KernelException =>
              (Verdict.Rejected(e.detail), scala.util.Try(recover(env)).toOption, e.trace)
            case e: ExportException =>
              (Verdict.Error(e.getMessage), scala.util.Try(recover(env)).toOption, Nil)
        val nanos = System.nanoTime() - t0
        names.foreach(n => results += DeclResult(n, verdict, nanos, trace))
        nextEnv.foreach(e => env = e)
        observeHeap()
        val rejected = verdict.isInstanceOf[Verdict.Rejected]
        if rejected && rejectedAt < 0 then rejectedAt = results.result().length
        rejected

      // Inductive blocks are contiguous and must be checked as a block.
      val infos = items

      def loop(i: Int): IO[Unit] =
        if i >= infos.length then IO.unit
        else if stopOnFirstRejection && rejectedAt >= 0 then
          // `lean4checker` aborts on the first rejection, so in comparison mode
          // the remaining declarations are not reached rather than accepted.
          IO {
            var k = i
            while k < infos.length do
              infos(k).names.foreach(n =>
                results += DeclResult(n, Verdict.NotChecked("not reached: an earlier declaration was rejected"), 0L)
              )
              k += 1
          }
        else
          val yieldNow = if i % cedeEvery == 0 then IO.cede else IO.unit
          yieldNow *> IO {
            infos(i) match
              case ExportItem.Info(ConstantInfo.InductInfo(first)) =>
                val block = first.all.toSet
                val inds  = List.newBuilder[InductiveVal]
                val ctors = List.newBuilder[ConstructorVal]
                val recs  = List.newBuilder[RecursorVal]
                var j = i
                var scanning = true
                while scanning && j < infos.length do
                  infos(j) match
                    case ExportItem.Info(ConstantInfo.InductInfo(v)) if block.contains(v.toConstantVal.name) =>
                      inds += v; j += 1
                    case ExportItem.Info(ConstantInfo.CtorInfo(v)) if block.contains(v.induct) =>
                      ctors += v; j += 1
                    case ExportItem.Info(ConstantInfo.RecInfo(v)) if v.all.toSet == block =>
                      recs += v; j += 1
                    case _ => scanning = false
                val exportedInds  = inds.result()
                val exportedCtors = ctors.result()
                val exportedRecs  = recs.result()
                val blockNames =
                  exportedInds.map(_.toConstantVal.name) ++
                    exportedCtors.map(_.toConstantVal.name) ++
                    exportedRecs.map(_.toConstantVal.name)
                val blockInfos =
                  exportedInds.map(ConstantInfo.InductInfo(_)) ++
                    exportedCtors.map(ConstantInfo.CtorInfo(_)) ++
                    exportedRecs.map(ConstantInfo.RecInfo(_))
                one(
                  () =>
                    val decl = InductiveChecker.declarationOf(exportedInds, exportedCtors)
                    val r    = AddInductive.add(env, decl, profile)
                    InductiveChecker.validate(
                      exportedInds, exportedCtors, r.inductives, r.constructors, exportedRecs, r.recursors
                    )
                    (r.env, CheckOutcome.Checked),
                  blockNames,
                  e => blockInfos.foldLeft(e)((acc, i) => if acc.contains(i.name) then acc else acc.addCore(i))
                )
                j
              case ExportItem.Info(info) =>
                one(
                  () => dc.addInfo(env, info),
                  List(info.name),
                  e => if e.contains(info.name) then e else e.addCore(info)
                )
                i + 1
              case ExportItem.Decl(d) =>
                one(() => (dc.add(env, d), CheckOutcome.Checked), d.declNames)
                i + 1
              case ExportItem.DefnWithoutHints(n, lp, t, v) =>
                // Text v1 carries no reducibility hint; the kernel supplies one.
                one(
                  () =>
                    (
                      dc.addDefinition(
                        env,
                        DefinitionVal(ConstantVal(n, lp, t), v, ReducibilityHints.Regular(0),
                          DefinitionSafety.Safe, List(n))
                      ),
                      CheckOutcome.Checked
                    ),
                  List(n),
                  e =>
                    if e.contains(n) then e
                    else
                      e.addCore(ConstantInfo.DefnInfo(DefinitionVal(
                        ConstantVal(n, lp, t), v, ReducibilityHints.Regular(0),
                        DefinitionSafety.Safe, List(n)
                      )))
                )
                i + 1
          }.flatMap(next => loop(next))

      loop(0).flatMap { _ =>
        IO.monotonic.map { end =>
          CheckerRun(
            name, toolchain, corpus, platform,
            results.result(), (end - start).toNanos, peak
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
      platform: String = "jvm"
  ): IO[CheckerRun] =
    IO.blocking(Layout.readFile(path)).flatMap { contents =>
      IO(ExportReader.fromString(contents)).attempt.flatMap {
        case Left(e) =>
          IO.pure(
            CheckerRun(name, toolchain, corpus, platform, Vector.empty, 0L, 0L, Some(e.getMessage))
          )
        case Right(env) => check(env.items, profile, toolchain, corpus, platform)
      }
    }
