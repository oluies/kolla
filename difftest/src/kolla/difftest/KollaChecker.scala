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
      stopOnFirstRejection: Boolean = false,
      expectRejection: Boolean = false,
      /** Whether to move the kernel's ambient constants to the front first.
        * Off only to show what the pass is for; a real run leaves it on.
        */
      hoist: Boolean = true
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
        * a cascade of spurious ones. See docs/semantics.md P6.
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
              (Verdict.Rejected(e.reason), scala.util.Try(recover(env)).toOption, e.trace)
            case e: ExportException =>
              (Verdict.Error(e.getMessage), scala.util.Try(recover(env)).toOption, Nil)
        val nanos = System.nanoTime() - t0
        names.foreach(n => results += DeclResult(n, verdict, nanos, trace))
        nextEnv.foreach(e => env = e)
        observeHeap()
        val rejected = verdict.isInstanceOf[Verdict.Rejected]
        if rejected && rejectedAt < 0 then rejectedAt = results.result().length
        rejected

      // Inductive blocks are contiguous and must be checked as a block. The
      // kernel's ambient constants come first, whatever order the file had.
      val infos = if hoist then hoistExtensionConstants(items, profile) else items

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
          IO.pure(
            CheckerRun(name, toolchain, corpus, platform, Vector.empty, 0L, 0L, Some(e.getMessage))
          )
        case Right(env) =>
          check(env.items, profile, toolchain, corpus, platform, stopOnFirstRejection, expectRejection)
      }
    }

  /** The constants the kernel's literal extensions refer to by name.
    *
    * These are not syntactic dependencies of the declarations that need them: a
    * theorem about `"ab" ++ "cd"` never mentions `String.ofList`, the kernel
    * reaches for it when it expands the literal. lean4export orders a file by
    * syntactic dependency, so such a constant can come after its first use.
    */
  def extensionConstants(profile: KernelProfile): Set[Name] =
    Set(
      profile.stringLiteralCtor,
      Names.string, Names.char, Names.charOfNat, Names.listCons, Names.listNil,
      Names.nat, Names.natZero, Names.natSucc
    )

  /** The start index of each group of items that must stay together.
    *
    * An inductive block is a contiguous run: the `InductInfo` of its first type
    * followed by the other types, the constructors and the recursors of the same
    * `all` list. The checker loop depends on that contiguity, so anything that
    * reorders the file has to move a whole block at a time.
    */
  def groupStarts(items: Vector[ExportItem]): Vector[Int] =
    val starts = Vector.newBuilder[Int]
    var i      = 0
    while i < items.length do
      starts += i
      items(i) match
        case ExportItem.Info(ConstantInfo.InductInfo(first)) =>
          val block = first.all.toSet
          var j        = i + 1
          var scanning = true
          while scanning && j < items.length do
            items(j) match
              case ExportItem.Info(ConstantInfo.InductInfo(v)) if block.contains(v.toConstantVal.name) => j += 1
              case ExportItem.Info(ConstantInfo.CtorInfo(v)) if block.contains(v.induct)               => j += 1
              case ExportItem.Info(ConstantInfo.RecInfo(v)) if v.all.toSet == block                    => j += 1
              case _ => scanning = false
          i = j
        case _ => i += 1
    starts.result()

  /** Moves the kernel's ambient constants, and what they depend on, to the front.
    *
    * Without this a declaration can be rejected for a constant the kernel
    * assumes is present: in the v4.25.0 export of `case-strlit`, `appendLit` is
    * item 406 and `String.mk` is item 1822, so the string-literal expansion has
    * nothing to expand to and `"ab" ++ "cd" = "abcd"` fails. Lean never sees
    * this, because its kernel always runs with `Init` imported.
    *
    * Relative order is preserved within the hoisted part and within the rest,
    * so every declaration still comes after its dependencies and each is still
    * checked exactly once. See docs/semantics.md P10.
    */
  def hoistExtensionConstants(items: Vector[ExportItem], profile: KernelProfile): Vector[ExportItem] =
    val wanted  = extensionConstants(profile)
    val starts  = groupStarts(items)
    val ends    = starts.drop(1) :+ items.length
    // The group each item belongs to, so a dependency pulls in its whole block.
    val groupOf = Array.fill(items.length)(0)
    starts.indices.foreach(g => (starts(g) until ends(g)).foreach(i => groupOf(i) = g))
    val byName = items.iterator.zipWithIndex.flatMap((it, i) => it.names.map(_ -> groupOf(i))).toMap
    val needed = scala.collection.mutable.BitSet.empty

    def require(g: Int): Unit =
      if !needed.contains(g) then
        needed += g
        val deps = scala.collection.mutable.LinkedHashSet.empty[Name]
        (starts(g) until ends(g)).foreach(i => exprsOf(items(i)).foreach(collect(_, deps)))
        deps.foreach(n => byName.get(n).filter(_ < g).foreach(require))

    def exprsOf(it: ExportItem): List[Expr] = it match
      case ExportItem.Info(info) =>
        info.tpe :: (info match
          case ConstantInfo.DefnInfo(v)   => List(v.value)
          case ConstantInfo.ThmInfo(v)    => List(v.value)
          case ConstantInfo.OpaqueInfo(v) => List(v.value)
          case ConstantInfo.RecInfo(v)    => v.rules.map(_.rhs)
          case _                          => Nil)
      case ExportItem.Decl(d) =>
        d match
          case Declaration.AxiomDecl(v)  => List(v.toConstantVal.tpe)
          case Declaration.DefnDecl(v)   => List(v.toConstantVal.tpe, v.value)
          case Declaration.ThmDecl(v)    => List(v.toConstantVal.tpe, v.value)
          case Declaration.OpaqueDecl(v) => List(v.toConstantVal.tpe, v.value)
          case Declaration.QuotDecl      => Nil
          case Declaration.MutualDefnDecl(ds) => ds.flatMap(v => List(v.toConstantVal.tpe, v.value))
          case Declaration.InductDecl(_, _, ts, _) =>
            ts.flatMap(t => t.tpe :: t.ctors.map(_.tpe))
      case ExportItem.DefnWithoutHints(_, _, t, v) => List(t, v)

    def collect(e: Expr, into: scala.collection.mutable.LinkedHashSet[Name]): Unit =
      ExprOps.forEach(e) { (x, _) =>
        x match
          case c: Expr.Const => into += c.name
          case p: Expr.Proj  => into += p.typeName
          case _             => ()
        true
      }

    wanted.toVector.flatMap(byName.get).distinct.sorted.foreach(require)
    if needed.isEmpty || needed.size == starts.length then items
    else
      val front = Vector.newBuilder[ExportItem]
      val back  = Vector.newBuilder[ExportItem]
      starts.indices.foreach { g =>
        val into = if needed.contains(g) then front else back
        (starts(g) until ends(g)).foreach(i => into += items(i))
      }
      front.result() ++ back.result()
