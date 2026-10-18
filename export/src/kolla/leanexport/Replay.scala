package kolla.leanexport

import kolla.kernel.*
import scala.collection.mutable

/** What replaying one declaration produced.
  *
  * This is the kernel's answer, not a verdict: a frontend decides what to call
  * it. `CarriedOver` is the `CheckOutcome.TypeOnly` case, where the export file
  * supplies a constant the kernel does not re-derive.
  */
enum ReplayOutcome:
  case Checked
  case CarriedOver(reason: String)
  case Rejected(reason: String, trace: List[String])
  case Failed(reason: String)

  def isRejection: Boolean = this.isInstanceOf[ReplayOutcome.Rejected]

/** One step of a replay: the names it declared and what became of them. */
final case class ReplayStep(names: List[Name], outcome: ReplayOutcome)

/** Replays an export file's declarations into an environment, one step at a
  * time, with no effect type of its own.
  *
  * The driver loops in `cli`, `web` and `difftest` differ only in how they
  * interleave: a fiber yield, an animation frame, a blocking loop. The checking
  * itself is the same and lives here, so the three cannot drift.
  *
  * A step is one declaration, or one whole inductive block: a block has to be
  * added at once, since the kernel derives its constructors and recursors
  * together. Each step gets its own `TypeChecker`, as `environment::add_*`
  * does, which `DeclarationChecker` arranges.
  */
final class Replay(
    source: Vector[ExportItem],
    val profile: KernelProfile,
    /** Whether to move the kernel's ambient constants to the front first. Off
      * only to show what the pass is for; a real run leaves it on.
      */
    hoist: Boolean = true
):

  /** The items in the order they are replayed. */
  val items: Vector[ExportItem] =
    if hoist then Replay.hoistExtensionConstants(source, profile) else source

  private val dc = new DeclarationChecker(profile)

  private var env: Environment = Environment.empty
  private var i: Int           = 0

  def environment: Environment = env
  def position: Int            = i
  def size: Int                = items.length
  def hasNext: Boolean         = i < items.length

  /** The names of every remaining item, consuming them without checking.
    *
    * Used when a frontend abandons the rest of a file, which is how
    * `lean4checker`'s abort-on-first-problem behaviour is matched.
    */
  def skipRest(): Vector[List[Name]] =
    val out = Vector.newBuilder[List[Name]]
    while i < items.length do
      out += items(i).names
      i += 1
    out.result()

  /** Replays one declaration or block and advances past it.
    *
    * A rejected declaration is still carried into the environment, unchecked.
    * Leaving it out would make every later declaration that mentions it fail
    * with an unknown constant, turning one disagreement into a cascade of
    * spurious ones. See docs/semantics.md P6.
    */
  def next(): ReplayStep =
    require(hasNext, "Replay.next() past the end")
    val (names, step, recover) = pending()
    val (outcome, nextEnv) =
      try
        val (e, out) = step()
        val o = out match
          case CheckOutcome.Checked  => ReplayOutcome.Checked
          case CheckOutcome.TypeOnly => ReplayOutcome.CarriedOver("carried over from the export file")
        (o, Some(e))
      catch
        case e: KernelException =>
          (ReplayOutcome.Rejected(e.reason, e.trace), scala.util.Try(recover(env)).toOption)
        case e: ExportException =>
          (ReplayOutcome.Failed(e.getMessage), scala.util.Try(recover(env)).toOption)
    nextEnv.foreach(e => env = e)
    ReplayStep(names, outcome)

  /** The step at the current position, advancing `i` past what it consumes. */
  private def pending(): (List[Name], () => (Environment, CheckOutcome), Environment => Environment) =
    items(i) match
      case ExportItem.Info(ConstantInfo.InductInfo(first)) =>
        val block = first.all.toSet
        val inds  = List.newBuilder[InductiveVal]
        val ctors = List.newBuilder[ConstructorVal]
        val recs  = List.newBuilder[RecursorVal]
        var j        = i
        var scanning = true
        while scanning && j < items.length do
          items(j) match
            case ExportItem.Info(ConstantInfo.InductInfo(v)) if block.contains(v.toConstantVal.name) =>
              inds += v; j += 1
            case ExportItem.Info(ConstantInfo.CtorInfo(v)) if block.contains(v.induct) =>
              ctors += v; j += 1
            case ExportItem.Info(ConstantInfo.RecInfo(v)) if v.all.toSet == block =>
              recs += v; j += 1
            case _ => scanning = false
        i = j
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
        (
          blockNames,
          () =>
            val decl = InductiveChecker.declarationOf(exportedInds, exportedCtors)
            val r    = AddInductive.add(env, decl, profile)
            InductiveChecker.validate(
              exportedInds, exportedCtors, r.inductives, r.constructors, exportedRecs, r.recursors
            )
            (r.env, CheckOutcome.Checked),
          e => blockInfos.foldLeft(e)((acc, x) => if acc.contains(x.name) then acc else acc.addCore(x))
        )
      case ExportItem.Info(info) =>
        i += 1
        (
          List(info.name),
          () => dc.addInfo(env, info),
          e => if e.contains(info.name) then e else e.addCore(info)
        )
      case ExportItem.Decl(d) =>
        i += 1
        (d.declNames, () => (dc.add(env, d), CheckOutcome.Checked), identity)
      case ExportItem.DefnWithoutHints(n, lp, t, v) =>
        i += 1
        // Text v1 carries no reducibility hint; the kernel supplies one.
        val defn = DefinitionVal(ConstantVal(n, lp, t), v, ReducibilityHints.Regular(0), DefinitionSafety.Safe, List(n))
        (
          List(n),
          () => (dc.addDefinition(env, defn), CheckOutcome.Checked),
          e => if e.contains(n) then e else e.addCore(ConstantInfo.DefnInfo(defn))
        )

object Replay:

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
    * It is a stable partition of whole groups, which gives exactly this: no
    * dependency that the file satisfied becomes unsatisfied. Both halves keep
    * their order, so an edge inside one half is untouched; an edge from a
    * hoisted group to a group declared earlier cannot escape, because `require`
    * follows every such dependency and hoists it too; and an edge into a
    * hoisted group can only be satisfied earlier than before. An edge that
    * already pointed forwards in the file stays forwards — the pass does not
    * repair a file that was not topologically ordered to begin with, it only
    * declines to break one that was.
    *
    * Each declaration is still checked exactly once, and none is added
    * unchecked. See docs/semantics.md P10.
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
        // Only a dependency declared *earlier* can be broken by moving `g`
        // forward; one declared later is already forward in the file and the
        // partition leaves it exactly where it was.
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
