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

  /** Accepted by an earlier run, identified by content digest. Not `Checked`:
    * this run did not check it. See docs/semantics.md P15.
    */
  case Cached(digest: String)

  def isRejection: Boolean = this.isInstanceOf[ReplayOutcome.Rejected]

/** Digests a run may skip, and where to record the ones it accepts.
  *
  * The storage is a frontend's business; `Replay` only asks and tells.
  */
trait ReplayCache:
  def contains(d: Digest): Boolean
  def accepted(d: Digest): Unit

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
  *
  * Items are pushed in with `feed` and `finish`, so a driver can supply them
  * from a stream and never hold the whole file. Only the hoisting prefix is
  * retained; see `Replay.hoistExtensionConstants` and docs/semantics.md P13.
  */
final class Replay(
    val profile: KernelProfile,
    /** Whether to move the kernel's ambient constants to the front first. Off
      * only to show what the pass is for; a real run leaves it on.
      */
    hoist: Boolean = true,
    /** How many items the hoisting pass may hold back. The prefix is released
      * at the first group boundary once every ambient constant has been
      * declared or this many items are held, whichever comes first, so a
      * stream never retains more than a window. See docs/semantics.md P13.
      */
    hoistWindow: Int = Replay.defaultHoistWindow,
    /** Which declarations to check. One that answers false is admitted into
      * the environment unchecked, exactly as a rejected one is (P6), and
      * reported as carried over. See docs/semantics.md P14.
      */
    check: Name => Boolean = _ => true,
    /** Accepted digests to trust from an earlier run, and a sink for the ones
      * this run accepts. See docs/semantics.md P15.
      */
    cache: Option[ReplayCache] = None,
    /** The reduction budget per declaration; see docs/semantics.md K21. */
    maxSteps: Long = TypeChecker.defaultMaxSteps,
    /** The environment to replay on top of, for a caller that has already
      * checked a library and is now checking something against it. The names
      * it already holds are the ones `check` is expected to answer false for:
      * a declaration the base has is skipped, not checked twice.
      */
    initial: Environment = Environment.empty
):

  // A digest mixes a dependency's digest, and the base's names have none here
  // (`stepDigest`'s `dep` is this replay's own table). Two different bases
  // would therefore give one candidate the same digest, and a cache entry
  // written under one would be reused under the other. See docs/semantics.md
  // S1 and P15.
  require(
    initial.size == 0 || cache.isEmpty,
    "a seeded replay cannot carry a digest cache"
  )

  /** Feeds a whole file at once, which is what a frontend with the items
    * already in memory wants.
    */
  def this(items: Vector[ExportItem], profile: KernelProfile, hoist: Boolean) =
    // An unbounded window: the items are already in memory, so holding them
    // costs nothing and the order is exactly what the whole-file pass gives.
    this(profile, hoist, Int.MaxValue, _ => true, None, TypeChecker.defaultMaxSteps)
    items.foreach(feed)
    finish()

  def this(items: Vector[ExportItem], profile: KernelProfile) =
    this(items, profile, true)

  private val dc = new DeclarationChecker(profile, maxSteps)

  private var env: Environment = initial

  /** Items whose order is settled and which have not been stepped yet. */
  private val ready = mutable.ArrayDeque.empty[ExportItem]

  /** Items held back while the ambient constants are still being waited for. */
  private val prefix = mutable.ArrayBuffer.empty[ExportItem]

  private var hoisting: Boolean = hoist
  private val awaited           = mutable.Set.from(Replay.extensionConstants(profile))
  private var completedAt: Int  = -1
  private var block: Option[Set[Name]] = None

  private val late                 = mutable.ArrayBuffer.empty[Name]
  private var admitted: Int        = 0
  private var reused: Int          = 0

  /** The digest of every name declared so far, so that a declaration
    * referring to one mixes in what it actually resolved to.
    */
  private val digests = mutable.HashMap.empty[Name, Digest]

  /** The ambient constants, in a fixed order, so the component they contribute
    * does not depend on the order they were declared in.
    */
  private val ambientNames  = Replay.extensionConstants(profile).toVector.sortBy(_.toString)
  private var ambientBase   = Digest.seed
  private var ambientStale  = true
  private var consumed: Int        = 0
  private var fed: Int             = 0
  private var finished: Boolean    = false

  def environment: Environment = env
  def position: Int            = consumed

  /** The number of items fed, once known; `-1` while a stream is still open. */
  def size: Int = if finished then fed else -1

  /** Ambient constants the file declared after the hoisting prefix was cut.
    *
    * Empty for every export whose `Init` comes first, which is every export
    * lean4export produces for a real project. Non-empty means the window was
    * too small to hoist them, so a literal expansion may have had nothing to
    * expand to; a frontend reports it rather than calling the result a
    * disagreement. See docs/semantics.md P13.
    */
  def lateAmbientConstants: List[Name] = late.toList

  /** How many declarations were admitted unchecked because `check` declined
    * them, as opposed to carried over because the format gave only a type.
    */
  def admittedUnchecked: Int = admitted

  /** How many declarations this run skipped on a cache hit. */
  def reusedFromCache: Int = reused

  /** The profile, the cache epoch and the ambient constants, which every
    * declaration's digest is taken against.
    *
    * The ambient constants are in it because the kernel reaches for them when
    * it expands a literal without the declaration naming them (P10), so a
    * digest that left them out could hit after `Nat.succ` changed underneath.
    */
  private def baseDigest(): Digest =
    if ambientStale then
      var a = Digest.mixString(Digest.seed, Digest.epoch)
      // The release rather than the label: `--defeq-cache` changes no verdict,
      // so it must not invalidate digests accepted without it. See P15.
      a = Digest.mixString(a, profile.release)
      ambientNames.foreach { n =>
        digests.get(n) match
          case Some(x) => a = Digest.mixAll(a, 1L, x.hi, x.lo)
          case None    => a = Digest.mix(a, 0L)
      }
      ambientBase = a
      ambientStale = false
    ambientBase

  /** The digest of one step, or `None` if the step is not of a shape the
    * digest covers.
    *
    * Only `Info` items are covered. The two text formats carry `Decl` items
    * instead, and rather than digest a shape that is not exercised, a run over
    * one of those simply never hits the cache.
    */
  private def stepDigest(slice: Vector[ExportItem]): Option[Digest] =
    // Only when a cache is in play. The walk is not free — it visits every
    // expression of the declaration — and a run with no cache has nothing to
    // do with the answer. See docs/semantics.md P16.
    if cache.isEmpty then None
    else
      val infos = slice.collect { case ExportItem.Info(i) => i }
      if infos.length != slice.length then None
      else
        val dep: Name => Option[Digest] = digests.get
        // One memo per step, so subterms shared inside a declaration are
        // digested once.
        val memo = new Digest.Memo
        Some(
          infos.foldLeft(Digest.mix(baseDigest(), slice.length.toLong))((acc, i) =>
            Digest.mixInfo(acc, i, dep, memo)
          )
        )

  def hasNext: Boolean = stepLength().isDefined

  /** The names the next step will declare, without taking it.
    *
    * A driver that only reports a step after it returns can say nothing about
    * a step that never returns, which is how a declaration that does not
    * terminate stays anonymous. See docs/semantics.md K20.
    */
  def peekNames: List[Name] =
    stepLength() match
      case None    => Nil
      case Some(n) => pending(Vector.tabulate(n)(ready(_)))._1

  /** Accepts one more item. */
  def feed(item: ExportItem): Unit =
    require(!finished, "Replay.feed after finish()")
    fed += 1
    if !hoisting then
      // Past the cut the pass can no longer place this first, so record it:
      // a rejection downstream may be P10 rather than a real disagreement.
      item.names.foreach(n => if awaited.remove(n) then late += n)
      ready += item
    else
      val startsGroup = !block.exists(Replay.continuesBlock(item, _))
      if startsGroup && (completedAt >= 0 || prefix.length >= hoistWindow) then
        // Either every ambient constant is in, or the window is full. Either
        // way a group has just closed, so the held prefix can be released.
        flushPrefix()
        item.names.foreach(n => if awaited.remove(n) then late += n)
        ready += item
      else
        if startsGroup then
          block = item match
            case ExportItem.Info(ConstantInfo.InductInfo(first)) => Some(first.all.toSet)
            case _                                               => None
        prefix += item
        item.names.foreach(awaited.remove)
        if awaited.isEmpty && completedAt < 0 then completedAt = prefix.length - 1

  /** Declares that no more items are coming. */
  def finish(): Unit =
    if !finished then
      if hoisting then flushPrefix()
      finished = true

  private def flushPrefix(): Unit =
    val head = prefix.toVector
    ready ++= (if hoist then Replay.hoistExtensionConstants(head, profile) else head)
    prefix.clear()
    hoisting = false

  /** The names of every buffered item, consuming them without checking.
    *
    * Used when a frontend abandons the rest of a file, which is how
    * `lean4checker`'s abort-on-first-problem behaviour is matched. A streaming
    * driver has to account for the items it never fed itself.
    */
  def skipRest(): Vector[List[Name]] =
    if hoisting then flushPrefix()
    val out = Vector.newBuilder[List[Name]]
    while ready.nonEmpty do
      out += ready.removeHead().names
      consumed += 1
    out.result()

  /** How many buffered items the next step consumes, or `None` if that is not
    * yet settled: an inductive block is only known to have ended once the item
    * after it has arrived, or the stream has closed.
    */
  private def stepLength(): Option[Int] =
    if ready.isEmpty then None
    else
      ready.head match
        case ExportItem.Info(ConstantInfo.InductInfo(first)) =>
          val b        = first.all.toSet
          var j        = 0
          var scanning = true
          while scanning && j < ready.length do
            if Replay.continuesBlock(ready(j), b) then j += 1 else scanning = false
          if !scanning || finished then Some(j) else None
        case _ => Some(1)

  /** Replays one declaration or block and advances past it.
    *
    * A rejected declaration is still carried into the environment, unchecked.
    * Leaving it out would make every later declaration that mentions it fail
    * with an unknown constant, turning one disagreement into a cascade of
    * spurious ones. See docs/semantics.md P6.
    */
  def next(): ReplayStep =
    val n = stepLength()
    require(n.isDefined, "Replay.next() without a complete step")
    val slice = Vector.tabulate(n.get)(ready(_))
    var k     = 0
    while k < n.get do { ready.removeHead(); k += 1 }
    consumed += n.get
    val (names, step, recover) = pending(slice)
    val dg = stepDigest(slice)
    dg.foreach { d =>
      names.foreach(n => digests.update(n, d))
      if names.exists(ambientNames.contains) then ambientStale = true
    }
    if dg.exists(d => cache.exists(_.contains(d))) then
      // Accepted by an earlier run against the same dependencies, profile and
      // epoch. Admitted the way an unchecked declaration is, and reported as
      // its own outcome so it is never mistaken for this run's work.
      reused += names.length
      scala.util.Try(recover(env)).toOption.foreach(e => env = e)
      ReplayStep(names, ReplayOutcome.Cached(dg.get.hex))
    else if !names.exists(check) then
      // Not selected: admit it unchecked so that what depends on it still
      // resolves, and say so. Never `Checked`, so it cannot be read as
      // agreement. See docs/semantics.md P14.
      admitted += names.length
      scala.util.Try(recover(env)).toOption.foreach(e => env = e)
      ReplayStep(names, ReplayOutcome.CarriedOver("admitted unchecked: not selected"))
    else
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
      if outcome == ReplayOutcome.Checked then
        dg.foreach(d => cache.foreach(_.accepted(d)))
      ReplayStep(names, outcome)

  /** The step the slice amounts to: one declaration, or one inductive block. */
  private def pending(slice: Vector[ExportItem]): (List[Name], () => (Environment, CheckOutcome), Environment => Environment) =
    slice.head match
      case ExportItem.Info(ConstantInfo.InductInfo(_)) =>
        val inds  = List.newBuilder[InductiveVal]
        val ctors = List.newBuilder[ConstructorVal]
        val recs  = List.newBuilder[RecursorVal]
        slice.foreach {
          case ExportItem.Info(ConstantInfo.InductInfo(v)) => inds += v
          case ExportItem.Info(ConstantInfo.CtorInfo(v))   => ctors += v
          case ExportItem.Info(ConstantInfo.RecInfo(v))    => recs += v
          case _                                           => ()
        }
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
            val r    = AddInductive.add(env, decl, profile, maxSteps)
            InductiveChecker.validate(
              exportedInds, exportedCtors, r.inductives, r.constructors, exportedRecs, r.recursors
            )
            (r.env, CheckOutcome.Checked),
          e => blockInfos.foldLeft(e)((acc, x) => if acc.contains(x.name) then acc else acc.addCore(x))
        )
      case ExportItem.Info(info) =>
        (
          List(info.name),
          () => dc.addInfo(env, info),
          e => Replay.admitInfo(e, info)
        )
      case ExportItem.Decl(d) =>
        (d.declNames, () => (dc.add(env, d), CheckOutcome.Checked), e => Replay.admit(e, d, profile))
      case ExportItem.DefnWithoutHints(n, lp, t, v) =>
        // Text v1 carries no reducibility hint; the kernel supplies one.
        val defn = DefinitionVal(ConstantVal(n, lp, t), v, ReducibilityHints.Regular(0), DefinitionSafety.Safe, List(n))
        (
          List(n),
          () => (dc.addDefinition(env, defn), CheckOutcome.Checked),
          e => if e.contains(n) then e else e.addCore(ConstantInfo.DefnInfo(defn))
        )

object Replay:

  /** How many items a streaming hoist holds back by default.
    *
    * The pass only has to span the distance between an ambient constant's
    * first use and its declaration. lean4export orders by syntactic
    * dependency, and the widest case measured is the v4.25.0 `case-strlit`
    * export, where `appendLit` is item 406 and `String.mk` item 1822. A window
    * of this size covers that by three orders of magnitude while bounding what
    * a stream retains.
    */
  val defaultHoistWindow: Int = 1 << 16

  /** Adds an exported constant to the environment without checking it.
    *
    * `addCore` is right for everything but the quotient package. That is a
    * kernel extension rather than four ordinary constants: `quotReduceRec` is
    * gated on `Environment.quotInitialized`, and only `Quot.add` sets it.
    * Adding the exported `QuotInfo` with `addCore` therefore puts `Quot`,
    * `Quot.mk`, `Quot.lift` and `Quot.ind` in scope with quotient reduction
    * switched off, and anything whose type needs a quotient to compute is then
    * rejected. See docs/semantics.md P21.
    */
  def admitInfo(env: Environment, info: ConstantInfo): Environment = info match
    case ConstantInfo.QuotInfo(_) =>
      // `Quot.add` can refuse: `checkEqType` rejects a missing or misshapen
      // `Eq`, and `checkName` rejects a name already taken. A `recover` runs
      // inside `Try(...).toOption`, so letting that escape would put none of
      // the four constants in scope and turn one disagreement into a cascade
      // of unknown-constant failures — which is what P6 exists to prevent, and
      // what the negative corpus produces by retyping `Eq`. So fall back to
      // the constant on its own, which is all that could be said before.
      if env.quotInitialized then env
      else
        scala.util.Try(Quot.add(env)).getOrElse {
          if env.contains(info.name) then env else env.addCore(info)
        }
    case _ =>
      if env.contains(info.name) then env else env.addCore(info)

  /** Adds a text-format declaration to the environment without checking it.
    *
    * The `Info` items an NDJSON or text v2 export carries are added with
    * `addCore`, so a declaration that was rejected (P6) or not selected (P14)
    * still resolves for everything after it. A `Decl` item had `identity`
    * here, which added nothing: on a text v1 export, where inductives arrive
    * as `Declaration.InductDecl` and the quotient package as `QuotDecl`,
    * neither case put anything in the environment and every later reference to
    * a type became an unknown constant.
    *
    * An inductive block cannot be admitted by writing down its constructors,
    * because its recursors are derived rather than exported; `AddInductive.add`
    * derives them. That makes admitting an inductive almost as much work as
    * checking one, which is the price of the text formats carrying blocks
    * rather than infos. A throw is tolerated: the callers wrap this in `Try`,
    * and the alternative to an incomplete environment is no environment.
    * See docs/semantics.md P18.
    */
  def admit(env: Environment, d: Declaration, profile: KernelProfile): Environment =
    def put(e: Environment, info: ConstantInfo): Environment =
      if e.contains(info.name) then e else e.addCore(info)
    d match
      case Declaration.AxiomDecl(v)  => put(env, ConstantInfo.AxiomInfo(v))
      case Declaration.DefnDecl(v)   => put(env, ConstantInfo.DefnInfo(v))
      case Declaration.ThmDecl(v)    => put(env, ConstantInfo.ThmInfo(v))
      case Declaration.OpaqueDecl(v) => put(env, ConstantInfo.OpaqueInfo(v))
      case Declaration.MutualDefnDecl(ds) =>
        ds.foldLeft(env)((acc, v) => put(acc, ConstantInfo.DefnInfo(v)))
      case Declaration.QuotDecl =>
        if env.quotInitialized then env else Quot.add(env)
      case i: Declaration.InductDecl =>
        AddInductive.add(env, i, profile).env

  /** Whether `item` belongs to the inductive block whose `all` list is `block`.
    *
    * The same predicate decides where a group ends in `groupStarts` and where
    * the next step ends in `Replay.stepLength`, so the two cannot disagree.
    */
  def continuesBlock(item: ExportItem, block: Set[Name]): Boolean = item match
    case ExportItem.Info(ConstantInfo.InductInfo(v)) => block.contains(v.toConstantVal.name)
    case ExportItem.Info(ConstantInfo.CtorInfo(v))   => block.contains(v.induct)
    case ExportItem.Info(ConstantInfo.RecInfo(v))    => v.all.toSet == block
    case _                                           => false

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
          val block    = first.all.toSet
          var j        = i + 1
          var scanning = true
          while scanning && j < items.length do
            if continuesBlock(items(j), block) then j += 1 else scanning = false
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
