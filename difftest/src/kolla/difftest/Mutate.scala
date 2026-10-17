package kolla.difftest

import kolla.kernel.*
import kolla.leanexport.*
import scala.collection.mutable

/** The kinds of corruption the negative corpus applies. */
enum MutationKind:
  case SwapConstructorIndices
  case ChangeUniverseLevel
  case AlterRecursorRuleRhs
  case RemoveLetValue
  case ChangeDefinitionalHeight
  case RetypeAxiom

  def slug: String = this match
    case SwapConstructorIndices   => "swap-ctor-indices"
    case ChangeUniverseLevel      => "change-universe-level"
    case AlterRecursorRuleRhs     => "alter-recursor-rhs"
    case RemoveLetValue           => "remove-let-value"
    case ChangeDefinitionalHeight => "change-definitional-height"
    case RetypeAxiom              => "retype-axiom"

/** One mutation: what was changed and where. */
final case class Mutation(
    kind: MutationKind,
    seed: Long,
    target: Name,
    description: String,
    items: Vector[ExportItem]
):
  def id: String = s"${kind.slug}-$seed"

/** Deterministic mutations of an export.
  *
  * A mutation is a function of `(kind, seed, base)` alone, so the same seed
  * reproduces the same corruption. `ChangeDefinitionalHeight` is expected *not*
  * to change any verdict, since a reducibility hint only steers which side
  * `is_def_eq` unfolds first; it is included to check that kolla does not reject
  * something on the strength of a hint.
  */
object Mutate:

  val all: List[MutationKind] = MutationKind.values.toList

  /** A small deterministic generator, so a seed means the same thing on every
    * platform regardless of the JDK's `Random`.
    */
  private final class Rng(seed: Long):
    private var s = if seed == 0 then 0x9E3779B97F4A7C15L else seed
    def next(): Long =
      s ^= s << 13; s ^= s >>> 7; s ^= s << 17; s
    def nonNegative(bound: Int): Int =
      if bound <= 0 then 0 else ((next() >>> 1) % bound).toInt
    def pick[A](xs: IndexedSeq[A]): Option[A] =
      if xs.isEmpty then None else Some(xs(nonNegative(xs.length)))

  def apply(kind: MutationKind, seed: Long, base: Vector[ExportItem]): Option[Mutation] =
    val rng = new Rng(seed * 31 + kind.ordinal)
    kind match
      case MutationKind.SwapConstructorIndices   => swapCtorIndices(rng, seed, base)
      case MutationKind.ChangeUniverseLevel      => changeUniverseLevel(rng, seed, base)
      case MutationKind.AlterRecursorRuleRhs     => alterRecursorRhs(rng, seed, base)
      case MutationKind.RemoveLetValue           => removeLetValue(rng, seed, base)
      case MutationKind.ChangeDefinitionalHeight => changeHeight(rng, seed, base)
      case MutationKind.RetypeAxiom              => retypeAxiom(rng, seed, base)

  /** Every mutation of every kind that applies to `base`, for one seed. */
  def generate(seed: Long, base: Vector[ExportItem]): List[Mutation] =
    all.flatMap(k => apply(k, seed, base))

  private def indicesOf(base: Vector[ExportItem])(
      pf: PartialFunction[ExportItem, Boolean]
  ): IndexedSeq[Int] =
    base.indices.filter(i => pf.isDefinedAt(base(i)) && pf(base(i)))

  private def swapCtorIndices(rng: Rng, seed: Long, base: Vector[ExportItem]): Option[Mutation] =
    // Pick an inductive whose constructors can be renumbered.
    val groups = base.indices
      .collect { case i if base(i).isInstanceOf[ExportItem.Info] => i }
      .flatMap { i =>
        base(i) match
          case ExportItem.Info(ConstantInfo.CtorInfo(v)) => Some((i, v))
          case _                                        => None
      }
      .groupBy(_._2.induct)
      .filter(_._2.length >= 2)
      .toIndexedSeq
      .sortBy(_._1.toString)
    rng.pick(groups).map { (induct, ctors) =>
      val a = ctors(0)
      val b = ctors(1)
      val swapped = base.updated(
        a._1, ExportItem.Info(ConstantInfo.CtorInfo(a._2.copy(cidx = b._2.cidx)))
      ).updated(
        b._1, ExportItem.Info(ConstantInfo.CtorInfo(b._2.copy(cidx = a._2.cidx)))
      )
      Mutation(
        MutationKind.SwapConstructorIndices, seed, induct,
        s"swapped cidx of ${a._2.toConstantVal.name} and ${b._2.toConstantVal.name}",
        swapped
      )
    }

  private def changeUniverseLevel(rng: Rng, seed: Long, base: Vector[ExportItem]): Option[Mutation] =
    val cands = indicesOf(base) {
      case ExportItem.Info(i) => i.tpe.isInstanceOf[Expr.Sort]
    }
    rng.pick(cands).map { i =>
      val info = base(i).asInstanceOf[ExportItem.Info].info
      val s    = info.tpe.asInstanceOf[Expr.Sort]
      val bumped = Expr.Sort(Level.Succ(s.level))
      Mutation(
        MutationKind.ChangeUniverseLevel, seed, info.name,
        s"raised the sort of ${info.name} from ${s.level} to ${Level.Succ(s.level)}",
        base.updated(i, ExportItem.Info(retype(info, bumped)))
      )
    }

  private def alterRecursorRhs(rng: Rng, seed: Long, base: Vector[ExportItem]): Option[Mutation] =
    val cands = indicesOf(base) {
      case ExportItem.Info(ConstantInfo.RecInfo(v)) => v.rules.nonEmpty
    }
    rng.pick(cands).map { i =>
      val rv   = base(i).asInstanceOf[ExportItem.Info].info.asInstanceOf[ConstantInfo.RecInfo].value
      val k    = rng.nonNegative(rv.rules.length)
      val rule = rv.rules(k)
      // Replace the right-hand side with a different, well-formed term.
      val broken = rule.copy(rhs = Expr.natLit(0))
      val rules  = rv.rules.updated(k, broken)
      Mutation(
        MutationKind.AlterRecursorRuleRhs, seed, rv.toConstantVal.name,
        s"replaced the rule for ${rule.ctor} with a nat literal",
        base.updated(i, ExportItem.Info(ConstantInfo.RecInfo(rv.copy(rules = rules))))
      )
    }

  private def removeLetValue(rng: Rng, seed: Long, base: Vector[ExportItem]): Option[Mutation] =
    // Replace a `let` value with a literal of a different type, keeping the
    // declared type, so the let's own `is_def_eq` check must fail.
    val cands = indicesOf(base) {
      case ExportItem.Info(i) => i.value().exists(containsLet)
    }
    rng.pick(cands).map { i =>
      val info = base(i).asInstanceOf[ExportItem.Info].info
      val v    = info.value().get
      Mutation(
        MutationKind.RemoveLetValue, seed, info.name,
        s"replaced a let value in ${info.name}",
        base.updated(i, ExportItem.Info(revalue(info, breakFirstLet(v))))
      )
    }

  private def changeHeight(rng: Rng, seed: Long, base: Vector[ExportItem]): Option[Mutation] =
    val cands = indicesOf(base) {
      case ExportItem.Info(ConstantInfo.DefnInfo(v)) => v.hints.isRegular
    }
    rng.pick(cands).map { i =>
      val dv = base(i).asInstanceOf[ExportItem.Info].info.asInstanceOf[ConstantInfo.DefnInfo].value
      val h  = dv.hints.regularHeight
      Mutation(
        MutationKind.ChangeDefinitionalHeight, seed, dv.toConstantVal.name,
        s"changed the definitional height of ${dv.toConstantVal.name} from $h to ${h + 97}",
        base.updated(
          i,
          ExportItem.Info(ConstantInfo.DefnInfo(dv.copy(hints = ReducibilityHints.Regular(h + 97))))
        )
      )
    }

  private def retypeAxiom(rng: Rng, seed: Long, base: Vector[ExportItem]): Option[Mutation] =
    val cands = indicesOf(base) { case ExportItem.Info(ConstantInfo.AxiomInfo(_)) => true }
    rng.pick(cands).map { i =>
      val av = base(i).asInstanceOf[ExportItem.Info].info.asInstanceOf[ConstantInfo.AxiomInfo].value
      // A nat literal is not a type, so the axiom's type is no longer a sort.
      Mutation(
        MutationKind.RetypeAxiom, seed, av.toConstantVal.name,
        s"retyped the axiom ${av.toConstantVal.name} to a nat literal",
        base.updated(
          i,
          ExportItem.Info(ConstantInfo.AxiomInfo(
            av.copy(toConstantVal = av.toConstantVal.copy(tpe = Expr.natLit(1)))
          ))
        )
      )
    }

  private def containsLet(e: Expr): Boolean =
    var found = false
    ExprOps.forEach(e) { (m, _) =>
      if found then false
      else if m.isInstanceOf[Expr.LetE] then { found = true; false }
      else true
    }
    found

  /** Replaces the first `let`'s value with a nat literal. */
  private def breakFirstLet(e: Expr): Expr =
    var done = false
    ExprOps.replace(e) { (m, _) =>
      m match
        case l: Expr.LetE if !done =>
          done = true
          Some(Expr.LetE(l.declName, l.tpe, Expr.natLit(0), l.body, l.nondep))
        case _ => None
    }

  private def retype(info: ConstantInfo, tpe: Expr): ConstantInfo = info match
    case ConstantInfo.AxiomInfo(v)  => ConstantInfo.AxiomInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))
    case ConstantInfo.DefnInfo(v)   => ConstantInfo.DefnInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))
    case ConstantInfo.ThmInfo(v)    => ConstantInfo.ThmInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))
    case ConstantInfo.OpaqueInfo(v) => ConstantInfo.OpaqueInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))
    case ConstantInfo.QuotInfo(v)   => ConstantInfo.QuotInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))
    case ConstantInfo.InductInfo(v) => ConstantInfo.InductInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))
    case ConstantInfo.CtorInfo(v)   => ConstantInfo.CtorInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))
    case ConstantInfo.RecInfo(v)    => ConstantInfo.RecInfo(v.copy(toConstantVal = v.toConstantVal.copy(tpe = tpe)))

  private def revalue(info: ConstantInfo, value: Expr): ConstantInfo = info match
    case ConstantInfo.DefnInfo(v)   => ConstantInfo.DefnInfo(v.copy(value = value))
    case ConstantInfo.ThmInfo(v)    => ConstantInfo.ThmInfo(v.copy(value = value))
    case ConstantInfo.OpaqueInfo(v) => ConstantInfo.OpaqueInfo(v.copy(value = value))
    case other                      => other

  /** A unified diff of the mutated export against the base, so a case can be
    * replayed without storing the whole file.
    */
  def diff(base: Vector[ExportItem], mutated: Vector[ExportItem], format: ExportFormat): String =
    val a = ExportWriter.toLines(ExportEnv(format, None, base), format)
    val b = ExportWriter.toLines(ExportEnv(format, None, mutated), format)
    Diff.unified(a, b)
