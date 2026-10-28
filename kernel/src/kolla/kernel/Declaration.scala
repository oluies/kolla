package kolla.kernel

final case class ConstantVal(name: Name, levelParams: List[Name], tpe: Expr)

enum ReducibilityHints:
  case Opaque
  case Abbrev
  case Regular(height: Int)

  def isRegular: Boolean = this.isInstanceOf[ReducibilityHints.Regular]
  def isAbbrev: Boolean  = this == ReducibilityHints.Abbrev

  def regularHeight: Int = this match
    case ReducibilityHints.Regular(h) => h
    case _                            => 0

object ReducibilityHints:
  /** `lean::compare(reducibility_hints, reducibility_hints)`:
    * `< 0` unfold the first, `0` unfold both, `> 0` unfold the second.
    */
  def compare(h1: ReducibilityHints, h2: ReducibilityHints): Int = (h1, h2) match
    case (Regular(a), Regular(b)) => if a == b then 0 else if a > b then -1 else 1
    case (Opaque, Opaque)         => 0
    case (Abbrev, Abbrev)         => 0
    case (Opaque, _)              => 1
    case (_, Opaque)              => -1
    case (Abbrev, _)              => -1
    case (_, Abbrev)              => 1
    case _                        => 0

enum DefinitionSafety:
  case Unsafe, Safe, Partial

enum QuotKind:
  case Type, Ctor, Lift, Ind

final case class RecursorRule(ctor: Name, nfields: Int, rhs: Expr)

final case class AxiomVal(toConstantVal: ConstantVal, isUnsafe: Boolean)

final case class DefinitionVal(
    toConstantVal: ConstantVal,
    value: Expr,
    hints: ReducibilityHints,
    safety: DefinitionSafety,
    all: List[Name]
):
  def isUnsafe: Boolean = safety == DefinitionSafety.Unsafe

final case class TheoremVal(toConstantVal: ConstantVal, value: Expr, all: List[Name])

final case class OpaqueVal(toConstantVal: ConstantVal, value: Expr, isUnsafe: Boolean, all: List[Name])

final case class QuotVal(toConstantVal: ConstantVal, kind: QuotKind)

final case class InductiveVal(
    toConstantVal: ConstantVal,
    numParams: Int,
    numIndices: Int,
    all: List[Name],
    ctors: List[Name],
    numNested: Int,
    isRec: Boolean,
    isUnsafe: Boolean,
    isReflexive: Boolean
):
  def numCtors: Int = ctors.length

final case class ConstructorVal(
    toConstantVal: ConstantVal,
    induct: Name,
    cidx: Int,
    numParams: Int,
    numFields: Int,
    isUnsafe: Boolean
)

final case class RecursorVal(
    toConstantVal: ConstantVal,
    all: List[Name],
    numParams: Int,
    numIndices: Int,
    numMotives: Int,
    numMinors: Int,
    rules: List[RecursorRule],
    k: Boolean,
    isUnsafe: Boolean
):
  def majorIdx: Int = numParams + numMotives + numMinors + numIndices

  /** `recursor_val::get_major_induct`: the inductive the major premise belongs
    * to, read off this recursor's own type.
    *
    * Not `all.head`. The recursors a nested inductive generates for its nested
    * occurrences share the block's `all`, so `SnapshotTree.rec_3` has
    * `all = [SnapshotTree]` while its major premise is a
    * `SnapshotTask SnapshotTree`. Asking about `SnapshotTree` there is asking
    * about the wrong type, and the answer decides whether iota gets to
    * eta-expand a structure major into a constructor application
    * (`to_cnstr_when_structure`). See docs/semantics.md K17.
    *
    * `declaration.cpp` walks `majorIdx` binders, takes the domain and returns
    * its head constant; this does the same, falling back to `all.head` on a
    * type that is not the Pi telescope a recursor must have.
    */
  def majorInduct: Name =
    var t = toConstantVal.tpe
    var i = 0
    while i < majorIdx do
      t match
        case f: Expr.ForallE => t = f.body; i += 1
        case _               => i = majorIdx
    t match
      case f: Expr.ForallE => Expr.constName(Expr.getAppFn(f.binderType)).getOrElse(all.head)
      case _               => all.head

final case class Constructor(name: Name, tpe: Expr)

final case class InductiveType(name: Name, tpe: Expr, ctors: List[Constructor])

enum ConstantInfo:
  case AxiomInfo(value: AxiomVal)
  case DefnInfo(value: DefinitionVal)
  case ThmInfo(value: TheoremVal)
  case OpaqueInfo(value: OpaqueVal)
  case QuotInfo(value: QuotVal)
  case InductInfo(value: InductiveVal)
  case CtorInfo(value: ConstructorVal)
  case RecInfo(value: RecursorVal)

  def toConstantVal: ConstantVal = this match
    case AxiomInfo(v)  => v.toConstantVal
    case DefnInfo(v)   => v.toConstantVal
    case ThmInfo(v)    => v.toConstantVal
    case OpaqueInfo(v) => v.toConstantVal
    case QuotInfo(v)   => v.toConstantVal
    case InductInfo(v) => v.toConstantVal
    case CtorInfo(v)   => v.toConstantVal
    case RecInfo(v)    => v.toConstantVal

  def name: Name                = toConstantVal.name
  def levelParams: List[Name]   = toConstantVal.levelParams
  def numLevelParams: Int       = levelParams.length
  def tpe: Expr                 = toConstantVal.tpe

  def isDefinition: Boolean  = this.isInstanceOf[ConstantInfo.DefnInfo]
  def isAxiom: Boolean       = this.isInstanceOf[ConstantInfo.AxiomInfo]
  def isTheorem: Boolean     = this.isInstanceOf[ConstantInfo.ThmInfo]
  def isOpaque: Boolean      = this.isInstanceOf[ConstantInfo.OpaqueInfo]
  def isQuot: Boolean        = this.isInstanceOf[ConstantInfo.QuotInfo]
  def isInductive: Boolean   = this.isInstanceOf[ConstantInfo.InductInfo]
  def isConstructor: Boolean = this.isInstanceOf[ConstantInfo.CtorInfo]
  def isRecursor: Boolean    = this.isInstanceOf[ConstantInfo.RecInfo]

  def isUnsafe: Boolean = this match
    case AxiomInfo(v)  => v.isUnsafe
    case DefnInfo(v)   => v.isUnsafe
    case ThmInfo(_)    => false
    case OpaqueInfo(v) => v.isUnsafe
    case QuotInfo(_)   => false
    case InductInfo(v) => v.isUnsafe
    case CtorInfo(v)   => v.isUnsafe
    case RecInfo(v)    => v.isUnsafe

  def hasValue(allowOpaque: Boolean = false): Boolean = this match
    case _: ThmInfo | _: DefnInfo => true
    case _: OpaqueInfo            => allowOpaque
    case _                        => false

  def value(allowOpaque: Boolean = false): Option[Expr] = this match
    case ThmInfo(v)                   => Some(v.value)
    case DefnInfo(v)                  => Some(v.value)
    case OpaqueInfo(v) if allowOpaque => Some(v.value)
    case _                            => None

  def hints: ReducibilityHints = this match
    case DefnInfo(v) => v.hints
    case _           => ReducibilityHints.Opaque

enum Declaration:
  case AxiomDecl(value: AxiomVal)
  case DefnDecl(value: DefinitionVal)
  case ThmDecl(value: TheoremVal)
  case OpaqueDecl(value: OpaqueVal)
  case QuotDecl
  case MutualDefnDecl(defns: List[DefinitionVal])
  case InductDecl(levelParams: List[Name], numParams: Int, types: List[InductiveType], isUnsafe: Boolean)

  def anyUnsafe: Boolean = this match
    case AxiomDecl(v)            => v.isUnsafe
    case DefnDecl(v)             => v.isUnsafe
    case ThmDecl(_)              => false
    case OpaqueDecl(v)           => v.isUnsafe
    case QuotDecl                => false
    case MutualDefnDecl(ds)      => ds.exists(_.isUnsafe)
    case InductDecl(_, _, _, u)  => u

  /** Only definitions are unfolded during reduction. */
  def hasValue: Boolean = this.isInstanceOf[Declaration.DefnDecl]

  def declNames: List[Name] = this match
    case AxiomDecl(v)            => List(v.toConstantVal.name)
    case DefnDecl(v)             => List(v.toConstantVal.name)
    case ThmDecl(v)              => List(v.toConstantVal.name)
    case OpaqueDecl(v)           => List(v.toConstantVal.name)
    // The four constants `add_quot` installs. Empty would mean no selector can
    // reach the declaration: `Replay` asks whether any of a step's names is
    // selected, and none of an empty list is, so a text-format `#QUOT` was
    // never checked and its failure to install was swallowed with it.
    case QuotDecl                => Quot.declarations.map(_.toConstantVal.name)
    case MutualDefnDecl(ds)      => ds.map(_.toConstantVal.name)
    case InductDecl(_, _, ts, _) => ts.flatMap(t => t.name :: t.ctors.map(_.name))
