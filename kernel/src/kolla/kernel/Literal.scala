package kolla.kernel

enum Literal:
  case NatVal(value: BigInt)
  case StrVal(value: String)

object Literal:
  /** `Lean.Literal.lt`: natural number values precede string values. */
  def lt(a: Literal, b: Literal): Boolean = (a, b) match
    case (NatVal(_), StrVal(_)) => true
    case (NatVal(x), NatVal(y)) => x < y
    case (StrVal(x), StrVal(y)) => x < y
    case _                      => false

  private[kernel] def hashOf(l: Literal): Long = l match
    case NatVal(v) => Name.mix(3L, if v.isValidLong then v.toLong else scala.util.hashing.MurmurHash3.bytesHash(v.toByteArray).toLong)
    case StrVal(v) => Name.mix(5L, scala.util.hashing.MurmurHash3.stringHash(v).toLong & 0xffffffffL)

  given Ordering[Literal] = Ordering.fromLessThan(lt)
