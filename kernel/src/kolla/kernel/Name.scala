package kolla.kernel

import scala.annotation.tailrec
import scala.util.hashing.MurmurHash3

sealed abstract class Name:
  val hash: Long

  final override def hashCode: Int = (hash ^ (hash >>> 32)).toInt

  final override def equals(that: Any): Boolean = that match
    case n: Name => Name.structEq(this, n)
    case _       => false

  final override def toString: String = Name.render(this)

  final def isAnonymous: Boolean = this.asInstanceOf[AnyRef] eq Name.Anonymous

  final def prefix: Name = this match
    case s: Name.Str => s.pre
    case n: Name.Num => n.pre
    case _           => Name.Anonymous

  final def isAtomic: Boolean = prefix.isAnonymous

  final def str(s: String): Name = Name.Str(this, s)
  final def num(i: BigInt): Name = Name.Num(this, i)
  final def num(i: Int): Name = Name.Num(this, BigInt(i))

  final def append(other: Name): Name = Name.append(this, other)

  final def components: List[Name] =
    @tailrec def go(n: Name, acc: List[Name]): List[Name] = n match
      case s: Name.Str => go(s.pre, Name.Str(Name.Anonymous, s.value) :: acc)
      case m: Name.Num => go(m.pre, Name.Num(Name.Anonymous, m.value) :: acc)
      case _           => acc
    go(this, Nil)

  final def length: Int =
    @tailrec def go(n: Name, acc: Int): Int =
      if n.isAnonymous then acc else go(n.prefix, acc + 1)
    go(this, 0)

object Name:

  object Anonymous extends Name:
    val hash: Long = 1723L

  final case class Str(pre: Name, value: String) extends Name:
    val hash: Long = Name.mix(pre.hash, Name.hashString(value))

  final case class Num(pre: Name, value: BigInt) extends Name:
    val hash: Long = Name.mix(pre.hash, Name.hashNat(value))

  val anonymous: Name = Anonymous

  def mkSimple(s: String): Name = Str(Anonymous, s)

  /** Splits on `.`; no escape handling. */
  def parse(s: String): Name =
    if s.isEmpty then Anonymous
    else s.split('.').foldLeft(anonymous)((n, c) => n.str(c))

  def apply(components: String*): Name =
    components.foldLeft(anonymous)((n, c) => n.str(c))

  private[kernel] def mix(h: Long, k0: Long): Long =
    val m = 0xc6a4a7935bd1e995L
    var k = k0 * m
    k ^= k >>> 47
    k ^= m
    var r = h ^ k
    r * m

  private def hashString(s: String): Long =
    MurmurHash3.stringHash(s).toLong & 0xffffffffL

  private def hashNat(i: BigInt): Long =
    if i.isValidLong then i.toLong else MurmurHash3.bytesHash(i.toByteArray).toLong & 0xffffffffL

  @tailrec
  private[kernel] def structEq(a: Name, b: Name): Boolean =
    if a.asInstanceOf[AnyRef] eq b.asInstanceOf[AnyRef] then true
    else if a.hash != b.hash then false
    else
      (a, b) match
        case (x: Str, y: Str) => x.value == y.value && structEq(x.pre, y.pre)
        case (x: Num, y: Num) => x.value == y.value && structEq(x.pre, y.pre)
        case _                => false

  /** `Name.hasMacroScopes`: a hygienic name ends in `._hyg.<scopes>`. */
  @tailrec
  def hasMacroScopes(n: Name): Boolean = n match
    case s: Str => s.value == "_hyg"
    case m: Num => hasMacroScopes(m.pre)
    case _      => false

  /** `Name.eraseMacroScopes`: the unhygienic base, that is the prefix of the
    * rightmost `_@` component.
    */
  def eraseMacroScopes(n: Name): Name =
    if !hasMacroScopes(n) then n
    else
      @tailrec def go(cur: Name): Name = cur match
        case s: Str => if s.value == "_@" then s.pre else go(s.pre)
        case m: Num => go(m.pre)
        case _      => Name.anonymous
      go(n)

  /** `Name.modifyBase`: applies `f` to the unhygienic base and puts the macro
    * scopes back, so a suffix lands on the readable part of the name rather than
    * after `._hyg.<scopes>`.
    */
  def modifyBase(n: Name, f: Name => Name): Name =
    if !hasMacroScopes(n) then f(n)
    else
      val cs = n.components
      // The tail starts at the rightmost `_@` component.
      var split = -1
      cs.zipWithIndex.foreach { (c, i) =>
        c match
          case s: Str if s.value == "_@" => split = i
          case _                         => ()
      }
      if split < 0 then f(n)
      else
        val base = cs.take(split).foldLeft(Name.anonymous)(appendComponent)
        cs.drop(split).foldLeft(f(base))(appendComponent)

  private def appendComponent(acc: Name, c: Name): Name = c match
    case s: Str => acc.str(s.value)
    case m: Num => acc.num(m.value)
    case _      => acc

  /** `Name.appendAfter`: extends the last string component of the unhygienic
    * base, or adds one.
    */
  def appendAfter(n: Name, suffix: String): Name =
    modifyBase(
      n,
      {
        case s: Str => s.pre.str(s.value + suffix)
        case other  => other.str(suffix)
      }
    )

  /** `Name.appendIndexAfter`, which separates the index with `_`. */
  def appendIndexAfter(n: Name, i: Int): Name = appendAfter(n, s"_$i")

  /** `lean::name::replace_prefix`. */
  def replacePrefix(n: Name, pre: Name, newPre: Name): Name =
    if n == pre then newPre
    else
      n match
        case s: Str => replacePrefix(s.pre, pre, newPre).str(s.value)
        case m: Num => replacePrefix(m.pre, pre, newPre).num(m.value)
        case _      => n

  def append(a: Name, b: Name): Name =
    b.components.foldLeft(a) { (acc, c) =>
      c match
        case s: Str => acc.str(s.value)
        case m: Num => acc.num(m.value)
        case _      => acc
    }

  /** Total order matching `lean::name::cmp_core`: component-wise from the outermost
    * prefix, numerals before strings, shorter names first.
    */
  def compare(a: Name, b: Name): Int =
    @tailrec def go(as: List[Name], bs: List[Name]): Int = (as, bs) match
      case (Nil, Nil)       => 0
      case (Nil, _)         => -1
      case (_, Nil)         => 1
      case (x :: xt, y :: yt) =>
        val c = compareComponent(x, y)
        if c != 0 then c else go(xt, yt)
    go(a.components, b.components)

  private def compareComponent(x: Name, y: Name): Int = (x, y) match
    case (_: Num, _: Str) => -1
    case (_: Str, _: Num) => 1
    case (p: Str, q: Str) => p.value.compareTo(q.value)
    case (p: Num, q: Num) => p.value.compare(q.value)
    case _                => 0

  given Ordering[Name] = Ordering.fromLessThan((a, b) => compare(a, b) < 0)

  private def isIdentStart(c: Char): Boolean =
    c.isLetter || c == '_'

  private def isIdentRest(c: Char): Boolean =
    c.isLetterOrDigit || c == '_' || c == '\'' || c == '!' || c == '?' || c == 'ₓ'

  private def escapeNeeded(s: String): Boolean =
    s.isEmpty || !isIdentStart(s.charAt(0)) || !s.forall(isIdentRest)

  private def renderComponent(n: Name, sb: StringBuilder): Unit = n match
    case s: Str => if escapeNeeded(s.value) then sb ++= "«" ++= s.value ++= "»" else sb ++= s.value
    case m: Num => sb ++= m.value.toString
    case _      => sb ++= "[anonymous]"

  private[kernel] def render(n: Name): String =
    val cs = n.components
    if cs.isEmpty then "[anonymous]"
    else
      val sb = new StringBuilder
      var first = true
      cs.foreach { c =>
        if !first then sb += '.'
        first = false
        renderComponent(c, sb)
      }
      sb.result()
