package kolla.leanexport

import kolla.kernel.*

/** A 128-bit content digest of a declaration, taken over its dependencies too.
  *
  * The point is a cache that can be reused across runs. A declaration's verdict
  * is not a function of its own text alone: it depends on every constant it
  * reaches, so a digest that ignored those would report a hit after a
  * dependency changed underneath it. The digest is therefore a Merkle hash over
  * the dependency graph — a `Const` mixes in the digest of what it names — plus
  * the profile and a cache epoch. See docs/semantics.md P15.
  *
  * It is not a cryptographic hash and does not need to be. A cache file is
  * already trusted as a whole: anything that can write it can put any digest in
  * it, so collision resistance against an adversary buys nothing. What matters
  * is the accidental collision rate, and at 128 bits that is negligible for
  * corpora of millions of declarations.
  */
final case class Digest(hi: Long, lo: Long):
  def hex: String = f"$hi%016x$lo%016x"

object Digest:

  /** Bump this on any change to kernel semantics.
    *
    * A cache entry means "this kolla accepted this declaration". If the kernel
    * changes what it accepts and the epoch does not change, a stale entry is a
    * false accept. It is the one part of the key that cannot be derived from
    * the input, so it is maintained by hand.
    */
  val epoch: String = "1"

  val seed: Digest = Digest(0x243f6a8885a308d3L, 0x13198a2e03707344L)

  def parse(s: String): Option[Digest] =
    if s.length != 32 then None
    else
      try Some(Digest(java.lang.Long.parseUnsignedLong(s.substring(0, 16), 16),
                      java.lang.Long.parseUnsignedLong(s.substring(16), 16)))
      catch case _: NumberFormatException => None

  private def avalanche(z0: Long): Long =
    var z = z0 + 0x9e3779b97f4a7c15L
    z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9L
    z = (z ^ (z >>> 27)) * 0x94d049bb133111ebL
    z ^ (z >>> 31)

  def mix(d: Digest, x: Long): Digest =
    val h = avalanche(d.hi ^ x)
    val l = avalanche(d.lo * 0x9e3779b97f4a7c15L + x)
    Digest(h ^ (l >>> 32), l ^ (h >>> 32))

  def mixAll(d: Digest, xs: Long*): Digest = xs.foldLeft(d)(mix)

  def mixString(d: Digest, s: String): Digest =
    var acc = mix(d, s.length.toLong)
    var i   = 0
    while i < s.length do
      acc = mix(acc, s.charAt(i).toLong)
      i += 1
    acc

  /** `Name.toString` is injective: `Name.parse` is its inverse, since a
    * component that would be ambiguous is rendered in guillemets. See
    * docs/semantics.md N4.
    */
  def mixName(d: Digest, n: Name): Digest = mixString(d, n.toString)

  def mixLevel(d: Digest, l: Level): Digest = l match
    case Level.Zero        => mix(d, 1L)
    case Level.Succ(x)     => mixLevel(mix(d, 2L), x)
    case Level.Max(a, b)   => mixLevel(mixLevel(mix(d, 3L), a), b)
    case Level.IMax(a, b)  => mixLevel(mixLevel(mix(d, 4L), a), b)
    case Level.Param(n)    => mixName(mix(d, 5L), n)
    case Level.MVar(n)     => mixName(mix(d, 6L), n)

  /** A memo of subterm digests, shared across one declaration.
    *
    * An export names expressions by index, so a declaration's term graph is a
    * DAG and the same subterm instance is reached many times. Walking it
    * structurally re-digests every shared subterm on every path, which is
    * exponential in the sharing, not linear in the nodes — on Mathlib it does
    * not finish. The memo is keyed by identity, which is exactly the sharing
    * the reader produced. See docs/semantics.md P16.
    */
  final class Memo:
    private val seen = scala.collection.mutable.HashMap.empty[Memo.Key, Digest]
    def getOrElseUpdate(e: Expr)(compute: => Digest): Digest =
      seen.getOrElseUpdate(new Memo.Key(e), compute)
    def size: Int = seen.size

  object Memo:
    /** Identity rather than structure: `Expr.equals` is `is_equal`, which is
      * O(size) on terms that are equal but not the same instance, and the
      * point here is to recognise the instances the reader shared.
      */
    private final class Key(val e: Expr):
      override val hashCode: Int = System.identityHashCode(e)
      override def equals(that: Any): Boolean = that match
        case k: Key => k.e eq e
        case _      => false

  /** The digest of one expression, with every `Const` and `Proj` standing for
    * what it names.
    *
    * `dep` supplies the digest of a constant already declared. A constant that
    * is not known yet — a forward reference, or one the export never declares —
    * contributes its name instead, which is the most that can be said about it.
    *
    * Binder names and `BinderInfo` are left out on purpose: `Expr.==` is
    * `lean::is_equal`, which ignores both, so two declarations that differ only
    * there are the same declaration to the kernel and must not miss the cache.
    * See docs/semantics.md X14.
    */
  def exprDigest(e: Expr, dep: Name => Option[Digest], memo: Memo): Digest =
    memo.getOrElseUpdate(e) {
      e match
        case Expr.BVar(i)  => mixAll(seed, 10L, i.toLong)
        case Expr.FVar(id) => mixName(mix(seed, 11L), id)
        case Expr.MVar(id) => mixName(mix(seed, 12L), id)
        case Expr.Sort(l)  => mixLevel(mix(seed, 13L), l)
        case Expr.Const(n, ls) =>
          val a = dep(n) match
            case Some(x) => mixAll(mix(seed, 14L), 1L, x.hi, x.lo)
            case None    => mixName(mixAll(seed, 14L, 0L), n)
          ls.foldLeft(mix(a, ls.length.toLong))(mixLevel)
        case Expr.App(f, a) =>
          val x = exprDigest(f, dep, memo)
          val y = exprDigest(a, dep, memo)
          mixAll(seed, 15L, x.hi, x.lo, y.hi, y.lo)
        case Expr.Lam(_, t, b, _) =>
          val x = exprDigest(t, dep, memo)
          val y = exprDigest(b, dep, memo)
          mixAll(seed, 16L, x.hi, x.lo, y.hi, y.lo)
        case Expr.ForallE(_, t, b, _) =>
          val x = exprDigest(t, dep, memo)
          val y = exprDigest(b, dep, memo)
          mixAll(seed, 17L, x.hi, x.lo, y.hi, y.lo)
        case Expr.LetE(_, t, v, b, nd) =>
          val x = exprDigest(t, dep, memo)
          val y = exprDigest(v, dep, memo)
          val z = exprDigest(b, dep, memo)
          mixAll(seed, 18L, if nd then 1L else 0L, x.hi, x.lo, y.hi, y.lo, z.hi, z.lo)
        case Expr.Lit(Literal.NatVal(v)) => mixString(mix(seed, 19L), v.toString)
        case Expr.Lit(Literal.StrVal(v)) => mixString(mix(seed, 20L), v)
        case Expr.MData(_, x) =>
          val y = exprDigest(x, dep, memo)
          mixAll(seed, 21L, y.hi, y.lo)
        case Expr.Proj(tn, i, st) =>
          val a = dep(tn) match
            case Some(x) => mixAll(mix(seed, 22L), 1L, x.hi, x.lo)
            case None    => mixName(mixAll(seed, 22L, 0L), tn)
          val y = exprDigest(st, dep, memo)
          mixAll(a, i.toLong, y.hi, y.lo)
    }

  /** Mixes an expression into a running digest, sharing a memo. */
  def mixExpr(d: Digest, e: Expr, dep: Name => Option[Digest], memo: Memo): Digest =
    val x = exprDigest(e, dep, memo)
    mixAll(d, x.hi, x.lo)

  private def mixConstantVal(d: Digest, v: ConstantVal, dep: Name => Option[Digest], memo: Memo): Digest =
    val a = mixName(d, v.name)
    val b = v.levelParams.foldLeft(mix(a, v.levelParams.length.toLong))(mixName)
    mixExpr(b, v.tpe, dep, memo)

  private def mixHints(d: Digest, h: ReducibilityHints): Digest = h match
    case ReducibilityHints.Opaque     => mix(d, 30L)
    case ReducibilityHints.Abbrev     => mix(d, 31L)
    case ReducibilityHints.Regular(x) => mixAll(d, 32L, x.toLong)

  private def mixSafety(d: Digest, s: DefinitionSafety): Digest = s match
    case DefinitionSafety.Unsafe  => mix(d, 40L)
    case DefinitionSafety.Safe    => mix(d, 41L)
    case DefinitionSafety.Partial => mix(d, 42L)

  def mixInfo(d: Digest, info: ConstantInfo, dep: Name => Option[Digest], memo: Memo): Digest = info match
    case ConstantInfo.AxiomInfo(v) =>
      mixAll(mixConstantVal(mix(d, 50L), v.toConstantVal, dep, memo), if v.isUnsafe then 1L else 0L)
    case ConstantInfo.DefnInfo(v) =>
      val a = mixConstantVal(mix(d, 51L), v.toConstantVal, dep, memo)
      mixSafety(mixHints(mixExpr(a, v.value, dep, memo), v.hints), v.safety)
    case ConstantInfo.ThmInfo(v) =>
      mixExpr(mixConstantVal(mix(d, 52L), v.toConstantVal, dep, memo), v.value, dep, memo)
    case ConstantInfo.OpaqueInfo(v) =>
      mixAll(mixExpr(mixConstantVal(mix(d, 53L), v.toConstantVal, dep, memo), v.value, dep, memo),
             if v.isUnsafe then 1L else 0L)
    case ConstantInfo.QuotInfo(v) =>
      mixConstantVal(mix(d, 54L), v.toConstantVal, dep, memo)
    case ConstantInfo.InductInfo(v) =>
      val a = mixConstantVal(mix(d, 55L), v.toConstantVal, dep, memo)
      val b = mixAll(a, v.numParams.toLong, v.numIndices.toLong,
                     if v.isRec then 1L else 0L, if v.isUnsafe then 1L else 0L,
                     if v.isReflexive then 1L else 0L)
      val c = v.all.foldLeft(mix(b, v.all.length.toLong))(mixName)
      v.ctors.foldLeft(mix(c, v.ctors.length.toLong))(mixName)
    case ConstantInfo.CtorInfo(v) =>
      val a = mixConstantVal(mix(d, 56L), v.toConstantVal, dep, memo)
      mixName(mixAll(a, v.cidx.toLong, v.numParams.toLong, v.numFields.toLong,
                     if v.isUnsafe then 1L else 0L), v.induct)
    case ConstantInfo.RecInfo(v) =>
      val a = mixConstantVal(mix(d, 57L), v.toConstantVal, dep, memo)
      val b = mixAll(a, v.numParams.toLong, v.numIndices.toLong, v.numMotives.toLong,
                     v.numMinors.toLong, if v.k then 1L else 0L, if v.isUnsafe then 1L else 0L)
      val c = v.all.foldLeft(mix(b, v.all.length.toLong))(mixName)
      v.rules.foldLeft(mix(c, v.rules.length.toLong)) { (acc, r) =>
        mixExpr(mixAll(mixName(acc, r.ctor), r.nfields.toLong), r.rhs, dep, memo)
      }
