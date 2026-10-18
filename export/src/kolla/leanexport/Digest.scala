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

  /** The expression, with every `Const` and `Proj` standing for what it names.
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
  def mixExpr(d0: Digest, e0: Expr, dep: Name => Option[Digest]): Digest =
    var acc = d0
    def go(e: Expr): Unit = e match
      case Expr.BVar(i)            => acc = mixAll(acc, 10L, i.toLong)
      case Expr.FVar(id)           => acc = mixName(mix(acc, 11L), id)
      case Expr.MVar(id)           => acc = mixName(mix(acc, 12L), id)
      case Expr.Sort(l)            => acc = mixLevel(mix(acc, 13L), l)
      case Expr.Const(n, ls) =>
        acc = mix(acc, 14L)
        dep(n) match
          case Some(x) => acc = mixAll(acc, 1L, x.hi, x.lo)
          case None    => acc = mixName(mix(acc, 0L), n)
        acc = mix(acc, ls.length.toLong)
        ls.foreach(l => acc = mixLevel(acc, l))
      case Expr.App(f, a)          => acc = mix(acc, 15L); go(f); go(a)
      case Expr.Lam(_, t, b, _)    => acc = mix(acc, 16L); go(t); go(b)
      case Expr.ForallE(_, t, b, _) => acc = mix(acc, 17L); go(t); go(b)
      case Expr.LetE(_, t, v, b, nd) =>
        acc = mixAll(acc, 18L, if nd then 1L else 0L); go(t); go(v); go(b)
      case Expr.Lit(Literal.NatVal(v)) => acc = mixString(mix(acc, 19L), v.toString)
      case Expr.Lit(Literal.StrVal(v)) => acc = mixString(mix(acc, 20L), v)
      case Expr.MData(_, x)        => acc = mix(acc, 21L); go(x)
      case Expr.Proj(tn, i, s) =>
        acc = mix(acc, 22L)
        dep(tn) match
          case Some(x) => acc = mixAll(acc, 1L, x.hi, x.lo)
          case None    => acc = mixName(mix(acc, 0L), tn)
        acc = mix(acc, i.toLong)
        go(s)
    go(e0)
    acc

  private def mixConstantVal(d: Digest, v: ConstantVal, dep: Name => Option[Digest]): Digest =
    val a = mixName(d, v.name)
    val b = v.levelParams.foldLeft(mix(a, v.levelParams.length.toLong))(mixName)
    mixExpr(b, v.tpe, dep)

  private def mixHints(d: Digest, h: ReducibilityHints): Digest = h match
    case ReducibilityHints.Opaque     => mix(d, 30L)
    case ReducibilityHints.Abbrev     => mix(d, 31L)
    case ReducibilityHints.Regular(x) => mixAll(d, 32L, x.toLong)

  private def mixSafety(d: Digest, s: DefinitionSafety): Digest = s match
    case DefinitionSafety.Unsafe  => mix(d, 40L)
    case DefinitionSafety.Safe    => mix(d, 41L)
    case DefinitionSafety.Partial => mix(d, 42L)

  def mixInfo(d: Digest, info: ConstantInfo, dep: Name => Option[Digest]): Digest = info match
    case ConstantInfo.AxiomInfo(v) =>
      mixAll(mixConstantVal(mix(d, 50L), v.toConstantVal, dep), if v.isUnsafe then 1L else 0L)
    case ConstantInfo.DefnInfo(v) =>
      val a = mixConstantVal(mix(d, 51L), v.toConstantVal, dep)
      mixSafety(mixHints(mixExpr(a, v.value, dep), v.hints), v.safety)
    case ConstantInfo.ThmInfo(v) =>
      mixExpr(mixConstantVal(mix(d, 52L), v.toConstantVal, dep), v.value, dep)
    case ConstantInfo.OpaqueInfo(v) =>
      mixAll(mixExpr(mixConstantVal(mix(d, 53L), v.toConstantVal, dep), v.value, dep),
             if v.isUnsafe then 1L else 0L)
    case ConstantInfo.QuotInfo(v) =>
      mixConstantVal(mix(d, 54L), v.toConstantVal, dep)
    case ConstantInfo.InductInfo(v) =>
      val a = mixConstantVal(mix(d, 55L), v.toConstantVal, dep)
      val b = mixAll(a, v.numParams.toLong, v.numIndices.toLong,
                     if v.isRec then 1L else 0L, if v.isUnsafe then 1L else 0L,
                     if v.isReflexive then 1L else 0L)
      val c = v.all.foldLeft(mix(b, v.all.length.toLong))(mixName)
      v.ctors.foldLeft(mix(c, v.ctors.length.toLong))(mixName)
    case ConstantInfo.CtorInfo(v) =>
      val a = mixConstantVal(mix(d, 56L), v.toConstantVal, dep)
      mixName(mixAll(a, v.cidx.toLong, v.numParams.toLong, v.numFields.toLong,
                     if v.isUnsafe then 1L else 0L), v.induct)
    case ConstantInfo.RecInfo(v) =>
      val a = mixConstantVal(mix(d, 57L), v.toConstantVal, dep)
      val b = mixAll(a, v.numParams.toLong, v.numIndices.toLong, v.numMotives.toLong,
                     v.numMinors.toLong, if v.k then 1L else 0L, if v.isUnsafe then 1L else 0L)
      val c = v.all.foldLeft(mix(b, v.all.length.toLong))(mixName)
      v.rules.foldLeft(mix(c, v.rules.length.toLong)) { (acc, r) =>
        mixExpr(mixAll(mixName(acc, r.ctor), r.nfields.toLong), r.rhs, dep)
      }
