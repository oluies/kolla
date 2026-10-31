package kolla.kernel

import scala.annotation.tailrec
import scala.collection.immutable.ArraySeq
import scala.collection.mutable

/** `data` is a constructor field rather than an abstract `val`, so reading it
  * is one field load the JIT can inline; as an abstract member it was a
  * call dispatched over eleven subclasses on every metadata query.
  */
sealed abstract class Expr(val data: Long):

  private[kernel] def kindOrd: Int

  final def hash: Long           = data & 0xffffffffL
  final def looseBVarRange: Int  = (data >>> 44).toInt
  final def approxDepth: Int     = ((data >>> 32) & 255L).toInt
  final def hasFVar: Boolean      = (data & (1L << 40)) != 0L
  final def hasExprMVar: Boolean  = (data & (1L << 41)) != 0L
  final def hasLevelMVar: Boolean = (data & (1L << 42)) != 0L
  final def hasLevelParam: Boolean = (data & (1L << 43)) != 0L
  final def hasLooseBVars: Boolean = looseBVarRange > 0

  final override def hashCode: Int = hash.toInt

  final override def equals(that: Any): Boolean = that match
    case e: Expr => Expr.isEqual(this, e)
    case _       => false

  final override def toString: String = Pretty.expr(this)

object Expr:

  final case class BVar(idx: Int) extends Expr(mkData(mix(7L, idx.toLong), idx + 1)):
    private[kernel] def kindOrd = 0

  final case class FVar(id: Name) extends Expr(mkData(mix(13L, id.hash), 0, 0, hasFVar = true)):
    private[kernel] def kindOrd = 1

  final case class MVar(id: Name) extends Expr(mkData(mix(17L, id.hash), 0, 0, hasExprMVar = true)):
    private[kernel] def kindOrd = 2

  final case class Sort(level: Level)
      extends Expr(
        mkData(mix(11L, level.hash), 0, 0, hasLevelMVar = level.hasMVar, hasLevelParam = level.hasParam)
      ):
    private[kernel] def kindOrd = 3

  final case class Const(name: Name, levels: List[Level])
      extends Expr(
        mkData(mix(5L, mix(name.hash, hashLevels(levels))), 0, 0,
          hasLevelMVar = levels.exists(_.hasMVar), hasLevelParam = levels.exists(_.hasParam))
      ):
    private[kernel] def kindOrd = 4

  final case class App(fn: Expr, arg: Expr) extends Expr(mkAppData(fn.data, arg.data)):
    private[kernel] def kindOrd = 5

  final case class Lam(binderName: Name, binderType: Expr, body: Expr, binderInfo: BinderInfo)
      extends Expr(mkBinderData(binderType, body)):
    private[kernel] def kindOrd = 6

  final case class ForallE(binderName: Name, binderType: Expr, body: Expr, binderInfo: BinderInfo)
      extends Expr(mkBinderData(binderType, body)):
    private[kernel] def kindOrd = 7

  final case class LetE(declName: Name, tpe: Expr, value: Expr, body: Expr, nondep: Boolean)
      extends Expr(letData(tpe, value, body)):
    private[kernel] def kindOrd = 8

  final case class Lit(value: Literal) extends Expr(mkData(Literal.hashOf(value))):
    private[kernel] def kindOrd = 9

  final case class MData(kv: KVMap, expr: Expr) extends Expr(mdataData(expr)):
    private[kernel] def kindOrd = 10

  final case class Proj(typeName: Name, idx: Int, struct: Expr) extends Expr(projData(typeName, idx, struct)):
    private[kernel] def kindOrd = 11

  // ------------------------------------------------------------------- data

  private def letData(tpe: Expr, value: Expr, body: Expr): Long =
    val d = math.max(math.max(tpe.approxDepth, value.approxDepth), body.approxDepth) + 1
    mkData(
      mix(d.toLong, mix(tpe.hash, mix(value.hash, body.hash))),
      math.max(math.max(tpe.looseBVarRange, value.looseBVarRange), math.max(body.looseBVarRange - 1, 0)),
      d,
      tpe.hasFVar || value.hasFVar || body.hasFVar,
      tpe.hasExprMVar || value.hasExprMVar || body.hasExprMVar,
      tpe.hasLevelMVar || value.hasLevelMVar || body.hasLevelMVar,
      tpe.hasLevelParam || value.hasLevelParam || body.hasLevelParam
    )

  private def mdataData(expr: Expr): Long =
    val d = expr.approxDepth + 1
    mkData(mix(d.toLong, expr.hash), expr.looseBVarRange, d,
      expr.hasFVar, expr.hasExprMVar, expr.hasLevelMVar, expr.hasLevelParam)

  private def projData(typeName: Name, idx: Int, struct: Expr): Long =
    val d = struct.approxDepth + 1
    mkData(mix(d.toLong, mix(typeName.hash, mix(idx.toLong, struct.hash))),
      struct.looseBVarRange, d,
      struct.hasFVar, struct.hasExprMVar, struct.hasLevelMVar, struct.hasLevelParam)

  val maxLooseBVarRange: Int = 1048575

  private[kernel] def mix(h: Long, k: Long): Long = Name.mix(h, k)

  private def hashLevels(ls: List[Level]): Long =
    var h = 7L
    var rest = ls
    while rest.nonEmpty do
      h = mix(h, rest.head.hash)
      rest = rest.tail
    h

  private[kernel] def mkData(
      h: Long,
      looseBVarRange: Int = 0,
      approxDepth: Int = 0,
      hasFVar: Boolean = false,
      hasExprMVar: Boolean = false,
      hasLevelMVar: Boolean = false,
      hasLevelParam: Boolean = false
  ): Long =
    if looseBVarRange < 0 || looseBVarRange > maxLooseBVarRange then
      throw KernelException.DeepRecursion(s"too many bound variables: $looseBVarRange")
    val d = if approxDepth > 255 then 255L else approxDepth.toLong
    (h & 0xffffffffL) |
      (d << 32) |
      (if hasFVar then 1L << 40 else 0L) |
      (if hasExprMVar then 1L << 41 else 0L) |
      (if hasLevelMVar then 1L << 42 else 0L) |
      (if hasLevelParam then 1L << 43 else 0L) |
      (looseBVarRange.toLong << 44)

  private def mkAppData(fd: Long, ad: Long): Long =
    val d0 = math.max((fd >>> 32) & 255L, (ad >>> 32) & 255L) + 1L
    val d  = if d0 > 255L then 255L else d0
    val range = math.max(fd >>> 44, ad >>> 44)
    val h = mix(fd, ad) & 0xffffffffL
    ((fd | ad) & (15L << 40)) | h | (d << 32) | (range << 44)

  private def mkBinderData(t: Expr, b: Expr): Long =
    val d = math.max(t.approxDepth, b.approxDepth) + 1
    mkData(
      mix(d.toLong, mix(t.hash, b.hash)),
      math.max(t.looseBVarRange, math.max(b.looseBVarRange - 1, 0)),
      d,
      t.hasFVar || b.hasFVar,
      t.hasExprMVar || b.hasExprMVar,
      t.hasLevelMVar || b.hasLevelMVar,
      t.hasLevelParam || b.hasLevelParam
    )

  // ------------------------------------------------------------- constructors

  def bvar(i: Int): Expr           = BVar(i)
  def fvar(n: Name): Expr          = FVar(n)
  def mvar(n: Name): Expr          = MVar(n)
  def sort(l: Level): Expr         = Sort(l)
  val prop: Expr                   = Sort(Level.zero)
  def const(n: Name, ls: List[Level] = Nil): Expr = Const(n, ls)
  def const(n: String): Expr       = Const(Name.parse(n), Nil)
  def app(f: Expr, a: Expr): Expr  = App(f, a)
  def natLit(v: BigInt): Expr      = Lit(Literal.NatVal(v))
  def strLit(v: String): Expr      = Lit(Literal.StrVal(v))

  def lam(n: Name, t: Expr, b: Expr, bi: BinderInfo = BinderInfo.Default): Expr = Lam(n, t, b, bi)
  def forallE(n: Name, t: Expr, b: Expr, bi: BinderInfo = BinderInfo.Default): Expr = ForallE(n, t, b, bi)
  def letE(n: Name, t: Expr, v: Expr, b: Expr, nondep: Boolean = false): Expr = LetE(n, t, v, b, nondep)
  def proj(s: Name, i: Int, e: Expr): Expr = Proj(s, i, e)
  def mdata(kv: KVMap, e: Expr): Expr = MData(kv, e)

  def mkAppN(f: Expr, args: Seq[Expr]): Expr =
    var r = f
    var i = 0
    while i < args.length do
      r = App(r, args(i))
      i += 1
    r

  def mkAppRange(f: Expr, args: IndexedSeq[Expr], from: Int, until: Int): Expr =
    var r = f
    var i = from
    while i < until do
      r = App(r, args(i))
      i += 1
    r

  // --------------------------------------------------------------- app spines

  @tailrec
  def getAppFn(e: Expr): Expr = e match
    case a: App => getAppFn(a.fn)
    case _      => e

  def getAppNumArgs(e: Expr): Int =
    @tailrec def go(e: Expr, acc: Int): Int = e match
      case a: App => go(a.fn, acc + 1)
      case _      => acc
    go(e, 0)

  /** Arguments in application order, array-backed and not copied. */
  def getAppArgs(e: Expr): ArraySeq[Expr] =
    val n = getAppNumArgs(e)
    val out = new Array[Expr](n)
    var i = n
    var cur = e
    while i > 0 do
      val a = cur.asInstanceOf[App]
      i -= 1
      out(i) = a.arg
      cur = a.fn
    ArraySeq.unsafeWrapArray(out)

  def getAppFnArgs(e: Expr): (Expr, ArraySeq[Expr]) = (getAppFn(e), getAppArgs(e))

  @tailrec
  def getRevArgD(e: Expr, i: Int, default: Expr): Expr = e match
    case a: App => if i == 0 then a.arg else getRevArgD(a.fn, i - 1, default)
    case _      => default

  def isApp(e: Expr): Boolean = e.isInstanceOf[App]

  @tailrec
  def consumeMData(e: Expr): Expr = e match
    case m: MData => consumeMData(m.expr)
    case _        => e

  def constName(e: Expr): Option[Name] = e match
    case c: Const => Some(c.name)
    case _        => None

  def isConstOf(e: Expr, n: Name): Boolean = e match
    case c: Const => c.name == n
    case _        => false

  // ---------------------------------------------------------------- equality

  private final class IdPair(val a: AnyRef, val b: AnyRef):
    override def hashCode: Int = System.identityHashCode(a) * 31 + System.identityHashCode(b)
    override def equals(that: Any): Boolean = that match
      case p: IdPair => (p.a eq a) && (p.b eq b)
      case _         => false

  /** Structural equality ignoring binder names and binder annotations, matching
    * `lean::is_equal` (`expr_eq_fn<false>`).
    */
  def isEqual(a: Expr, b: Expr): Boolean = eqCore(a, b, compareBinderInfo = false)

  /** `lean::is_bi_equal` (`expr_eq_fn<true>`). */
  def isBiEqual(a: Expr, b: Expr): Boolean = eqCore(a, b, compareBinderInfo = true)

  private def eqCore(a0: Expr, b0: Expr, compareBinderInfo: Boolean): Boolean =
    if a0.asInstanceOf[AnyRef] eq b0.asInstanceOf[AnyRef] then return true
    if a0.data != b0.data then return false
    val stack = mutable.ArrayDeque.empty[(Expr, Expr)]
    var seen: mutable.HashSet[IdPair] = null
    stack.append((a0, b0))
    var ok = true
    while ok && stack.nonEmpty do
      val (x, y) = stack.removeLast()
      if x.asInstanceOf[AnyRef] eq y.asInstanceOf[AnyRef] then ()
      else if x.hash != y.hash || x.kindOrd != y.kindOrd then ok = false
      else
        var skip = false
        x match
          case _: BVar | _: FVar | _: MVar | _: Sort | _: Lit => ()
          case _ =>
            if seen == null then seen = mutable.HashSet.empty[IdPair]
            if !seen.add(new IdPair(x, y)) then skip = true
        if !skip then
          x match
            case p: BVar => if p.idx != y.asInstanceOf[BVar].idx then ok = false
            case p: FVar => if p.id != y.asInstanceOf[FVar].id then ok = false
            case p: MVar => if p.id != y.asInstanceOf[MVar].id then ok = false
            case p: Sort => if p.level != y.asInstanceOf[Sort].level then ok = false
            case p: Lit  => if p.value != y.asInstanceOf[Lit].value then ok = false
            case p: Const =>
              val q = y.asInstanceOf[Const]
              if p.name != q.name || p.levels.length != q.levels.length || !p.levels.corresponds(q.levels)(_ == _) then ok = false
            case p: App =>
              val q = y.asInstanceOf[App]
              stack.append((p.fn, q.fn))
              stack.append((p.arg, q.arg))
            case p: Lam =>
              val q = y.asInstanceOf[Lam]
              if compareBinderInfo && (p.binderName != q.binderName || p.binderInfo != q.binderInfo) then ok = false
              else { stack.append((p.binderType, q.binderType)); stack.append((p.body, q.body)) }
            case p: ForallE =>
              val q = y.asInstanceOf[ForallE]
              if compareBinderInfo && (p.binderName != q.binderName || p.binderInfo != q.binderInfo) then ok = false
              else { stack.append((p.binderType, q.binderType)); stack.append((p.body, q.body)) }
            case p: LetE =>
              val q = y.asInstanceOf[LetE]
              if p.nondep != q.nondep || (compareBinderInfo && p.declName != q.declName) then ok = false
              else
                stack.append((p.tpe, q.tpe)); stack.append((p.value, q.value)); stack.append((p.body, q.body))
            case p: MData =>
              val q = y.asInstanceOf[MData]
              if p.kv != q.kv then ok = false else stack.append((p.expr, q.expr))
            case p: Proj =>
              val q = y.asInstanceOf[Proj]
              if p.typeName != q.typeName || p.idx != q.idx then ok = false
              else stack.append((p.struct, q.struct))
    ok
