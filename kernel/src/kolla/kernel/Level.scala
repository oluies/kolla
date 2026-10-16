package kolla.kernel

import cats.Eval
import scala.annotation.tailrec
import scala.collection.mutable

sealed abstract class Level:
  val hash: Long
  val depth: Int
  val hasParam: Boolean
  val hasMVar: Boolean

  private[kernel] def kindOrd: Int

  final override def hashCode: Int = (hash ^ (hash >>> 32)).toInt

  final override def equals(that: Any): Boolean = that match
    case l: Level => Level.structEq(this, l)
    case _        => false

  final override def toString: String = Level.render(this)

  final def isZero: Boolean  = this eq Level.Zero
  final def isSucc: Boolean  = this.isInstanceOf[Level.Succ]
  final def isMax: Boolean   = this.isInstanceOf[Level.Max]
  final def isIMax: Boolean  = this.isInstanceOf[Level.IMax]
  final def isParam: Boolean = this.isInstanceOf[Level.Param]
  final def isMVar: Boolean  = this.isInstanceOf[Level.MVar]

  final def isExplicit: Boolean = Level.isExplicit(this)
  final def toOffset: (Level, Int) = Level.toOffset(this)

  final def normalize: Level = Level.normalize(this)
  final def isEquivTo(other: Level): Boolean = Level.isEquiv(this, other)
  final def geqOf(other: Level): Boolean = Level.geq(this, other)
  final def instantiate(ps: List[Name], ls: List[Level]): Level = Level.instantiate(this, ps, ls)

object Level:

  object Zero extends Level:
    val hash: Long            = 2221L
    val depth: Int            = 0
    val hasParam: Boolean     = false
    val hasMVar: Boolean      = false
    private[kernel] def kindOrd = 0

  final case class Succ(level: Level) extends Level:
    val hash: Long            = Name.mix(2243L, level.hash)
    val depth: Int            = level.depth + 1
    val hasParam: Boolean     = level.hasParam
    val hasMVar: Boolean      = level.hasMVar
    private[kernel] def kindOrd = 1

  final case class Max(lhs: Level, rhs: Level) extends Level:
    val hash: Long            = Name.mix(2251L, Name.mix(lhs.hash, rhs.hash))
    val depth: Int            = math.max(lhs.depth, rhs.depth) + 1
    val hasParam: Boolean     = lhs.hasParam || rhs.hasParam
    val hasMVar: Boolean      = lhs.hasMVar || rhs.hasMVar
    private[kernel] def kindOrd = 2

  final case class IMax(lhs: Level, rhs: Level) extends Level:
    val hash: Long            = Name.mix(2267L, Name.mix(lhs.hash, rhs.hash))
    val depth: Int            = math.max(lhs.depth, rhs.depth) + 1
    val hasParam: Boolean     = lhs.hasParam || rhs.hasParam
    val hasMVar: Boolean      = lhs.hasMVar || rhs.hasMVar
    private[kernel] def kindOrd = 3

  final case class Param(name: Name) extends Level:
    val hash: Long            = Name.mix(2239L, name.hash)
    val depth: Int            = 0
    val hasParam: Boolean     = true
    val hasMVar: Boolean      = false
    private[kernel] def kindOrd = 4

  final case class MVar(name: Name) extends Level:
    val hash: Long            = Name.mix(2237L, name.hash)
    val depth: Int            = 0
    val hasParam: Boolean     = false
    val hasMVar: Boolean      = true
    private[kernel] def kindOrd = 5

  val zero: Level = Zero
  val one: Level  = Succ(Zero)

  def param(n: Name): Level  = Param(n)
  def param(s: String): Level = Param(Name.mkSimple(s))
  def mvar(n: Name): Level   = MVar(n)

  /** `lean::mk_succ`: no simplification. */
  def succ(l: Level): Level = Succ(l)

  @tailrec
  def succN(l: Level, k: Int): Level = if k <= 0 then l else succN(Succ(l), k - 1)

  def ofNat(k: Int): Level = succN(Zero, k)

  // ---------------------------------------------------------------- equality

  private[kernel] def structEq(a: Level, b: Level): Boolean =
    val stack = mutable.ArrayDeque.empty[(Level, Level)]
    stack.append((a, b))
    var ok = true
    while ok && stack.nonEmpty do
      val (x, y) = stack.removeLast()
      if x.asInstanceOf[AnyRef] eq y.asInstanceOf[AnyRef] then ()
      else if x.kindOrd != y.kindOrd || x.hash != y.hash then ok = false
      else
        x match
          case p: Param =>
            if p.name != y.asInstanceOf[Param].name then ok = false
          case p: MVar =>
            if p.name != y.asInstanceOf[MVar].name then ok = false
          case p: Succ =>
            val q = y.asInstanceOf[Succ]
            if p.depth != q.depth then ok = false else stack.append((p.level, q.level))
          case p: Max =>
            val q = y.asInstanceOf[Max]
            if p.depth != q.depth then ok = false
            else { stack.append((p.lhs, q.lhs)); stack.append((p.rhs, q.rhs)) }
          case p: IMax =>
            val q = y.asInstanceOf[IMax]
            if p.depth != q.depth then ok = false
            else { stack.append((p.lhs, q.lhs)); stack.append((p.rhs, q.rhs)) }
          case _ => ()
    ok

  // ------------------------------------------------------------ basic shape

  def isExplicit(l0: Level): Boolean =
    @tailrec def go(l: Level): Boolean = l match
      case s: Succ => go(s.level)
      case _       => l.isZero
    go(l0)

  /** Converts `succ^k l` into `(l, k)`. */
  def toOffset(l0: Level): (Level, Int) =
    @tailrec def go(l: Level, k: Int): (Level, Int) = l match
      case s: Succ => go(s.level, k + 1)
      case other   => (other, k)
    go(l0, 0)

  def toExplicit(l: Level): Int = toOffset(l)._2

  def isOne(l: Level): Boolean = l == one

  def isNotZero(l: Level): Boolean = isNotZeroE(l).value

  private def isNotZeroE(l: Level): Eval[Boolean] = l match
    case _: Succ => Eval.True
    case m: Max  => Eval.defer(isNotZeroE(m.lhs)).flatMap(b => if b then Eval.True else Eval.defer(isNotZeroE(m.rhs)))
    case m: IMax => Eval.defer(isNotZeroE(m.rhs))
    case _       => Eval.False

  def normalizesToZero(l: Level): Boolean = normalizesToZeroE(l).value

  private def normalizesToZeroE(l: Level): Eval[Boolean] = l match
    case _: Param | _: MVar | _: Succ => Eval.False
    case m: Max  => Eval.defer(normalizesToZeroE(m.lhs)).flatMap(b => if b then Eval.defer(normalizesToZeroE(m.rhs)) else Eval.False)
    case m: IMax => Eval.defer(normalizesToZeroE(m.rhs))
    case _       => Eval.True

  // ------------------------------------------------------- smart constructors

  /** `lean::mk_max`. */
  def max(l1: Level, l2: Level): Level =
    if isExplicit(l1) && isExplicit(l2) then (if l1.depth >= l2.depth then l1 else l2)
    else if l1 == l2 then l1
    else if l1.isZero then l2
    else if l2.isZero then l1
    else
      l2 match
        case m2: Max if m2.lhs == l1 || m2.rhs == l1 => l2
        case _ =>
          l1 match
            case m1: Max if m1.lhs == l2 || m1.rhs == l2 => l1
            case _ =>
              val (b1, k1) = toOffset(l1)
              val (b2, k2) = toOffset(l2)
              if b1 == b2 then (if k1 > k2 then l1 else l2)
              else Max(l1, l2)

  /** `lean::mk_imax`. */
  def imax(l1: Level, l2: Level): Level =
    if isNotZero(l2) then max(l1, l2)
    else if l2.isZero then l2
    else if l1.isZero || isOne(l1) then l2
    else if l1 == l2 then l1
    else IMax(l1, l2)

  private def updateSucc(l: Succ, newArg: Level): Level =
    if l.level.asInstanceOf[AnyRef] eq newArg.asInstanceOf[AnyRef] then l else Succ(newArg)

  private def updateMax(l: Level, lhs: Level, rhs: Level): Level = l match
    case m: Max =>
      if (m.lhs.asInstanceOf[AnyRef] eq lhs.asInstanceOf[AnyRef]) && (m.rhs.asInstanceOf[AnyRef] eq rhs.asInstanceOf[AnyRef]) then l
      else max(lhs, rhs)
    case m: IMax =>
      if (m.lhs.asInstanceOf[AnyRef] eq lhs.asInstanceOf[AnyRef]) && (m.rhs.asInstanceOf[AnyRef] eq rhs.asInstanceOf[AnyRef]) then l
      else imax(lhs, rhs)
    case _ => l

  // ------------------------------------------------------------ instantiation

  def instantiate(l: Level, ps: List[Name], ls: List[Level]): Level =
    if ps.isEmpty then l else instantiateE(l, ps, ls).value

  private def lookupParam(n: Name, ps: List[Name], ls: List[Level]): Option[Level] =
    @tailrec def go(ps: List[Name], ls: List[Level]): Option[Level] = (ps, ls) match
      case (p :: pt, v :: vt) => if p == n then Some(v) else go(pt, vt)
      case _                  => None
    go(ps, ls)

  private def instantiateE(l: Level, ps: List[Name], ls: List[Level]): Eval[Level] =
    if !l.hasParam then Eval.now(l)
    else
      l match
        case p: Param => Eval.now(lookupParam(p.name, ps, ls).getOrElse(l))
        case s: Succ  => Eval.defer(instantiateE(s.level, ps, ls)).map(updateSucc(s, _))
        case m: Max =>
          for
            a <- Eval.defer(instantiateE(m.lhs, ps, ls))
            b <- Eval.defer(instantiateE(m.rhs, ps, ls))
          yield updateMax(m, a, b)
        case m: IMax =>
          for
            a <- Eval.defer(instantiateE(m.lhs, ps, ls))
            b <- Eval.defer(instantiateE(m.rhs, ps, ls))
          yield updateMax(m, a, b)
        case _ => Eval.now(l)

  def paramsToLevels(ps: List[Name]): List[Level] = ps.map(Param(_))

  /** First parameter in `l` that is not listed in `ps`. */
  def undefinedParam(l: Level, ps: List[Name]): Option[Name] =
    val stack = mutable.ArrayDeque.empty[Level]
    stack.append(l)
    var r: Option[Name] = None
    while r.isEmpty && stack.nonEmpty do
      val x = stack.removeLast()
      if x.hasParam then
        x match
          case p: Param => if !ps.contains(p.name) then r = Some(p.name)
          case s: Succ  => stack.append(s.level)
          case m: Max   => stack.append(m.lhs); stack.append(m.rhs)
          case m: IMax  => stack.append(m.lhs); stack.append(m.rhs)
          case _        => ()
    r

  // ------------------------------------------------------------- normalization

  /** Total order used by `normalize`: `succ l` is the immediate successor of `l`,
    * and `zero` is minimal. Mirrors `lean::is_norm_lt`.
    */
  @tailrec
  private[kernel] def isNormLt(a: Level, b: Level): Boolean =
    if a.asInstanceOf[AnyRef] eq b.asInstanceOf[AnyRef] then false
    else
      val (l1, k1) = toOffset(a)
      val (l2, k2) = toOffset(b)
      if l1 != l2 then
        if l1.kindOrd != l2.kindOrd then l1.kindOrd < l2.kindOrd
        else
          (l1, l2) match
            case (p: Param, q: Param) => Name.compare(p.name, q.name) < 0
            case (p: MVar, q: MVar)   => Name.compare(p.name, q.name) < 0
            case (p: Max, q: Max) =>
              if p.lhs != q.lhs then isNormLt(p.lhs, q.lhs) else isNormLt(p.rhs, q.rhs)
            case (p: IMax, q: IMax) =>
              if p.lhs != q.lhs then isNormLt(p.lhs, q.lhs) else isNormLt(p.rhs, q.rhs)
            case _ => false
      else k1 < k2

  private def pushMaxArgs(l: Level, out: mutable.ArrayBuffer[Level]): Unit =
    val stack = mutable.ArrayDeque.empty[Level]
    stack.append(l)
    while stack.nonEmpty do
      stack.removeLast() match
        case m: Max => stack.append(m.rhs); stack.append(m.lhs)
        case other  => out += other

  private def maxOfArgs(args: collection.IndexedSeq[Level]): Level =
    val n = args.length
    if n == 1 then args(0)
    else
      var r = max(args(n - 2), args(n - 1))
      var i = n - 2
      while i > 0 do
        i -= 1
        r = max(args(i), r)
      r

  def normalize(l: Level): Level = normalizeE(l).value

  private def normalizeE(l: Level): Eval[Level] =
    val (base, k) = toOffset(l)
    base match
      case im: IMax =>
        for
          l1 <- Eval.defer(normalizeE(im.lhs))
          l2 <- Eval.defer(normalizeE(im.rhs))
        yield succN(imax(l1, l2), k)
      case mx: Max =>
        val todo = mutable.ArrayBuffer.empty[Level]
        pushMaxArgs(mx, todo)
        val args = mutable.ArrayBuffer.empty[Level]
        def loop(i: Int): Eval[Unit] =
          if i >= todo.length then Eval.Unit
          else
            Eval.defer(normalizeE(todo(i))).flatMap { n =>
              pushMaxArgs(n, args)
              Eval.defer(loop(i + 1))
            }
        loop(0).map(_ => finishMax(args, k))
      case _ => Eval.now(l)

  private def finishMax(argsIn: mutable.ArrayBuffer[Level], k: Int): Level =
    val args = argsIn.sortWith(isNormLt)
    val rargs = mutable.ArrayBuffer.empty[Level]
    var i = 0
    if isExplicit(args(i)) then
      while i + 1 < args.length && isExplicit(args(i + 1)) do i += 1
      val kk = toOffset(args(i))._2
      var j = i + 1
      var subsumed = false
      while j < args.length && !subsumed do
        if toOffset(args(j))._2 >= kk then subsumed = true else j += 1
      if subsumed then i += 1
    rargs += args(i)
    var prev = toOffset(args(i))
    i += 1
    while i < args.length do
      val curr = toOffset(args(i))
      if prev._1 == curr._1 then
        if prev._2 < curr._2 then
          prev = curr
          rargs.remove(rargs.length - 1)
          rargs += args(i)
      else
        prev = curr
        rargs += args(i)
      i += 1
    maxOfArgs(rargs.map(succN(_, k)))

  // ------------------------------------------------------------- comparisons

  def isEquiv(lhs: Level, rhs: Level): Boolean =
    lhs == rhs || normalize(lhs) == normalize(rhs)

  def geq(l1: Level, l2: Level): Boolean = geqE(l1, l2).value

  private def geqE(l1: Level, l2: Level): Eval[Boolean] =
    for
      a <- Eval.defer(normalizeE(l1))
      b <- Eval.defer(normalizeE(l2))
      r <- Eval.defer(geqCore(a, b))
    yield r

  private def geqCore(l1: Level, l2: Level): Eval[Boolean] =
    if l1 == l2 || l2.isZero then Eval.True
    else
      l2 match
        case m2: Max =>
          Eval.defer(geqE(l1, m2.lhs)).flatMap(b => if b then Eval.defer(geqE(l1, m2.rhs)) else Eval.False)
        case _ =>
          val viaMax1: Eval[Boolean] = l1 match
            case m1: Max =>
              Eval.defer(geqE(m1.lhs, l2)).flatMap(b => if b then Eval.True else Eval.defer(geqE(m1.rhs, l2)))
            case _ => Eval.False
          viaMax1.flatMap { hit =>
            if hit then Eval.True
            else
              l2 match
                case i2: IMax =>
                  Eval.defer(geqE(l1, i2.lhs)).flatMap(b => if b then Eval.defer(geqE(l1, i2.rhs)) else Eval.False)
                case _ =>
                  l1 match
                    case i1: IMax => Eval.defer(geqE(i1.rhs, l2))
                    case _ =>
                      val (b1, k1) = toOffset(l1)
                      val (b2, k2) = toOffset(l2)
                      if b1 == b2 || b2.isZero then Eval.now(k1 >= k2)
                      else if k1 == k2 && k1 > 0 then Eval.defer(geqE(b1, b2))
                      else Eval.False
          }

  // --------------------------------------------------------------- rendering

  private def renderChild(l: Level, sb: StringBuilder): Unit =
    if isExplicit(l) || l.isParam || l.isMVar then renderInto(l, sb)
    else { sb += '('; renderInto(l, sb); sb += ')' }

  private def renderInto(l0: Level, sb: StringBuilder): Unit =
    if isExplicit(l0) then sb ++= l0.depth.toString
    else
      l0 match
        case p: Param => sb ++= p.name.toString
        case p: MVar  => sb += '?'; sb ++= p.name.toString
        case s: Succ  => sb ++= "succ "; renderChild(s.level, sb)
        case m: Max   => sb ++= "max "; renderChild(m.lhs, sb); sb += ' '; renderChild(m.rhs, sb)
        case m: IMax  => sb ++= "imax "; renderChild(m.lhs, sb); sb += ' '; renderChild(m.rhs, sb)
        case _        => sb += '0'

  private[kernel] def render(l: Level): String =
    val sb = new StringBuilder
    renderInto(l, sb)
    sb.result()

  given Ordering[Level] = Ordering.fromLessThan(isNormLt)
