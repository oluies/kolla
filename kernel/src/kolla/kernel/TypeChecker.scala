package kolla.kernel

import scala.annotation.tailrec
import scala.collection.immutable.ArraySeq
import scala.collection.mutable

/** Unordered pair key for the `is_def_eq` caches, matching
  * `type_checker::failed_before`'s hash-ordered lookup.
  */
private final class ExprPair(val a: Expr, val b: Expr):
  override val hashCode: Int = (a.hash + b.hash).toInt
  override def equals(that: Any): Boolean = that match
    case p: ExprPair => (p.a == a && p.b == b) || (p.a == b && p.b == a)
    case _           => false

/** `lean::type_checker`.
  *
  * One instance per declaration: the caches are plain mutable maps and are never
  * shared. All recursion runs in `Step`, which is direct while the stack is
  * shallow and trampolined through `cats.Eval` below that.
  */
final class TypeChecker(
    val env: Environment,
    val profile: KernelProfile = KernelProfile.default,
    val definitionSafety: DefinitionSafety = DefinitionSafety.Safe,
    initialLocalContext: LocalContext = LocalContext.empty,
    val maxSteps: Long = TypeChecker.defaultMaxSteps,
    /** A wall-clock bound on this declaration, alongside `maxSteps`. */
    val timeLimit: Option[TypeChecker.TimeLimit] = None
):

  private val ngen = new NameGenerator()

  /** Nesting of direct steps; see `Step`. */
  private given depth: Step.Depth = new Step.Depth

  /** `local_ctx`, append-only. Lean scopes it with `flet`, but free variable
    * identifiers are globally unique and each one keeps its type for the whole
    * run, so never discarding an entry is equivalent. See docs/semantics.md K6.
    */
  private var lctx: LocalContext = initialLocalContext

  private var lparams: Option[List[Name]] = None

  private val inferCacheCheck = mutable.HashMap.empty[Expr, Expr]
  private val inferCacheOnly  = mutable.HashMap.empty[Expr, Expr]
  private val whnfCoreCache   = mutable.HashMap.empty[Expr, Expr]
  private val whnfCache       = mutable.HashMap.empty[Expr, Expr]
  private val unfoldCache     = mutable.HashMap.empty[Expr, Expr]
  private val successCache    = mutable.HashSet.empty[ExprPair]
  private val failureCache    = mutable.HashSet.empty[ExprPair]

  private val failedPairs = mutable.ArrayDeque.empty[String]
  private var steps: Long = 0

  /** What the reduction spent itself on, for when it does not terminate.
    *
    * A declaration that never finishes cannot be diagnosed from outside: the
    * thread does not reach a safepoint, so `jstack`, `jcmd` and `SIGQUIT` are
    * all refused, and a driver that reports a step after it returns reports
    * nothing at all. These ride on the `maxSteps` guard instead, so running
    * with a lower cap turns "it is still going" into a statement of what it
    * was going on. Single-threaded by construction: one `TypeChecker` per
    * declaration, and only the checking thread touches them.
    * See docs/semantics.md K21.
    */
  /** Whether the per-constant tables are worth keeping.
    *
    * They cost two `HashMap` operations per delta attempt, which on the K21
    * example is 17.8 million of them for one declaration. A run at the
    * default budget is not going to print a report, so it does not pay for
    * them; the plain counters are a `Long` increment and stay unconditional.
    */
  private val diagnosing    = maxSteps != TypeChecker.defaultMaxSteps || timeLimit.isDefined

  timeLimit.foreach(_.begin())

  private val unfolded      = mutable.HashMap.empty[Name, Long]
  private val missed        = mutable.HashMap.empty[Name, Long]
  private var defEqCalls    = 0L
  private var deltaSteps    = 0L
  private var deltaMisses   = 0L
  private var defEqIdentical = 0L
  private var defEqCacheHit  = 0L
  private var cachedWithFVar = 0L

  /** Where the reduction went, most attempted constant first.
    *
    * Printed with the `maxSteps` exception, which is the only moment a
    * non-terminating check says anything.
    *
    * The first column is delta *attempts*, most of which `unfoldCache`
    * answers; it says which constants the search keeps reaching for, not what
    * the kernel re-derives. Re-derivation is the misses column, and on the
    * K21 example that is 128 against 17.8 million attempts. The per-constant
    * tables are only filled when a budget was set, so a default run reports
    * the counters and no breakdown.
    */
  def work: String =
    val top = unfolded.toVector.sortBy(-_._2).take(12)
    val sb  = new StringBuilder
    sb ++= f"  is_def_eq calls: $defEqCalls%,d"
    sb ++= f" (identical: $defEqIdentical%,d, cache hits: $defEqCacheHit%,d,"
    sb ++= f" distinct cached pairs: ${successCache.size}%,d,"
    sb ++= f" cache writes mentioning an fvar: $cachedWithFVar%,d,"
    sb ++= f" distinct failed pairs: ${failureCache.size}%,d)\n"
    sb ++= f"  delta attempts: $deltaSteps%,d"
    sb ++= f" of which cache misses: $deltaMisses%,d"
    sb ++= f", distinct constants: ${unfolded.size}%,d\n"
    if top.nonEmpty then
      sb ++= "  most attempted (attempts / misses):\n"
      top.foreach((n, c) => sb ++= f"    ${c}%,12d / ${missed.getOrElse(n, 0L)}%,-10d $n\n")
    sb.result()

  /** The pairs `is_def_eq` rejected, most recent last. */
  def defeqTrace: List[String] = failedPairs.toList

  def localContext: LocalContext = lctx

  private def step(): Unit =
    steps += 1
    if steps > maxSteps then
      throw KernelException(
        ExceptionKind.DeepRecursion,
        s"exceeded $maxSteps reduction steps\n$work"
      )
    timeLimit.foreach { l =>
      if steps % l.every == 0L && l.exceeded then
        throw KernelException(
          ExceptionKind.DeepRecursion,
          s"exceeded the ${l.nanos / 1000000L} ms budget after $steps reduction steps\n$work"
        )
    }

  private def recordFailure(t: Expr, s: Expr): Unit =
    if failedPairs.length >= TypeChecker.maxTraceEntries then failedPairs.removeHead()
    failedPairs.append(s"${Pretty.expr(t, 200)}  =?=  ${Pretty.expr(s, 200)}")

  private def fail(kind: ExceptionKind, detail: String): Nothing =
    throw new KernelException(kind, None, detail, defeqTrace)

  // ------------------------------------------------------------------ public

  /** `infer`: assumes the term is type correct. */
  def infer(e: Expr): Expr = inferTypeE(e, inferOnly = true).value

  /** `check(e, ps)`: also type checks, and rejects universe parameters outside `ps`. */
  def check(e: Expr, ps: List[Name]): Expr =
    lparams = Some(ps)
    try inferTypeE(e, inferOnly = false).value
    finally lparams = None

  /** `check(e)`: checks but ignores undefined universes. */
  def check(e: Expr): Expr =
    lparams = None
    inferTypeE(e, inferOnly = false).value

  def whnf(e: Expr): Expr = whnfE(e).value

  def whnfCore(e: Expr, cheapRec: Boolean = false, cheapProj: Boolean = false): Expr =
    whnfCoreE(e, cheapRec, cheapProj).value

  def isDefEq(t: Expr, s: Expr): Boolean =
    val r = isDefEqE(t, s, eager = false).value
    if r && profile.cacheDefEqSuccess then cacheSuccess(t, s)
    r

  def ensureSort(t: Expr, s: Expr): Expr = ensureSortE(t, s).value
  def ensurePi(t: Expr, s: Expr): Expr   = ensurePiE(t, s).value
  def ensureType(e: Expr): Expr          = ensureSort(infer(e), e)
  def ensureFun(e: Expr): Expr           = ensurePi(infer(e), e)

  def isProp(e: Expr): Boolean = isPropE(e).value

  // -------------------------------------------------------------- ensure/sort

  private def ensureSortE(e: Expr, s: Expr): Step[Expr] =
    if e.isInstanceOf[Expr.Sort] then Step.now(e)
    else
      Step.defer(whnfE(e)).map {
        case r: Expr.Sort => r
        case _ =>
          throw new KernelException(
            ExceptionKind.TypeExpected, None, Pretty.expr(s), defeqTrace
          )
      }

  private def ensurePiE(e: Expr, s: Expr): Step[Expr] =
    if e.isInstanceOf[Expr.ForallE] then Step.now(e)
    else
      Step.defer(whnfE(e)).map {
        case r: Expr.ForallE => r
        case _ =>
          throw new KernelException(
            ExceptionKind.FunctionExpected, None, Pretty.expr(s), defeqTrace
          )
      }

  private def checkLevel(l: Level): Unit =
    lparams.foreach { ps =>
      Level.undefinedParam(l, ps).foreach { n =>
        fail(ExceptionKind.Other, s"invalid reference to undefined universe level parameter '$n'")
      }
    }

  /** `is_prop`. v4.35 tests the level up to normalization because `imax 1 0`
    * denotes `Prop` without being syntactically `zero`.
    */
  private def isPropE(e: Expr): Step[Boolean] =
    for
      t <- Step.defer(inferTypeE(e, inferOnly = true))
      s <- Step.defer(ensureSortE(t, t))
    yield
      val l = s.asInstanceOf[Expr.Sort].level
      if profile.propByNormalization then Level.normalizesToZero(l) else l.isZero

  // ----------------------------------------------------------------- inferType

  private def inferTypeE(e: Expr, inferOnly: Boolean): Step[Expr] =
    if e.hasLooseBVars then
      fail(
        ExceptionKind.Other,
        "the type checker does not accept loose bound variables; replace them with free variables first"
      )
    step()
    val cache = if inferOnly then inferCacheOnly else inferCacheCheck
    cache.get(e) match
      case Some(r) => Step.now(r)
      case None =>
        val computed: Step[Expr] = e match
          case l: Expr.Lit     => Step.now(inferLit(l))
          case m: Expr.MData   => Step.defer(inferTypeE(m.expr, inferOnly))
          case p: Expr.Proj    => Step.defer(inferProj(p, inferOnly))
          case f: Expr.FVar    => Step.now(inferFVar(f))
          case _: Expr.MVar    => fail(ExceptionKind.DeclarationHasMetavars, "metavariables are not supported")
          case _: Expr.BVar    => fail(ExceptionKind.Other, "unexpected bound variable")
          case s: Expr.Sort =>
            if !inferOnly then checkLevel(s.level)
            Step.now(Expr.Sort(Level.Succ(s.level)))
          case c: Expr.Const   => Step.now(inferConstant(c, inferOnly))
          case l: Expr.Lam     => Step.defer(inferLambda(l, inferOnly))
          case p: Expr.ForallE => Step.defer(inferPi(p, inferOnly))
          case a: Expr.App     => Step.defer(inferApp(a, inferOnly))
          case l: Expr.LetE    => Step.defer(inferLet(l, inferOnly))
        computed.map { r =>
          cache(e) = r
          r
        }

  private def inferLit(l: Expr.Lit): Expr =
    l.value match
      case Literal.NatVal(v) => checkNatSize(natSizeInBytes(v)); ExprOps.litType(l.value)
      case _                 => ExprOps.litType(l.value)

  private def inferFVar(f: Expr.FVar): Expr =
    lctx.find(f.id) match
      case Some(d) => d.tpe
      case None    => fail(ExceptionKind.Other, s"unknown free variable '${f.id}'")

  private def inferConstant(c: Expr.Const, inferOnly: Boolean): Expr =
    val info = env.get(c.name)
    val ps   = info.levelParams
    if ps.length != c.levels.length then
      fail(
        ExceptionKind.Other,
        s"incorrect number of universe levels for '${c.name}', ${ps.length} expected, ${c.levels.length} provided"
      )
    if !inferOnly then
      if info.isUnsafe && definitionSafety != DefinitionSafety.Unsafe then
        fail(ExceptionKind.InvalidDeclaration, s"invalid declaration, it uses unsafe declaration '${c.name}'")
      info match
        case ConstantInfo.DefnInfo(d)
            if d.safety == DefinitionSafety.Partial && definitionSafety == DefinitionSafety.Safe =>
          fail(
            ExceptionKind.InvalidDeclaration,
            s"invalid declaration, a safe declaration must not contain the partial declaration '${c.name}'"
          )
        case _ => ()
      c.levels.foreach(checkLevel)
    ExprOps.instantiateLevelParams(info.tpe, ps, c.levels)

  private def inferLambda(e0: Expr.Lam, inferOnly: Boolean): Step[Expr] =
    val fvars = mutable.ArrayBuffer.empty[Expr]
    def loop(e: Expr): Step[Expr] = e match
      case l: Expr.Lam =>
        val d = ExprOps.instantiateRev(l.binderType, fvars.toIndexedSeq)
        val checked =
          if inferOnly then Step.Unit
          else Step.defer(inferTypeE(d, inferOnly)).flatMap(t => Step.defer(ensureSortE(t, d))).map(_ => ())
        checked.flatMap { _ =>
          val (next, fvar) = lctx.mkLocalDecl(ngen, l.binderName, d, l.binderInfo)
          lctx = next
          fvars += fvar
          Step.defer(loop(l.body))
        }
      case other =>
        Step.defer(inferTypeE(ExprOps.instantiateRev(other, fvars.toIndexedSeq), inferOnly))
    // `infer_lambda` returns `mk_pi`: the type of a lambda is a Pi.
    loop(e0).map(r => lctx.mkPi(fvars.toIndexedSeq, ExprOps.cheapBetaReduce(r)))

  private def inferPi(e0: Expr.ForallE, inferOnly: Boolean): Step[Expr] =
    val fvars = mutable.ArrayBuffer.empty[Expr]
    val us    = mutable.ArrayBuffer.empty[Level]
    def loop(e: Expr): Step[Expr] = e match
      case p: Expr.ForallE =>
        val d = ExprOps.instantiateRev(p.binderType, fvars.toIndexedSeq)
        for
          t1 <- Step.defer(inferTypeE(d, inferOnly))
          s1 <- Step.defer(ensureSortE(t1, d))
          r <- {
            us += s1.asInstanceOf[Expr.Sort].level
            val (next, fvar) = lctx.mkLocalDecl(ngen, p.binderName, d, p.binderInfo)
            lctx = next
            fvars += fvar
            Step.defer(loop(p.body))
          }
        yield r
      case other =>
        val body = ExprOps.instantiateRev(other, fvars.toIndexedSeq)
        for
          t <- Step.defer(inferTypeE(body, inferOnly))
          s <- Step.defer(ensureSortE(t, body))
        yield
          var r = s.asInstanceOf[Expr.Sort].level
          var i = fvars.length
          while i > 0 do
            i -= 1
            r = Level.imax(us(i), r)
          Expr.Sort(r)
    loop(e0)

  private def isEagerReduce(e: Expr): Boolean =
    Expr.isConstOf(Expr.getAppFn(e), Names.eagerReduce) && Expr.getAppNumArgs(e) == 2

  private def inferApp(e: Expr.App, inferOnly: Boolean): Step[Expr] =
    if !inferOnly then
      for
        ft0    <- Step.defer(inferTypeE(e.fn, inferOnly))
        fType  <- Step.defer(ensurePiE(ft0, e))
        aType  <- Step.defer(inferTypeE(e.arg, inferOnly))
        dType   = fType.asInstanceOf[Expr.ForallE].binderType
        ok     <- Step.defer(isDefEqE(aType, dType, eager = isEagerReduce(e.arg)))
      yield
        if !ok then
          recordFailure(aType, dType)
          throw new KernelException(
            ExceptionKind.AppTypeMismatch,
            None,
            s"application type mismatch\n  ${Pretty.expr(e)}\nargument has type\n  ${Pretty.expr(aType)}\nbut the function expects\n  ${Pretty.expr(dType)}",
            defeqTrace
          )
        ExprOps.instantiate1(fType.asInstanceOf[Expr.ForallE].body, e.arg)
    else
      val args = Expr.getAppArgs(e)
      val f    = Expr.getAppFn(e)
      Step.defer(inferTypeE(f, true)).flatMap { ft0 =>
        def loop(i: Int, j: Int, fType: Expr): Step[Expr] =
          if i >= args.length then Step.now(ExprOps.instantiateRev(fType, args.slice(j, args.length)))
          else
            fType match
              case p: Expr.ForallE => Step.defer(loop(i + 1, j, p.body))
              case _ =>
                val t = ExprOps.instantiateRev(fType, args.slice(j, i))
                Step.defer(ensurePiE(t, e)).flatMap { p =>
                  Step.defer(loop(i + 1, i, p.asInstanceOf[Expr.ForallE].body))
                }
        loop(0, 0, ft0)
      }

  private def inferLet(e0: Expr.LetE, inferOnly: Boolean): Step[Expr] =
    val fvars = mutable.ArrayBuffer.empty[Expr]
    def loop(e: Expr): Step[Expr] = e match
      case l: Expr.LetE =>
        val tpe = ExprOps.instantiateRev(l.tpe, fvars.toIndexedSeq)
        val v   = ExprOps.instantiateRev(l.value, fvars.toIndexedSeq)
        val checked: Step[Unit] =
          if inferOnly then Step.Unit
          else
            for
              tt <- Step.defer(inferTypeE(tpe, inferOnly))
              _  <- Step.defer(ensureSortE(tt, tpe))
              vt <- Step.defer(inferTypeE(v, inferOnly))
              ok <- Step.defer(isDefEqE(vt, tpe, eager = false))
            yield
              if !ok then
                recordFailure(vt, tpe)
                throw new KernelException(
                  ExceptionKind.DefinitionTypeMismatch,
                  Some(l.declName),
                  s"let value has type\n  ${Pretty.expr(vt)}\nbut is declared with type\n  ${Pretty.expr(tpe)}",
                  defeqTrace
                )
              ()
        checked.flatMap { _ =>
          val (next, fvar) = lctx.mkLetDecl(ngen, l.declName, tpe, v)
          lctx = next
          fvars += fvar
          Step.defer(loop(l.body))
        }
      case other =>
        Step.defer(inferTypeE(ExprOps.instantiateRev(other, fvars.toIndexedSeq), inferOnly))
    loop(e0).map(r => lctx.mkPi(fvars.toIndexedSeq, ExprOps.cheapBetaReduce(r), removeDeadLet = true))

  private def projIdx(p: Expr.Proj): Int =
    if profile.boundedProjIdx && p.idx < 0 then
      throw new KernelException(ExceptionKind.InvalidProj, None, Pretty.expr(p), defeqTrace)
    p.idx

  private def inferProj(p: Expr.Proj, inferOnly: Boolean): Step[Expr] =
    def invalid: Nothing =
      throw new KernelException(ExceptionKind.InvalidProj, None, Pretty.expr(p), defeqTrace)
    for
      t0   <- Step.defer(inferTypeE(p.struct, inferOnly))
      tpe  <- Step.defer(whnfE(t0))
      args  = Expr.getAppArgs(tpe)
      iName = Expr.constName(Expr.getAppFn(tpe)).getOrElse(invalid)
      _     = if iName != p.typeName then invalid
      iInfo = env.find(iName).getOrElse(invalid)
      iVal  = iInfo match
                case ConstantInfo.InductInfo(v) => v
                case _                          => invalid
      _     = if iVal.ctors.length != 1 || args.length != iVal.numParams + iVal.numIndices then invalid
      cInfo = env.get(iVal.ctors.head)
      levels = Expr.getAppFn(tpe).asInstanceOf[Expr.Const].levels
      r0    = ExprOps.instantiateLevelParams(cInfo.tpe, cInfo.levelParams, levels)
      prop <- Step.defer(isPropE(tpe))
      res  <- {
        val idx = projIdx(p)
        def params(i: Int, r: Expr): Step[Expr] =
          if i >= iVal.numParams then Step.now(r)
          else
            Step.defer(whnfE(r)).flatMap {
              case pi: Expr.ForallE => Step.defer(params(i + 1, ExprOps.instantiate1(pi.body, args(i))))
              case _                => invalid
            }
        def fields(i: Int, r: Expr): Step[Expr] =
          if i >= idx then Step.now(r)
          else
            Step.defer(whnfE(r)).flatMap {
              case pi: Expr.ForallE =>
                if ExprOps.hasLooseBVar(pi.body, 0) then
                  val dom = pi.binderType
                  Step.defer(if prop then isPropE(dom) else Step.True).flatMap { domProp =>
                    if prop && !domProp then invalid
                    else
                      Step.defer(
                        fields(i + 1, ExprOps.instantiate1(pi.body, Expr.Proj(iName, i, p.struct)))
                      )
                  }
                else Step.defer(fields(i + 1, pi.body))
              case _ => invalid
            }
        for
          afterParams <- params(0, r0)
          afterFields <- fields(0, afterParams)
          last        <- Step.defer(whnfE(afterFields))
          dom = last match
                  case pi: Expr.ForallE => pi.binderType
                  case _                => invalid
          domProp <- Step.defer(if prop then isPropE(dom) else Step.True)
        yield
          if prop && !domProp then invalid
          dom
      }
    yield res

  // ---------------------------------------------------------------- Nat size

  private def natSizeInBytes(v: BigInt): Long =
    if v.signum == 0 then 1L else ((v.bitLength + 7) / 8).toLong

  private def checkNatSize(bytes: Long): Unit =
    profile.natMaxSizeBytes.foreach { limit =>
      if bytes > limit then
        fail(
          ExceptionKind.Other,
          "the kernel refused a `Nat` numeral because its size exceeds the maximum"
        )
    }

  private def countArg(v: BigInt, op: String): Int =
    if v > BigInt(Int.MaxValue) then
      fail(
        ExceptionKind.Other,
        s"the kernel refused to evaluate `$op` because its second argument does not fit in a 32-bit unsigned integer"
      )
    v.toInt


  // --------------------------------------------------------------- reduction

  /** `is_delta`: the head constant is unfoldable. */
  private def isDelta(e: Expr): Option[ConstantInfo] =
    Expr.getAppFn(e) match
      case c: Expr.Const =>
        env.find(c.name).filter(i => i.hasValue() && c.levels.length == i.numLevelParams)
      case _ => None

  private def unfoldDefinitionCore(e: Expr): Option[Expr] = e match
    case c: Expr.Const =>
      isDelta(c).map { d =>
        // Attempts and misses are counted apart: an attempt that the cache
        // answers is cheap, and conflating the two would read a working cache
        // as repeated work. See docs/semantics.md K21.
        deltaSteps += 1
        if diagnosing then unfolded.update(c.name, unfolded.getOrElse(c.name, 0L) + 1L)
        def fresh(): Expr =
          deltaMisses += 1
          if diagnosing then missed.update(c.name, missed.getOrElse(c.name, 0L) + 1L)
          ExprOps.instantiateValueLevelParams(d, c.levels)
        if c.levels.nonEmpty then
          unfoldCache.get(c) match
            case Some(r) => r
            case None =>
              val r = fresh()
              unfoldCache(c) = r
              r
        else fresh()
      }
    case _ => None

  /** `unfold_definition`: unfolds the head of an application. */
  def unfoldDefinition(e: Expr): Option[Expr] = e match
    case _: Expr.App =>
      unfoldDefinitionCore(Expr.getAppFn(e)).map(f => Expr.mkAppN(f, Expr.getAppArgs(e)))
    case _ => unfoldDefinitionCore(e)

  /** `reduce_proj_core`. */
  private def reduceProjCore(c0: Expr, sname: Name, idx: Int): Step[Option[Expr]] =
    val prepared: Step[Expr] = c0 match
      case l: Expr.Lit =>
        l.value match
          case Literal.StrVal(v) => Step.defer(whnfE(ExprOps.stringLitToConstructor(v, profile)))
          case _                 => Step.now(c0)
      case _ => Step.now(c0)
    prepared.map { c =>
      val args = Expr.getAppArgs(c)
      Expr.constName(Expr.getAppFn(c)).flatMap(env.find).flatMap {
        case ConstantInfo.CtorInfo(mk) =>
          // `sname` selects the field layout, so a constructor of any other
          // inductive must not be projected.
          if mk.induct != sname then None
          else if mk.numParams + idx < args.length then Some(args(mk.numParams + idx))
          else None
        case _ => None
      }
    }

  private def reduceProj(p: Expr.Proj, cheapRec: Boolean, cheapProj: Boolean): Step[Option[Expr]] =
    val idx = projIdx(p)
    val c =
      if cheapProj then Step.defer(whnfCoreE(p.struct, cheapRec, cheapProj))
      else Step.defer(whnfE(p.struct))
    c.flatMap(cv => Step.defer(reduceProjCore(cv, p.typeName, idx)))

  /** `quot_reduce_rec`. */
  private def quotReduceRec(e: Expr): Step[Option[Expr]] =
    Expr.constName(Expr.getAppFn(e)) match
      case Some(n) if n == Names.quotLift || n == Names.quotInd =>
        val mkPos  = if n == Names.quotLift then 5 else 4
        val argPos = 3
        val args   = Expr.getAppArgs(e)
        if args.length <= mkPos then Step.now(None)
        else
          Step.defer(whnfE(args(mkPos))).map { mk =>
            if !Expr.isConstOf(Expr.getAppFn(mk), Names.quotMk) || Expr.getAppNumArgs(mk) != 3 then None
            else
              val f = args(argPos)
              var r: Expr = Expr.App(f, Expr.getAppArgs(mk).last)
              val elimArity = mkPos + 1
              if args.length > elimArity then r = Expr.mkAppRange(r, args, elimArity, args.length)
              Some(r)
          }
      case _ => Step.now(None)

  private def firstCtor(n: Name): Option[Name] =
    env.find(n).collect { case ConstantInfo.InductInfo(v) => v }.flatMap(_.ctors.headOption)

  private def isNonRecStructure(n: Name): Boolean =
    env.find(n) match
      case Some(ConstantInfo.InductInfo(v)) =>
        v.ctors.length == 1 && v.numIndices == 0 && (!profile.etaStructRequiresNonRec || !v.isRec)
      case _ => false

  private def isCtorApp(e: Expr): Boolean =
    Expr.constName(Expr.getAppFn(e)).flatMap(env.find).exists(_.isConstructor)

  /** `expand_eta_struct`: `e` as `C.mk e.1 ... e.n`. */
  private def expandEtaStruct(eType: Expr, e: Expr): Expr =
    val args = Expr.getAppArgs(eType)
    Expr.getAppFn(eType) match
      case i: Expr.Const =>
        firstCtor(i.name) match
          case Some(ctorName) =>
            val ctor = env.get(ctorName).asInstanceOf[ConstantInfo.CtorInfo].value
            var r: Expr = Expr.mkAppRange(Expr.Const(ctorName, i.levels), args, 0, math.min(ctor.numParams, args.length))
            var k = 0
            while k < ctor.numFields do
              r = Expr.App(r, Expr.Proj(i.name, k, e))
              k += 1
            r
          case None => e
      case _ => e

  /** `to_cnstr_when_structure`. */
  private def toCtorWhenStructure(inductName: Name, e: Expr): Step[Expr] =
    if !isNonRecStructure(inductName) || isCtorApp(e) then Step.now(e)
    else
      Step.defer(inferTypeE(e, inferOnly = true)).flatMap(t => Step.defer(whnfE(t))).flatMap { eType =>
        if !Expr.isConstOf(Expr.getAppFn(eType), inductName) then Step.now(e)
        else
          Step.defer(isPropE(eType)).map { p =>
            if p then e else expandEtaStruct(eType, e)
          }
      }

  /** `mk_nullary_cnstr`. */
  private def mkNullaryCtor(tpe: Expr, numParams: Int): Option[Expr] =
    val args = Expr.getAppArgs(tpe)
    Expr.getAppFn(tpe) match
      case d: Expr.Const =>
        firstCtor(d.name).map { c =>
          Expr.mkAppRange(Expr.Const(c, d.levels), args, 0, math.min(numParams, args.length))
        }
      case _ => None

  /** `to_cnstr_when_K`: K-like reduction. */
  private def toCtorWhenK(rval: RecursorVal, e: Expr): Step[Expr] =
    for
      t0      <- Step.defer(inferTypeE(e, inferOnly = true))
      appType <- Step.defer(whnfE(t0))
      r <-
        if !Expr.isConstOf(Expr.getAppFn(appType), rval.majorInduct) then Step.now(e)
        else
          mkNullaryCtor(appType, rval.numParams) match
            case None => Step.now(e)
            case Some(newCtorApp) =>
              for
                newType <- Step.defer(inferTypeE(newCtorApp, inferOnly = true))
                ok      <- Step.defer(isDefEqE(appType, newType, eager = false))
              yield if ok then newCtorApp else e
    yield r

  private def recRuleFor(rval: RecursorVal, major: Expr): Option[RecursorRule] =
    Expr.constName(Expr.getAppFn(major)).flatMap(n => rval.rules.find(_.ctor == n))

  /** `inductive_reduce_rec`: iota reduction. */
  private def inductiveReduceRec(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Step[Option[Expr]] =
    val recFn = Expr.getAppFn(e)
    Expr.constName(recFn).flatMap(env.find) match
      case Some(ConstantInfo.RecInfo(rval)) =>
        val recArgs  = Expr.getAppArgs(e)
        val majorIdx = rval.majorIdx
        if majorIdx >= recArgs.length then Step.now(None)
        else
          val reduceMajor: Expr => Step[Expr] =
            if cheapRec then x => whnfCoreE(x, cheapRec, cheapProj) else x => whnfE(x)
          val major0 = recArgs(majorIdx)
          for
            afterK <- if rval.k then Step.defer(toCtorWhenK(rval, major0)) else Step.now(major0)
            w      <- Step.defer(reduceMajor(afterK))
            major <- w match
                       case l: Expr.Lit =>
                         l.value match
                           case Literal.NatVal(v) => Step.now(ExprOps.natLitToConstructor(v))
                           case Literal.StrVal(v) =>
                             Step.defer(whnfE(ExprOps.stringLitToConstructor(v, profile)))
                       case other => Step.defer(toCtorWhenStructure(rval.majorInduct, other))
          yield
            recRuleFor(rval, major) match
              case None => None
              case Some(rule) =>
                val majorArgs = Expr.getAppArgs(major)
                if rule.nfields > majorArgs.length then None
                else
                  val levels = recFn.asInstanceOf[Expr.Const].levels
                  if levels.length != rval.toConstantVal.levelParams.length then None
                  else
                    var rhs = ExprOps.instantiateLevelParams(rule.rhs, rval.toConstantVal.levelParams, levels)
                    val nPrefix = rval.numParams + rval.numMotives + rval.numMinors
                    rhs = Expr.mkAppRange(rhs, recArgs, 0, math.min(nPrefix, recArgs.length))
                    // A nested inductive's constructor need not have as many
                    // parameters as its recursor.
                    val nparams = majorArgs.length - rule.nfields
                    rhs = Expr.mkAppRange(rhs, majorArgs, nparams, majorArgs.length)
                    if recArgs.length > majorIdx + 1 then
                      rhs = Expr.mkAppRange(rhs, recArgs, majorIdx + 1, recArgs.length)
                    Some(rhs)
      case _ => Step.now(None)

  private def reduceRecursor(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Step[Option[Expr]] =
    val quot: Step[Option[Expr]] =
      if env.quotInitialized then Step.defer(quotReduceRec(e)) else Step.now(None)
    quot.flatMap {
      case Some(r) => Step.now(Some(r))
      case None    => Step.defer(inductiveReduceRec(e, cheapRec, cheapProj))
    }

  private def whnfFVar(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Step[Expr] =
    lctx.find(e).flatMap(_.value) match
      case Some(v) => Step.defer(whnfCoreE(v, cheapRec, cheapProj)) // zeta
      case None    => Step.now(e)

  /** `whnf_core`: every reduction except delta and the normalizer extensions. */
  private def whnfCoreE(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Step[Expr] =
    step()
    e match
      case _: Expr.BVar | _: Expr.Sort | _: Expr.MVar | _: Expr.ForallE | _: Expr.Const | _: Expr.Lam |
          _: Expr.Lit =>
        Step.now(e)
      case m: Expr.MData => Step.defer(whnfCoreE(m.expr, cheapRec, cheapProj))
      case f: Expr.FVar =>
        if lctx.isLetFVar(f) then Step.defer(whnfFVar(f, cheapRec, cheapProj)) else Step.now(e)
      case _ =>
        val cacheable = !cheapRec && !cheapProj
        if cacheable then
          whnfCoreCache.get(e) match
            case Some(r) => return Step.now(r)
            case None    => ()
        val computed: Step[Expr] = e match
          case p: Expr.Proj =>
            Step.defer(reduceProj(p, cheapRec, cheapProj)).flatMap {
              case Some(m) => Step.defer(whnfCoreE(m, cheapRec, cheapProj))
              case None    => Step.now(e)
            }
          case a: Expr.App =>
            val args = Expr.getAppArgs(a)
            val f0   = Expr.getAppFn(a)
            Step.defer(whnfCoreE(f0, cheapRec, cheapProj)).flatMap { f =>
              if f.isInstanceOf[Expr.Lam] then
                Step.defer(whnfCoreE(ExprOps.betaReduce(f, args), cheapRec, cheapProj))
              else if f == f0 then
                Step.defer(reduceRecursor(a, cheapRec, cheapProj)).flatMap {
                  case Some(r) => Step.defer(whnfCoreE(r, cheapRec, cheapProj))
                  case None    => Step.now(e)
                }
              else Step.defer(whnfCoreE(Expr.mkAppN(f, args), cheapRec, cheapProj))
            }
          case l: Expr.LetE =>
            Step.defer(whnfCoreE(ExprOps.instantiate1(l.body, l.value), cheapRec, cheapProj))
          case other => Step.now(other)
        computed.map { r =>
          if cacheable then whnfCoreCache(e) = r
          r
        }

  /** `whnf`. */
  private def whnfE(e: Expr): Step[Expr] =
    e match
      case _: Expr.BVar | _: Expr.Sort | _: Expr.MVar | _: Expr.ForallE | _: Expr.Lit => Step.now(e)
      case m: Expr.MData => Step.defer(whnfE(m.expr))
      case f: Expr.FVar if !lctx.isLetFVar(f) => Step.now(e)
      case _ =>
        whnfCache.get(e) match
          case Some(r) => Step.now(r)
          case None =>
            def loop(t: Expr): Step[Expr] =
              Step.defer(whnfCoreE(t, false, false)).flatMap { t1 =>
                Step.defer(reduceNat(t1)).flatMap {
                  case Some(v) => Step.now(v)
                  case None =>
                    unfoldDefinition(t1) match
                      case Some(next) => Step.defer(loop(next))
                      case None       => Step.now(t1)
                }
              }
            loop(e).map { r =>
              whnfCache(e) = r
              r
            }

  // ------------------------------------------------------- Nat literal rules

  private def isNatLitExt(e: Expr): Boolean = e match
    case l: Expr.Lit => l.value.isInstanceOf[Literal.NatVal]
    case c: Expr.Const => c.name == Names.natZero && c.levels.isEmpty
    case _ => false

  private def natVal(e: Expr): BigInt = e match
    case l: Expr.Lit =>
      l.value match
        case Literal.NatVal(v) => v
        case _                 => BigInt(0)
    case _ => BigInt(0)

  private def binNatArgs(e: Expr): Step[Option[(BigInt, BigInt)]] =
    val fn = e.asInstanceOf[Expr.App]
    for
      a1 <- Step.defer(whnfE(fn.fn.asInstanceOf[Expr.App].arg))
      r <-
        if !isNatLitExt(a1) then Step.now(None)
        else
          Step.defer(whnfE(fn.arg)).map { a2 =>
            if !isNatLitExt(a2) then None else Some((natVal(a1), natVal(a2)))
          }
    yield r

  private def binNatOp(e: Expr, checkSize: Boolean)(f: (BigInt, BigInt) => BigInt): Step[Option[Expr]] =
    binNatArgs(e).map {
      case None => None
      case Some((v1, v2)) =>
        val r = f(v1, v2)
        if checkSize then checkNatSize(natSizeInBytes(r))
        Some(Expr.natLit(r))
    }

  private def binNatPred(e: Expr)(f: (BigInt, BigInt) => Boolean): Step[Option[Expr]] =
    binNatArgs(e).map {
      case None           => None
      case Some((v1, v2)) => Some(Expr.const(if f(v1, v2) then Names.boolTrue else Names.boolFalse))
    }

  private def reducePow(e: Expr): Step[Option[Expr]] =
    binNatArgs(e).map {
      case None => None
      case Some((base, exp)) =>
        val k = countArg(exp, "Nat.pow")
        profile.natMaxSizeBytes.foreach { limit =>
          if base > 1 && k != 0 && natSizeInBytes(base) > limit / k then
            fail(
              ExceptionKind.Other,
              "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size"
            )
        }
        Some(Expr.natLit(base.pow(k)))
    }

  private def reduceShiftLeft(e: Expr): Step[Option[Expr]] =
    binNatArgs(e).map {
      case None => None
      case Some((v, shift)) =>
        if v.signum != 0 then
          val k = countArg(shift, "Nat.shiftLeft")
          checkNatSize(natSizeInBytes(v) + k / 8 + 1)
          Some(Expr.natLit(v << k))
        else Some(Expr.natLit(BigInt(0)))
    }

  /** `reduce_nat`: the `Nat` literal extensions. */
  private def reduceNat(e: Expr): Step[Option[Expr]] =
    val nargs = Expr.getAppNumArgs(e)
    if nargs == 1 then
      val a = e.asInstanceOf[Expr.App]
      if Expr.isConstOf(a.fn, Names.natSucc) then
        Step.defer(whnfE(a.arg)).map { arg =>
          if !isNatLitExt(arg) then None
          else
            val v = natVal(arg) + 1
            checkNatSize(natSizeInBytes(v))
            Some(Expr.natLit(v))
        }
      else Step.now(None)
    else if nargs == 2 then
      Expr.constName(Expr.getAppFn(e)) match
        case Some(n) if n == Names.natAdd   => binNatOp(e, true)(_ + _)
        case Some(n) if n == Names.natSub   => binNatOp(e, true)((a, b) => if a > b then a - b else BigInt(0))
        case Some(n) if n == Names.natMul   => binNatOp(e, true)(_ * _)
        case Some(n) if n == Names.natPow   => reducePow(e)
        case Some(n) if n == Names.natGcd   => binNatOp(e, false)(_.gcd(_))
        case Some(n) if n == Names.natMod   => binNatOp(e, false)((a, b) => if b.signum == 0 then a else a mod b)
        case Some(n) if n == Names.natDiv   => binNatOp(e, false)((a, b) => if b.signum == 0 then BigInt(0) else a / b)
        case Some(n) if n == Names.natBeq   => binNatPred(e)(_ == _)
        case Some(n) if n == Names.natBle   => binNatPred(e)(_ <= _)
        case Some(n) if n == Names.natLand  => binNatOp(e, false)(_ & _)
        case Some(n) if n == Names.natLor   => binNatOp(e, false)(_ | _)
        case Some(n) if n == Names.natXor   => binNatOp(e, false)(_ ^ _)
        case Some(n) if n == Names.natShiftLeft  => reduceShiftLeft(e)
        case Some(n) if n == Names.natShiftRight =>
          binNatOp(e, false)((v, s) => if s > BigInt(Int.MaxValue) then BigInt(0) else v >> s.toInt)
        case _ => Step.now(None)
    else Step.now(None)

  // ------------------------------------------------------------- is_def_eq

  private def cacheSuccess(t: Expr, s: Expr): Unit =
    // A count of writes, not of entries: it exceeded the set's size when
    // measured, which is how the duplicate writes were noticed. `hasFVar` is
    // in the cached data word, so this is O(1). See docs/semantics.md K21.
    if diagnosing && (t.hasFVar || s.hasFVar) then cachedWithFVar += 1
    successCache.add(new ExprPair(t, s))
  private def succeededBefore(t: Expr, s: Expr): Boolean =
    profile.cacheDefEqSuccess && successCache.contains(new ExprPair(t, s))
  private def cacheFailure(t: Expr, s: Expr): Unit = failureCache.add(new ExprPair(t, s))
  private def failedBefore(t: Expr, s: Expr): Boolean = failureCache.contains(new ExprPair(t, s))

  private def isDefEqLevels(ls1: List[Level], ls2: List[Level]): Boolean =
    ls1.length == ls2.length && ls1.corresponds(ls2)(Level.isEquiv)

  /** `is_def_eq_binding`. */
  private def isDefEqBinding(t0: Expr, s0: Expr, eager: Boolean): Step[Boolean] =
    val subst = mutable.ArrayBuffer.empty[Expr]
    def loop(t: Expr, s: Expr): Step[Boolean] =
      val (td, tb, sd, sb, bn, bi) = (t, s) match
        case (a: Expr.Lam, b: Expr.Lam) =>
          (a.binderType, a.body, b.binderType, b.body, b.binderName, b.binderInfo)
        case (a: Expr.ForallE, b: Expr.ForallE) =>
          (a.binderType, a.body, b.binderType, b.body, b.binderName, b.binderInfo)
        case _ => return Step.defer(
            isDefEqE(
              ExprOps.instantiateRev(t, subst.toIndexedSeq),
              ExprOps.instantiateRev(s, subst.toIndexedSeq),
              eager
            )
          )
      val domainsEqual: Step[Boolean] =
        if td == sd then Step.True
        else
          val vs = ExprOps.instantiateRev(sd, subst.toIndexedSeq)
          val vt = ExprOps.instantiateRev(td, subst.toIndexedSeq)
          Step.defer(isDefEqE(vt, vs, eager))
      domainsEqual.flatMap { ok =>
        if !ok then Step.False
        else
          if tb.hasLooseBVars || sb.hasLooseBVars then
            val vs           = ExprOps.instantiateRev(sd, subst.toIndexedSeq)
            val (next, fvar) = lctx.mkLocalDecl(ngen, bn, vs, bi)
            lctx = next
            subst += fvar
          else subst += TypeChecker.dontCare
          if tb.getClass == t.getClass && sb.getClass == s.getClass then Step.defer(loop(tb, sb))
          else
            Step.defer(
              isDefEqE(
                ExprOps.instantiateRev(tb, subst.toIndexedSeq),
                ExprOps.instantiateRev(sb, subst.toIndexedSeq),
                eager
              )
            )
      }
    loop(t0, s0)

  /** `quick_is_def_eq`: `None` means "not an easy case". */
  private def quickIsDefEq(t: Expr, s: Expr, eager: Boolean): Step[Option[Boolean]] =
    if t == s then
      defEqIdentical += 1
      Step.now(Some(true))
    else if succeededBefore(t, s) then
      defEqCacheHit += 1
      Step.now(Some(true))
    else if t.kindOrd == s.kindOrd then
      (t, s) match
        case (_: Expr.Lam, _: Expr.Lam) | (_: Expr.ForallE, _: Expr.ForallE) =>
          Step.defer(isDefEqBinding(t, s, eager)).map(Some(_))
        case (a: Expr.Sort, b: Expr.Sort) => Step.now(Some(Level.isEquiv(a.level, b.level)))
        case (a: Expr.MData, b: Expr.MData) => Step.defer(isDefEqE(a.expr, b.expr, eager)).map(Some(_))
        case (a: Expr.Lit, b: Expr.Lit)   => Step.now(Some(a.value == b.value))
        case _                            => Step.now(None)
    else Step.now(None)

  /** `is_def_eq_args`. */
  private def isDefEqArgs(t0: Expr, s0: Expr, eager: Boolean): Step[Boolean] =
    def loop(t: Expr, s: Expr): Step[Boolean] = (t, s) match
      case (a: Expr.App, b: Expr.App) =>
        Step.defer(isDefEqE(a.arg, b.arg, eager)).flatMap { ok =>
          if !ok then Step.False else Step.defer(loop(a.fn, b.fn))
        }
      case _ => Step.now(!t.isInstanceOf[Expr.App] && !s.isInstanceOf[Expr.App])
    loop(t0, s0)

  /** `try_eta_expansion_core`. */
  private def tryEtaExpansionCore(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    if t.isInstanceOf[Expr.Lam] && !s.isInstanceOf[Expr.Lam] then
      for
        st0 <- Step.defer(inferTypeE(s, inferOnly = true))
        st  <- Step.defer(whnfE(st0))
        r <- st match
               case pi: Expr.ForallE =>
                 val newS = Expr.Lam(pi.binderName, pi.binderType, Expr.App(s, Expr.BVar(0)), pi.binderInfo)
                 Step.defer(isDefEqE(t, newS, eager))
               case _ => Step.False
      yield r
    else Step.False

  private def tryEtaExpansion(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    Step.defer(tryEtaExpansionCore(t, s, eager)).flatMap { ok =>
      if ok then Step.True else Step.defer(tryEtaExpansionCore(s, t, eager))
    }

  /** `try_eta_struct_core`: is `s` of the form `mk t.1 ... t.n`? */
  private def tryEtaStructCore(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    Expr.constName(Expr.getAppFn(s)).flatMap(env.find) match
      case Some(ConstantInfo.CtorInfo(fv)) =>
        if Expr.getAppNumArgs(s) != fv.numParams + fv.numFields then Step.False
        else if !isNonRecStructure(fv.induct) then Step.False
        else
          for
            tt <- Step.defer(inferTypeE(t, inferOnly = true))
            st <- Step.defer(inferTypeE(s, inferOnly = true))
            ok <- Step.defer(isDefEqE(tt, st, eager))
            r <-
              if !ok then Step.False
              else
                val sArgs = Expr.getAppArgs(s)
                def loop(i: Int): Step[Boolean] =
                  if i >= sArgs.length then Step.True
                  else
                    val proj = Expr.Proj(fv.induct, i - fv.numParams, t)
                    Step.defer(isDefEqE(proj, sArgs(i), eager)).flatMap { o =>
                      if !o then Step.False else Step.defer(loop(i + 1))
                    }
                loop(fv.numParams)
          yield r
      case _ => Step.False

  private def tryEtaStruct(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    Step.defer(tryEtaStructCore(t, s, eager)).flatMap { ok =>
      if ok then Step.True else Step.defer(tryEtaStructCore(s, t, eager))
    }

  /** `is_def_eq_app`. */
  private def isDefEqApp(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    if t.isInstanceOf[Expr.App] && s.isInstanceOf[Expr.App] then
      val tArgs = Expr.getAppArgs(t)
      val sArgs = Expr.getAppArgs(s)
      if tArgs.length != sArgs.length then Step.False
      else
        Step.defer(isDefEqE(Expr.getAppFn(t), Expr.getAppFn(s), eager)).flatMap { ok =>
          if !ok then Step.False
          else
            def loop(i: Int): Step[Boolean] =
              if i >= tArgs.length then Step.True
              else
                Step.defer(isDefEqE(tArgs(i), sArgs(i), eager)).flatMap { o =>
                  if !o then Step.False else Step.defer(loop(i + 1))
                }
            loop(0)
        }
    else Step.False

  /** `is_def_eq_proof_irrel`. */
  private def isDefEqProofIrrel(t: Expr, s: Expr, eager: Boolean): Step[Option[Boolean]] =
    for
      tType <- Step.defer(inferTypeE(t, inferOnly = true))
      p     <- Step.defer(isPropE(tType))
      r <-
        if !p then Step.now(None)
        else
          for
            sType <- Step.defer(inferTypeE(s, inferOnly = true))
            ok    <- Step.defer(isDefEqE(tType, sType, eager))
          yield Some(ok)
    yield r

  /** `is_def_eq_unit_like`. */
  private def isDefEqUnitLike(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    for
      t0    <- Step.defer(inferTypeE(t, inferOnly = true))
      tType <- Step.defer(whnfE(t0))
      r <- Expr.constName(Expr.getAppFn(tType)) match
             case Some(i) if isNonRecStructure(i) =>
               val ctorName = env.get(i).asInstanceOf[ConstantInfo.InductInfo].value.ctors.head
               val ctorVal  = env.get(ctorName).asInstanceOf[ConstantInfo.CtorInfo].value
               if ctorVal.numFields != 0 then Step.False
               else
                 Step.defer(inferTypeE(s, inferOnly = true)).flatMap(st =>
                   Step.defer(isDefEqE(tType, st, eager))
                 )
             case _ => Step.False
    yield r

  /** `try_string_lit_expansion_core`. */
  private def tryStringLitExpansionCore(t: Expr, s: Expr, eager: Boolean): Step[Option[Boolean]] =
    t match
      case l: Expr.Lit =>
        l.value match
          case Literal.StrVal(v)
              if s.isInstanceOf[Expr.App] &&
                Expr.isConstOf(s.asInstanceOf[Expr.App].fn, profile.stringLiteralCtor) =>
            Step
              .defer(whnfE(ExprOps.stringLitToConstructor(v, profile)))
              .flatMap(x => Step.defer(isDefEqE(x, s, eager)))
              .map(Some(_))
          case _ => Step.now(None)
      case _ => Step.now(None)

  private def tryStringLitExpansion(t: Expr, s: Expr, eager: Boolean): Step[Option[Boolean]] =
    Step.defer(tryStringLitExpansionCore(t, s, eager)).flatMap {
      case Some(r) => Step.now(Some(r))
      case None    => Step.defer(tryStringLitExpansionCore(s, t, eager))
    }

  private def tryUnfoldProjApp(e: Expr): Step[Option[Expr]] =
    if Expr.getAppFn(e).isInstanceOf[Expr.Proj] then
      Step.defer(whnfCoreE(e, false, false)).map(n => if n != e then Some(n) else None)
    else Step.now(None)

  private enum ReductionStatus:
    case Continue, DefUnknown, DefEqual, DefDiff

  /** `lazy_delta_reduction_step`. */
  private def lazyDeltaReductionStep(t: Expr, s: Expr, eager: Boolean): Step[(ReductionStatus, Expr, Expr)] =
    val dt = isDelta(t)
    val ds = isDelta(s)
    // `Left` is a status the step reached on its own, `Right` the pair to retry
    // `quick_is_def_eq` on. The two cannot be collapsed into a non-local return:
    // a suspended `Step` runs its continuations after this method's frame is gone.
    val stepped: Step[Either[(ReductionStatus, Expr, Expr), (Expr, Expr)]] =
      (dt, ds) match
        case (None, None) => Step.now(Left((ReductionStatus.DefUnknown, t, s)))
        case (Some(_), None) =>
          Step.defer(tryUnfoldProjApp(s)).flatMap {
            case Some(sNew) => Step.now(Right((t, sNew)))
            case None =>
              Step.defer(whnfCoreE(unfoldDefinition(t).get, false, true)).map(tn => Right((tn, s)))
          }
        case (None, Some(_)) =>
          Step.defer(tryUnfoldProjApp(t)).flatMap {
            case Some(tNew) => Step.now(Right((tNew, s)))
            case None =>
              Step.defer(whnfCoreE(unfoldDefinition(s).get, false, true)).map(sn => Right((t, sn)))
          }
        case (Some(a), Some(b)) =>
          val c = ReducibilityHints.compare(a.hints, b.hints)
          if c < 0 then Step.defer(whnfCoreE(unfoldDefinition(t).get, false, true)).map(tn => Right((tn, s)))
          else if c > 0 then Step.defer(whnfCoreE(unfoldDefinition(s).get, false, true)).map(sn => Right((t, sn)))
          else
            val sameAndRegular =
              t.isInstanceOf[Expr.App] && s.isInstanceOf[Expr.App] && a.name == b.name && a.hints.isRegular
            val shortcut: Step[Boolean] =
              if sameAndRegular && !failedBefore(t, s) then
                val tl = Expr.getAppFn(t).asInstanceOf[Expr.Const].levels
                val sl = Expr.getAppFn(s).asInstanceOf[Expr.Const].levels
                if isDefEqLevels(tl, sl) then
                  Step.defer(isDefEqArgs(t, s, eager)).map { ok =>
                    if !ok then cacheFailure(t, s)
                    ok
                  }
                else { cacheFailure(t, s); Step.False }
              else Step.False
            shortcut.flatMap { hit =>
              if hit then Step.now(Left((ReductionStatus.DefEqual, t, s)))
              else
                for
                  tn <- Step.defer(whnfCoreE(unfoldDefinition(t).get, false, true))
                  sn <- Step.defer(whnfCoreE(unfoldDefinition(s).get, false, true))
                yield Right((tn, sn))
            }
    stepped.flatMap {
      case Left(done) => Step.now(done)
      case Right((tn, sn)) =>
        Step.defer(quickIsDefEq(tn, sn, eager)).map {
          case Some(true)  => (ReductionStatus.DefEqual, tn, sn)
          case Some(false) => (ReductionStatus.DefDiff, tn, sn)
          case None        => (ReductionStatus.Continue, tn, sn)
        }
    }

  private def isNatZero(t: Expr): Boolean = t match
    case c: Expr.Const => c.name == Names.natZero
    case l: Expr.Lit =>
      l.value match
        case Literal.NatVal(v) => v.signum == 0
        case _                 => false
    case _ => false

  private def isNatSucc(t: Expr): Option[Expr] = t match
    case l: Expr.Lit =>
      l.value match
        case Literal.NatVal(v) if v.signum != 0 => Some(Expr.natLit(v - 1))
        case _                                  => None
    case _ =>
      if Expr.isConstOf(Expr.getAppFn(t), Names.natSucc) && Expr.getAppNumArgs(t) == 1 then
        Some(t.asInstanceOf[Expr.App].arg)
      else None

  /** `is_def_eq_offset`. */
  private def isDefEqOffset(t: Expr, s: Expr, eager: Boolean): Step[Option[Boolean]] =
    if isNatZero(t) && isNatZero(s) then Step.now(Some(true))
    else
      (isNatSucc(t), isNatSucc(s)) match
        case (Some(pt), Some(ps)) => Step.defer(isDefEqCoreE(pt, ps, eager)).map(Some(_))
        case _                    => Step.now(None)

  /** `lazy_delta_reduction`. */
  private def lazyDeltaReduction(t0: Expr, s0: Expr, eager: Boolean): Step[(Option[Boolean], Expr, Expr)] =
    def loop(t: Expr, s: Expr): Step[(Option[Boolean], Expr, Expr)] =
      Step.defer(isDefEqOffset(t, s, eager)).flatMap {
        case Some(r) => Step.now((Some(r), t, s))
        case None =>
          val natPath: Step[Option[Boolean]] =
            if (!t.hasFVar && !s.hasFVar) || eager then
              Step.defer(reduceNat(t)).flatMap {
                case Some(tv) => Step.defer(isDefEqCoreE(tv, s, eager)).map(Some(_))
                case None =>
                  Step.defer(reduceNat(s)).flatMap {
                    case Some(sv) => Step.defer(isDefEqCoreE(t, sv, eager)).map(Some(_))
                    case None     => Step.now(None)
                  }
              }
            else Step.now(None)
          natPath.flatMap {
            case Some(r) => Step.now((Some(r), t, s))
            case None =>
              Step.defer(lazyDeltaReductionStep(t, s, eager)).flatMap { (status, tn, sn) =>
                status match
                  case ReductionStatus.Continue   => Step.defer(loop(tn, sn))
                  case ReductionStatus.DefUnknown => Step.now((None, tn, sn))
                  case ReductionStatus.DefEqual   => Step.now((Some(true), tn, sn))
                  case ReductionStatus.DefDiff    => Step.now((Some(false), tn, sn))
              }
          }
      }
    loop(t0, s0)

  /** `lazy_delta_proj_reduction`. */
  private def lazyDeltaProjReduction(t0: Expr, s0: Expr, sname: Name, idx: Int, eager: Boolean): Step[Boolean] =
    def loop(t: Expr, s: Expr): Step[Boolean] =
      Step.defer(lazyDeltaReductionStep(t, s, eager)).flatMap { (status, tn, sn) =>
        status match
          case ReductionStatus.Continue => Step.defer(loop(tn, sn))
          case ReductionStatus.DefEqual => Step.True
          case _ =>
            Step.defer(reduceProjCore(tn, sname, idx)).flatMap {
              case Some(a) =>
                Step.defer(reduceProjCore(sn, sname, idx)).flatMap {
                  case Some(b) => Step.defer(isDefEqCoreE(a, b, eager))
                  case None    => Step.defer(isDefEqCoreE(tn, sn, eager))
                }
              case None => Step.defer(isDefEqCoreE(tn, sn, eager))
            }
      }
    loop(t0, s0)

  /** `is_def_eq_core`. */
  private def isDefEqCoreE(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    defEqCalls += 1
    step()
    Step.defer(quickIsDefEq(t, s, eager)).flatMap {
      case Some(r) => Step.now(r)
      case None =>
        // Proofs by reflection: `decide` produces `Eq.refl true : decide p = true`.
        val reflection: Step[Boolean] =
          if (!t.hasFVar || eager) && Expr.isConstOf(s, Names.boolTrue) then
            Step.defer(whnfE(t)).map(w => Expr.isConstOf(w, Names.boolTrue))
          else Step.False
        reflection.flatMap { hit =>
          if hit then Step.True
          else
            for
              tn0 <- Step.defer(whnfCoreE(t, false, true))
              sn0 <- Step.defer(whnfCoreE(s, false, true))
              r <- {
                val changed = (tn0 ne t) || (sn0 ne s)
                val quick: Step[Option[Boolean]] =
                  if changed then Step.defer(quickIsDefEq(tn0, sn0, eager)) else Step.now(None)
                quick.flatMap {
                  case Some(q) => Step.now(q)
                  case None =>
                    Step.defer(isDefEqProofIrrel(tn0, sn0, eager)).flatMap {
                      case Some(pi) => Step.now(pi)
                      case None =>
                        Step.defer(lazyDeltaReduction(tn0, sn0, eager)).flatMap { (ld, tn, sn) =>
                          ld match
                            case Some(r) => Step.now(r)
                            case None    => Step.defer(isDefEqFinal(tn, sn, eager))
                        }
                    }
                }
              }
            yield r
        }
    }

  private def isDefEqFinal(tn: Expr, sn: Expr, eager: Boolean): Step[Boolean] =
    (tn, sn) match
      case (a: Expr.Const, b: Expr.Const) if a.name == b.name && isDefEqLevels(a.levels, b.levels) =>
        Step.True
      case (a: Expr.FVar, b: Expr.FVar) if a.id == b.id => Step.True
      case _ =>
        val projPath: Step[Boolean] = (tn, sn) match
          case (a: Expr.Proj, b: Expr.Proj) if a.typeName == b.typeName && a.idx == b.idx =>
            Step.defer(lazyDeltaProjReduction(a.struct, b.struct, a.typeName, a.idx, eager))
          case _ => Step.False
        projPath.flatMap { hit =>
          if hit then Step.True
          else
            for
              tnn <- Step.defer(whnfCoreE(tn, false, false))
              snn <- Step.defer(whnfCoreE(sn, false, false))
              r <-
                if (tnn ne tn) || (snn ne sn) then Step.defer(isDefEqCoreE(tnn, snn, eager))
                else
                  Step.defer(isDefEqApp(tn, sn, eager)).flatMap { ok =>
                    if ok then Step.True
                    else
                      Step.defer(tryEtaExpansion(tn, sn, eager)).flatMap { ok2 =>
                        if ok2 then Step.True
                        else
                          Step.defer(tryEtaStruct(tn, sn, eager)).flatMap { ok3 =>
                            if ok3 then Step.True
                            else
                              Step.defer(tryStringLitExpansion(tn, sn, eager)).flatMap {
                                case Some(r) => Step.now(r)
                                case None    => Step.defer(isDefEqUnitLike(tn, sn, eager))
                              }
                          }
                      }
                  }
            yield r
        }

  private def isDefEqE(t: Expr, s: Expr, eager: Boolean): Step[Boolean] =
    Step.defer(isDefEqCoreE(t, s, eager)).map { r
      =>
      if r then { if profile.cacheDefEqSuccess then cacheSuccess(t, s) }
      else recordFailure(t, s)
      r
    }

object TypeChecker:
  val defaultMaxSteps: Long = 1L << 32
  val maxTraceEntries: Int  = 32

  /** How often the clock is read, in reduction steps.
    *
    * It has to be below what an ordinary declaration costs, or the limit
    * cannot fire for one at all: the declarations of the committed nested
    * fixture take between 256 and 1024 steps each, so at 4096 the clock was
    * never read for any of them.
    */
  val defaultClockEvery: Long = 256L

  /** A wall-clock bound on checking one declaration.
    *
    * `maxSteps` bounds the work; this bounds the waiting, which is what a
    * caller with a deadline of its own can state. The two are independent:
    * whichever is reached first ends the declaration, and both report where
    * the reduction went.
    *
    * The clock is supplied rather than named here, because the kernel cross-
    * builds to three platforms and a test needs a clock it controls. It is
    * read every `every` steps rather than on each one: a step is a few
    * nanoseconds and reading a clock is of the same order, so sampling keeps
    * the guard off the hot path. The bound is therefore overshot by at most
    * what `every` steps cost.
    *
    * One instance can be shared by every declaration of a run. Each
    * `TypeChecker` reads the clock once when it is built, so the bound is per
    * declaration rather than for the run as a whole.
    */
  final class TimeLimit(val nanos: Long, val now: () => Long, val every: Long = defaultClockEvery):
    require(nanos > 0, "a time limit must be positive")
    require(every > 0, "a clock interval must be positive")

    private var startedAt: Long = Long.MinValue

    /** Starts the window, once. Every `TypeChecker` built from this instance
      * calls it, and the first call is the one that counts: a declaration
      * whose checking is spread over several checkers — an inductive block
      * builds more than twenty — gets one budget between them rather than one
      * each. The scope of a limit is therefore the scope of its instance,
      * which is why a caller takes a `fresh` one per declaration.
      */
    def begin(): Unit = if startedAt == Long.MinValue then startedAt = now()

    def exceeded: Boolean = startedAt != Long.MinValue && now() - startedAt >= nanos

    /** The same bound and clock, with its window not yet started. */
    def fresh(): TimeLimit = new TimeLimit(nanos, now, every)

  /** The largest bound `TimeLimit` can hold, in milliseconds.
    *
    * A caller states milliseconds and the kernel keeps nanoseconds, so a
    * larger number silently wraps: 18,446,744,073,710 ms came out as 0.45 ms.
    * Callers check against this rather than multiplying first.
    */
  val maxTimeMillis: Long = Long.MaxValue / 1000000L

  /** `g_dont_care`: placeholder for a binder whose variable does not occur. */
  private[kernel] val dontCare: Expr = Expr.const(Name.mkSimple("_dontCare"))
