package kolla.kernel

import cats.Eval
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
  * shared. All recursion runs in `cats.Eval`.
  */
final class TypeChecker(
    val env: Environment,
    val profile: KernelProfile = KernelProfile.default,
    val definitionSafety: DefinitionSafety = DefinitionSafety.Safe,
    initialLocalContext: LocalContext = LocalContext.empty,
    val maxSteps: Long = TypeChecker.defaultMaxSteps
):

  private val ngen = new NameGenerator()

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
  private var steps: Long = 0L

  /** The pairs `is_def_eq` rejected, most recent last. */
  def defeqTrace: List[String] = failedPairs.toList

  def localContext: LocalContext = lctx

  private def step(): Unit =
    steps += 1
    if steps > maxSteps then
      throw KernelException(
        ExceptionKind.DeepRecursion,
        s"exceeded $maxSteps reduction steps"
      )

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

  private def ensureSortE(e: Expr, s: Expr): Eval[Expr] =
    if e.isInstanceOf[Expr.Sort] then Eval.now(e)
    else
      Eval.defer(whnfE(e)).map {
        case r: Expr.Sort => r
        case _ =>
          throw new KernelException(
            ExceptionKind.TypeExpected, None, Pretty.expr(s), defeqTrace
          )
      }

  private def ensurePiE(e: Expr, s: Expr): Eval[Expr] =
    if e.isInstanceOf[Expr.ForallE] then Eval.now(e)
    else
      Eval.defer(whnfE(e)).map {
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
  private def isPropE(e: Expr): Eval[Boolean] =
    for
      t <- Eval.defer(inferTypeE(e, inferOnly = true))
      s <- Eval.defer(ensureSortE(t, t))
    yield
      val l = s.asInstanceOf[Expr.Sort].level
      if profile.propByNormalization then Level.normalizesToZero(l) else l.isZero

  // ----------------------------------------------------------------- inferType

  private def inferTypeE(e: Expr, inferOnly: Boolean): Eval[Expr] =
    if e.hasLooseBVars then
      fail(
        ExceptionKind.Other,
        "the type checker does not accept loose bound variables; replace them with free variables first"
      )
    step()
    val cache = if inferOnly then inferCacheOnly else inferCacheCheck
    cache.get(e) match
      case Some(r) => Eval.now(r)
      case None =>
        val computed: Eval[Expr] = e match
          case l: Expr.Lit     => Eval.now(inferLit(l))
          case m: Expr.MData   => Eval.defer(inferTypeE(m.expr, inferOnly))
          case p: Expr.Proj    => Eval.defer(inferProj(p, inferOnly))
          case f: Expr.FVar    => Eval.now(inferFVar(f))
          case _: Expr.MVar    => fail(ExceptionKind.DeclarationHasMetavars, "metavariables are not supported")
          case _: Expr.BVar    => fail(ExceptionKind.Other, "unexpected bound variable")
          case s: Expr.Sort =>
            if !inferOnly then checkLevel(s.level)
            Eval.now(Expr.Sort(Level.Succ(s.level)))
          case c: Expr.Const   => Eval.now(inferConstant(c, inferOnly))
          case l: Expr.Lam     => Eval.defer(inferLambda(l, inferOnly))
          case p: Expr.ForallE => Eval.defer(inferPi(p, inferOnly))
          case a: Expr.App     => Eval.defer(inferApp(a, inferOnly))
          case l: Expr.LetE    => Eval.defer(inferLet(l, inferOnly))
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

  private def inferLambda(e0: Expr.Lam, inferOnly: Boolean): Eval[Expr] =
    val fvars = mutable.ArrayBuffer.empty[Expr]
    def loop(e: Expr): Eval[Expr] = e match
      case l: Expr.Lam =>
        val d = ExprOps.instantiateRev(l.binderType, fvars.toIndexedSeq)
        val checked =
          if inferOnly then Eval.Unit
          else Eval.defer(inferTypeE(d, inferOnly)).flatMap(t => Eval.defer(ensureSortE(t, d))).map(_ => ())
        checked.flatMap { _ =>
          val (next, fvar) = lctx.mkLocalDecl(ngen, l.binderName, d, l.binderInfo)
          lctx = next
          fvars += fvar
          Eval.defer(loop(l.body))
        }
      case other =>
        Eval.defer(inferTypeE(ExprOps.instantiateRev(other, fvars.toIndexedSeq), inferOnly))
    // `infer_lambda` returns `mk_pi`: the type of a lambda is a Pi.
    loop(e0).map(r => lctx.mkPi(fvars.toIndexedSeq, ExprOps.cheapBetaReduce(r)))

  private def inferPi(e0: Expr.ForallE, inferOnly: Boolean): Eval[Expr] =
    val fvars = mutable.ArrayBuffer.empty[Expr]
    val us    = mutable.ArrayBuffer.empty[Level]
    def loop(e: Expr): Eval[Expr] = e match
      case p: Expr.ForallE =>
        val d = ExprOps.instantiateRev(p.binderType, fvars.toIndexedSeq)
        for
          t1 <- Eval.defer(inferTypeE(d, inferOnly))
          s1 <- Eval.defer(ensureSortE(t1, d))
          r <- {
            us += s1.asInstanceOf[Expr.Sort].level
            val (next, fvar) = lctx.mkLocalDecl(ngen, p.binderName, d, p.binderInfo)
            lctx = next
            fvars += fvar
            Eval.defer(loop(p.body))
          }
        yield r
      case other =>
        val body = ExprOps.instantiateRev(other, fvars.toIndexedSeq)
        for
          t <- Eval.defer(inferTypeE(body, inferOnly))
          s <- Eval.defer(ensureSortE(t, body))
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

  private def inferApp(e: Expr.App, inferOnly: Boolean): Eval[Expr] =
    if !inferOnly then
      for
        ft0    <- Eval.defer(inferTypeE(e.fn, inferOnly))
        fType  <- Eval.defer(ensurePiE(ft0, e))
        aType  <- Eval.defer(inferTypeE(e.arg, inferOnly))
        dType   = fType.asInstanceOf[Expr.ForallE].binderType
        ok     <- Eval.defer(isDefEqE(aType, dType, eager = isEagerReduce(e.arg)))
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
      Eval.defer(inferTypeE(f, true)).flatMap { ft0 =>
        def loop(i: Int, j: Int, fType: Expr): Eval[Expr] =
          if i >= args.length then Eval.now(ExprOps.instantiateRev(fType, args.slice(j, args.length)))
          else
            fType match
              case p: Expr.ForallE => Eval.defer(loop(i + 1, j, p.body))
              case _ =>
                val t = ExprOps.instantiateRev(fType, args.slice(j, i))
                Eval.defer(ensurePiE(t, e)).flatMap { p =>
                  Eval.defer(loop(i + 1, i, p.asInstanceOf[Expr.ForallE].body))
                }
        loop(0, 0, ft0)
      }

  private def inferLet(e0: Expr.LetE, inferOnly: Boolean): Eval[Expr] =
    val fvars = mutable.ArrayBuffer.empty[Expr]
    def loop(e: Expr): Eval[Expr] = e match
      case l: Expr.LetE =>
        val tpe = ExprOps.instantiateRev(l.tpe, fvars.toIndexedSeq)
        val v   = ExprOps.instantiateRev(l.value, fvars.toIndexedSeq)
        val checked: Eval[Unit] =
          if inferOnly then Eval.Unit
          else
            for
              tt <- Eval.defer(inferTypeE(tpe, inferOnly))
              _  <- Eval.defer(ensureSortE(tt, tpe))
              vt <- Eval.defer(inferTypeE(v, inferOnly))
              ok <- Eval.defer(isDefEqE(vt, tpe, eager = false))
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
          Eval.defer(loop(l.body))
        }
      case other =>
        Eval.defer(inferTypeE(ExprOps.instantiateRev(other, fvars.toIndexedSeq), inferOnly))
    loop(e0).map(r => lctx.mkPi(fvars.toIndexedSeq, ExprOps.cheapBetaReduce(r), removeDeadLet = true))

  private def projIdx(p: Expr.Proj): Int =
    if profile.boundedProjIdx && p.idx < 0 then
      throw new KernelException(ExceptionKind.InvalidProj, None, Pretty.expr(p), defeqTrace)
    p.idx

  private def inferProj(p: Expr.Proj, inferOnly: Boolean): Eval[Expr] =
    def invalid: Nothing =
      throw new KernelException(ExceptionKind.InvalidProj, None, Pretty.expr(p), defeqTrace)
    for
      t0   <- Eval.defer(inferTypeE(p.struct, inferOnly))
      tpe  <- Eval.defer(whnfE(t0))
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
      prop <- Eval.defer(isPropE(tpe))
      res  <- {
        val idx = projIdx(p)
        def params(i: Int, r: Expr): Eval[Expr] =
          if i >= iVal.numParams then Eval.now(r)
          else
            Eval.defer(whnfE(r)).flatMap {
              case pi: Expr.ForallE => Eval.defer(params(i + 1, ExprOps.instantiate1(pi.body, args(i))))
              case _                => invalid
            }
        def fields(i: Int, r: Expr): Eval[Expr] =
          if i >= idx then Eval.now(r)
          else
            Eval.defer(whnfE(r)).flatMap {
              case pi: Expr.ForallE =>
                if ExprOps.hasLooseBVar(pi.body, 0) then
                  val dom = pi.binderType
                  Eval.defer(if prop then isPropE(dom) else Eval.True).flatMap { domProp =>
                    if prop && !domProp then invalid
                    else
                      Eval.defer(
                        fields(i + 1, ExprOps.instantiate1(pi.body, Expr.Proj(iName, i, p.struct)))
                      )
                  }
                else Eval.defer(fields(i + 1, pi.body))
              case _ => invalid
            }
        for
          afterParams <- params(0, r0)
          afterFields <- fields(0, afterParams)
          last        <- Eval.defer(whnfE(afterFields))
          dom = last match
                  case pi: Expr.ForallE => pi.binderType
                  case _                => invalid
          domProp <- Eval.defer(if prop then isPropE(dom) else Eval.True)
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
        if c.levels.nonEmpty then
          unfoldCache.get(c) match
            case Some(r) => r
            case None =>
              val r = ExprOps.instantiateValueLevelParams(d, c.levels)
              unfoldCache(c) = r
              r
        else ExprOps.instantiateValueLevelParams(d, c.levels)
      }
    case _ => None

  /** `unfold_definition`: unfolds the head of an application. */
  def unfoldDefinition(e: Expr): Option[Expr] = e match
    case _: Expr.App =>
      unfoldDefinitionCore(Expr.getAppFn(e)).map(f => Expr.mkAppN(f, Expr.getAppArgs(e)))
    case _ => unfoldDefinitionCore(e)

  /** `reduce_proj_core`. */
  private def reduceProjCore(c0: Expr, sname: Name, idx: Int): Eval[Option[Expr]] =
    val prepared: Eval[Expr] = c0 match
      case l: Expr.Lit =>
        l.value match
          case Literal.StrVal(v) => Eval.defer(whnfE(ExprOps.stringLitToConstructor(v, profile)))
          case _                 => Eval.now(c0)
      case _ => Eval.now(c0)
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

  private def reduceProj(p: Expr.Proj, cheapRec: Boolean, cheapProj: Boolean): Eval[Option[Expr]] =
    val idx = projIdx(p)
    val c =
      if cheapProj then Eval.defer(whnfCoreE(p.struct, cheapRec, cheapProj))
      else Eval.defer(whnfE(p.struct))
    c.flatMap(cv => Eval.defer(reduceProjCore(cv, p.typeName, idx)))

  /** `quot_reduce_rec`. */
  private def quotReduceRec(e: Expr): Eval[Option[Expr]] =
    Expr.constName(Expr.getAppFn(e)) match
      case Some(n) if n == Names.quotLift || n == Names.quotInd =>
        val mkPos  = if n == Names.quotLift then 5 else 4
        val argPos = 3
        val args   = Expr.getAppArgs(e)
        if args.length <= mkPos then Eval.now(None)
        else
          Eval.defer(whnfE(args(mkPos))).map { mk =>
            if !Expr.isConstOf(Expr.getAppFn(mk), Names.quotMk) || Expr.getAppNumArgs(mk) != 3 then None
            else
              val f = args(argPos)
              var r: Expr = Expr.App(f, Expr.getAppArgs(mk).last)
              val elimArity = mkPos + 1
              if args.length > elimArity then r = Expr.mkAppRange(r, args, elimArity, args.length)
              Some(r)
          }
      case _ => Eval.now(None)

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
  private def toCtorWhenStructure(inductName: Name, e: Expr): Eval[Expr] =
    if !isNonRecStructure(inductName) || isCtorApp(e) then Eval.now(e)
    else
      Eval.defer(inferTypeE(e, inferOnly = true)).flatMap(t => Eval.defer(whnfE(t))).flatMap { eType =>
        if !Expr.isConstOf(Expr.getAppFn(eType), inductName) then Eval.now(e)
        else
          Eval.defer(isPropE(eType)).map { p =>
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
  private def toCtorWhenK(rval: RecursorVal, e: Expr): Eval[Expr] =
    for
      t0      <- Eval.defer(inferTypeE(e, inferOnly = true))
      appType <- Eval.defer(whnfE(t0))
      r <-
        if !Expr.isConstOf(Expr.getAppFn(appType), rval.majorInduct) then Eval.now(e)
        else
          mkNullaryCtor(appType, rval.numParams) match
            case None => Eval.now(e)
            case Some(newCtorApp) =>
              for
                newType <- Eval.defer(inferTypeE(newCtorApp, inferOnly = true))
                ok      <- Eval.defer(isDefEqE(appType, newType, eager = false))
              yield if ok then newCtorApp else e
    yield r

  private def recRuleFor(rval: RecursorVal, major: Expr): Option[RecursorRule] =
    Expr.constName(Expr.getAppFn(major)).flatMap(n => rval.rules.find(_.ctor == n))

  /** `inductive_reduce_rec`: iota reduction. */
  private def inductiveReduceRec(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Eval[Option[Expr]] =
    val recFn = Expr.getAppFn(e)
    Expr.constName(recFn).flatMap(env.find) match
      case Some(ConstantInfo.RecInfo(rval)) =>
        val recArgs  = Expr.getAppArgs(e)
        val majorIdx = rval.majorIdx
        if majorIdx >= recArgs.length then Eval.now(None)
        else
          val reduceMajor: Expr => Eval[Expr] =
            if cheapRec then x => whnfCoreE(x, cheapRec, cheapProj) else x => whnfE(x)
          val major0 = recArgs(majorIdx)
          for
            afterK <- if rval.k then Eval.defer(toCtorWhenK(rval, major0)) else Eval.now(major0)
            w      <- Eval.defer(reduceMajor(afterK))
            major <- w match
                       case l: Expr.Lit =>
                         l.value match
                           case Literal.NatVal(v) => Eval.now(ExprOps.natLitToConstructor(v))
                           case Literal.StrVal(v) =>
                             Eval.defer(whnfE(ExprOps.stringLitToConstructor(v, profile)))
                       case other => Eval.defer(toCtorWhenStructure(rval.majorInduct, other))
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
      case _ => Eval.now(None)

  private def reduceRecursor(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Eval[Option[Expr]] =
    val quot: Eval[Option[Expr]] =
      if env.quotInitialized then Eval.defer(quotReduceRec(e)) else Eval.now(None)
    quot.flatMap {
      case Some(r) => Eval.now(Some(r))
      case None    => Eval.defer(inductiveReduceRec(e, cheapRec, cheapProj))
    }

  private def whnfFVar(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Eval[Expr] =
    lctx.find(e).flatMap(_.value) match
      case Some(v) => Eval.defer(whnfCoreE(v, cheapRec, cheapProj)) // zeta
      case None    => Eval.now(e)

  /** `whnf_core`: every reduction except delta and the normalizer extensions. */
  private def whnfCoreE(e: Expr, cheapRec: Boolean, cheapProj: Boolean): Eval[Expr] =
    step()
    e match
      case _: Expr.BVar | _: Expr.Sort | _: Expr.MVar | _: Expr.ForallE | _: Expr.Const | _: Expr.Lam |
          _: Expr.Lit =>
        Eval.now(e)
      case m: Expr.MData => Eval.defer(whnfCoreE(m.expr, cheapRec, cheapProj))
      case f: Expr.FVar =>
        if lctx.isLetFVar(f) then Eval.defer(whnfFVar(f, cheapRec, cheapProj)) else Eval.now(e)
      case _ =>
        val cacheable = !cheapRec && !cheapProj
        if cacheable then
          whnfCoreCache.get(e) match
            case Some(r) => return Eval.now(r)
            case None    => ()
        val computed: Eval[Expr] = e match
          case p: Expr.Proj =>
            Eval.defer(reduceProj(p, cheapRec, cheapProj)).flatMap {
              case Some(m) => Eval.defer(whnfCoreE(m, cheapRec, cheapProj))
              case None    => Eval.now(e)
            }
          case a: Expr.App =>
            val args = Expr.getAppArgs(a)
            val f0   = Expr.getAppFn(a)
            Eval.defer(whnfCoreE(f0, cheapRec, cheapProj)).flatMap { f =>
              if f.isInstanceOf[Expr.Lam] then
                Eval.defer(whnfCoreE(ExprOps.betaReduce(f, args), cheapRec, cheapProj))
              else if f == f0 then
                Eval.defer(reduceRecursor(a, cheapRec, cheapProj)).flatMap {
                  case Some(r) => Eval.defer(whnfCoreE(r, cheapRec, cheapProj))
                  case None    => Eval.now(e)
                }
              else Eval.defer(whnfCoreE(Expr.mkAppN(f, args), cheapRec, cheapProj))
            }
          case l: Expr.LetE =>
            Eval.defer(whnfCoreE(ExprOps.instantiate1(l.body, l.value), cheapRec, cheapProj))
          case other => Eval.now(other)
        computed.map { r =>
          if cacheable then whnfCoreCache(e) = r
          r
        }

  /** `whnf`. */
  private def whnfE(e: Expr): Eval[Expr] =
    e match
      case _: Expr.BVar | _: Expr.Sort | _: Expr.MVar | _: Expr.ForallE | _: Expr.Lit => Eval.now(e)
      case m: Expr.MData => Eval.defer(whnfE(m.expr))
      case f: Expr.FVar if !lctx.isLetFVar(f) => Eval.now(e)
      case _ =>
        whnfCache.get(e) match
          case Some(r) => Eval.now(r)
          case None =>
            def loop(t: Expr): Eval[Expr] =
              Eval.defer(whnfCoreE(t, false, false)).flatMap { t1 =>
                Eval.defer(reduceNat(t1)).flatMap {
                  case Some(v) => Eval.now(v)
                  case None =>
                    unfoldDefinition(t1) match
                      case Some(next) => Eval.defer(loop(next))
                      case None       => Eval.now(t1)
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

  private def binNatArgs(e: Expr): Eval[Option[(BigInt, BigInt)]] =
    val fn = e.asInstanceOf[Expr.App]
    for
      a1 <- Eval.defer(whnfE(fn.fn.asInstanceOf[Expr.App].arg))
      r <-
        if !isNatLitExt(a1) then Eval.now(None)
        else
          Eval.defer(whnfE(fn.arg)).map { a2 =>
            if !isNatLitExt(a2) then None else Some((natVal(a1), natVal(a2)))
          }
    yield r

  private def binNatOp(e: Expr, checkSize: Boolean)(f: (BigInt, BigInt) => BigInt): Eval[Option[Expr]] =
    binNatArgs(e).map {
      case None => None
      case Some((v1, v2)) =>
        val r = f(v1, v2)
        if checkSize then checkNatSize(natSizeInBytes(r))
        Some(Expr.natLit(r))
    }

  private def binNatPred(e: Expr)(f: (BigInt, BigInt) => Boolean): Eval[Option[Expr]] =
    binNatArgs(e).map {
      case None           => None
      case Some((v1, v2)) => Some(Expr.const(if f(v1, v2) then Names.boolTrue else Names.boolFalse))
    }

  private def reducePow(e: Expr): Eval[Option[Expr]] =
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

  private def reduceShiftLeft(e: Expr): Eval[Option[Expr]] =
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
  private def reduceNat(e: Expr): Eval[Option[Expr]] =
    val nargs = Expr.getAppNumArgs(e)
    if nargs == 1 then
      val a = e.asInstanceOf[Expr.App]
      if Expr.isConstOf(a.fn, Names.natSucc) then
        Eval.defer(whnfE(a.arg)).map { arg =>
          if !isNatLitExt(arg) then None
          else
            val v = natVal(arg) + 1
            checkNatSize(natSizeInBytes(v))
            Some(Expr.natLit(v))
        }
      else Eval.now(None)
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
        case _ => Eval.now(None)
    else Eval.now(None)

  // ------------------------------------------------------------- is_def_eq

  private def cacheSuccess(t: Expr, s: Expr): Unit = successCache.add(new ExprPair(t, s))
  private def succeededBefore(t: Expr, s: Expr): Boolean =
    profile.cacheDefEqSuccess && successCache.contains(new ExprPair(t, s))
  private def cacheFailure(t: Expr, s: Expr): Unit = failureCache.add(new ExprPair(t, s))
  private def failedBefore(t: Expr, s: Expr): Boolean = failureCache.contains(new ExprPair(t, s))

  private def isDefEqLevels(ls1: List[Level], ls2: List[Level]): Boolean =
    ls1.length == ls2.length && ls1.corresponds(ls2)(Level.isEquiv)

  /** `is_def_eq_binding`. */
  private def isDefEqBinding(t0: Expr, s0: Expr, eager: Boolean): Eval[Boolean] =
    val subst = mutable.ArrayBuffer.empty[Expr]
    def loop(t: Expr, s: Expr): Eval[Boolean] =
      val (td, tb, sd, sb, bn, bi) = (t, s) match
        case (a: Expr.Lam, b: Expr.Lam) =>
          (a.binderType, a.body, b.binderType, b.body, b.binderName, b.binderInfo)
        case (a: Expr.ForallE, b: Expr.ForallE) =>
          (a.binderType, a.body, b.binderType, b.body, b.binderName, b.binderInfo)
        case _ => return Eval.defer(
            isDefEqE(
              ExprOps.instantiateRev(t, subst.toIndexedSeq),
              ExprOps.instantiateRev(s, subst.toIndexedSeq),
              eager
            )
          )
      val domainsEqual: Eval[Boolean] =
        if td == sd then Eval.True
        else
          val vs = ExprOps.instantiateRev(sd, subst.toIndexedSeq)
          val vt = ExprOps.instantiateRev(td, subst.toIndexedSeq)
          Eval.defer(isDefEqE(vt, vs, eager))
      domainsEqual.flatMap { ok =>
        if !ok then Eval.False
        else
          if tb.hasLooseBVars || sb.hasLooseBVars then
            val vs           = ExprOps.instantiateRev(sd, subst.toIndexedSeq)
            val (next, fvar) = lctx.mkLocalDecl(ngen, bn, vs, bi)
            lctx = next
            subst += fvar
          else subst += TypeChecker.dontCare
          if tb.getClass == t.getClass && sb.getClass == s.getClass then Eval.defer(loop(tb, sb))
          else
            Eval.defer(
              isDefEqE(
                ExprOps.instantiateRev(tb, subst.toIndexedSeq),
                ExprOps.instantiateRev(sb, subst.toIndexedSeq),
                eager
              )
            )
      }
    loop(t0, s0)

  /** `quick_is_def_eq`: `None` means "not an easy case". */
  private def quickIsDefEq(t: Expr, s: Expr, eager: Boolean): Eval[Option[Boolean]] =
    if t == s || succeededBefore(t, s) then Eval.now(Some(true))
    else if t.kindOrd == s.kindOrd then
      (t, s) match
        case (_: Expr.Lam, _: Expr.Lam) | (_: Expr.ForallE, _: Expr.ForallE) =>
          Eval.defer(isDefEqBinding(t, s, eager)).map(Some(_))
        case (a: Expr.Sort, b: Expr.Sort) => Eval.now(Some(Level.isEquiv(a.level, b.level)))
        case (a: Expr.MData, b: Expr.MData) => Eval.defer(isDefEqE(a.expr, b.expr, eager)).map(Some(_))
        case (a: Expr.Lit, b: Expr.Lit)   => Eval.now(Some(a.value == b.value))
        case _                            => Eval.now(None)
    else Eval.now(None)

  /** `is_def_eq_args`. */
  private def isDefEqArgs(t0: Expr, s0: Expr, eager: Boolean): Eval[Boolean] =
    def loop(t: Expr, s: Expr): Eval[Boolean] = (t, s) match
      case (a: Expr.App, b: Expr.App) =>
        Eval.defer(isDefEqE(a.arg, b.arg, eager)).flatMap { ok =>
          if !ok then Eval.False else Eval.defer(loop(a.fn, b.fn))
        }
      case _ => Eval.now(!t.isInstanceOf[Expr.App] && !s.isInstanceOf[Expr.App])
    loop(t0, s0)

  /** `try_eta_expansion_core`. */
  private def tryEtaExpansionCore(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    if t.isInstanceOf[Expr.Lam] && !s.isInstanceOf[Expr.Lam] then
      for
        st0 <- Eval.defer(inferTypeE(s, inferOnly = true))
        st  <- Eval.defer(whnfE(st0))
        r <- st match
               case pi: Expr.ForallE =>
                 val newS = Expr.Lam(pi.binderName, pi.binderType, Expr.App(s, Expr.BVar(0)), pi.binderInfo)
                 Eval.defer(isDefEqE(t, newS, eager))
               case _ => Eval.False
      yield r
    else Eval.False

  private def tryEtaExpansion(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    Eval.defer(tryEtaExpansionCore(t, s, eager)).flatMap { ok =>
      if ok then Eval.True else Eval.defer(tryEtaExpansionCore(s, t, eager))
    }

  /** `try_eta_struct_core`: is `s` of the form `mk t.1 ... t.n`? */
  private def tryEtaStructCore(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    Expr.constName(Expr.getAppFn(s)).flatMap(env.find) match
      case Some(ConstantInfo.CtorInfo(fv)) =>
        if Expr.getAppNumArgs(s) != fv.numParams + fv.numFields then Eval.False
        else if !isNonRecStructure(fv.induct) then Eval.False
        else
          for
            tt <- Eval.defer(inferTypeE(t, inferOnly = true))
            st <- Eval.defer(inferTypeE(s, inferOnly = true))
            ok <- Eval.defer(isDefEqE(tt, st, eager))
            r <-
              if !ok then Eval.False
              else
                val sArgs = Expr.getAppArgs(s)
                def loop(i: Int): Eval[Boolean] =
                  if i >= sArgs.length then Eval.True
                  else
                    val proj = Expr.Proj(fv.induct, i - fv.numParams, t)
                    Eval.defer(isDefEqE(proj, sArgs(i), eager)).flatMap { o =>
                      if !o then Eval.False else Eval.defer(loop(i + 1))
                    }
                loop(fv.numParams)
          yield r
      case _ => Eval.False

  private def tryEtaStruct(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    Eval.defer(tryEtaStructCore(t, s, eager)).flatMap { ok =>
      if ok then Eval.True else Eval.defer(tryEtaStructCore(s, t, eager))
    }

  /** `is_def_eq_app`. */
  private def isDefEqApp(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    if t.isInstanceOf[Expr.App] && s.isInstanceOf[Expr.App] then
      val tArgs = Expr.getAppArgs(t)
      val sArgs = Expr.getAppArgs(s)
      if tArgs.length != sArgs.length then Eval.False
      else
        Eval.defer(isDefEqE(Expr.getAppFn(t), Expr.getAppFn(s), eager)).flatMap { ok =>
          if !ok then Eval.False
          else
            def loop(i: Int): Eval[Boolean] =
              if i >= tArgs.length then Eval.True
              else
                Eval.defer(isDefEqE(tArgs(i), sArgs(i), eager)).flatMap { o =>
                  if !o then Eval.False else Eval.defer(loop(i + 1))
                }
            loop(0)
        }
    else Eval.False

  /** `is_def_eq_proof_irrel`. */
  private def isDefEqProofIrrel(t: Expr, s: Expr, eager: Boolean): Eval[Option[Boolean]] =
    for
      tType <- Eval.defer(inferTypeE(t, inferOnly = true))
      p     <- Eval.defer(isPropE(tType))
      r <-
        if !p then Eval.now(None)
        else
          for
            sType <- Eval.defer(inferTypeE(s, inferOnly = true))
            ok    <- Eval.defer(isDefEqE(tType, sType, eager))
          yield Some(ok)
    yield r

  /** `is_def_eq_unit_like`. */
  private def isDefEqUnitLike(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    for
      t0    <- Eval.defer(inferTypeE(t, inferOnly = true))
      tType <- Eval.defer(whnfE(t0))
      r <- Expr.constName(Expr.getAppFn(tType)) match
             case Some(i) if isNonRecStructure(i) =>
               val ctorName = env.get(i).asInstanceOf[ConstantInfo.InductInfo].value.ctors.head
               val ctorVal  = env.get(ctorName).asInstanceOf[ConstantInfo.CtorInfo].value
               if ctorVal.numFields != 0 then Eval.False
               else
                 Eval.defer(inferTypeE(s, inferOnly = true)).flatMap(st =>
                   Eval.defer(isDefEqE(tType, st, eager))
                 )
             case _ => Eval.False
    yield r

  /** `try_string_lit_expansion_core`. */
  private def tryStringLitExpansionCore(t: Expr, s: Expr, eager: Boolean): Eval[Option[Boolean]] =
    t match
      case l: Expr.Lit =>
        l.value match
          case Literal.StrVal(v)
              if s.isInstanceOf[Expr.App] &&
                Expr.isConstOf(s.asInstanceOf[Expr.App].fn, profile.stringLiteralCtor) =>
            Eval
              .defer(whnfE(ExprOps.stringLitToConstructor(v, profile)))
              .flatMap(x => Eval.defer(isDefEqE(x, s, eager)))
              .map(Some(_))
          case _ => Eval.now(None)
      case _ => Eval.now(None)

  private def tryStringLitExpansion(t: Expr, s: Expr, eager: Boolean): Eval[Option[Boolean]] =
    Eval.defer(tryStringLitExpansionCore(t, s, eager)).flatMap {
      case Some(r) => Eval.now(Some(r))
      case None    => Eval.defer(tryStringLitExpansionCore(s, t, eager))
    }

  private def tryUnfoldProjApp(e: Expr): Eval[Option[Expr]] =
    if Expr.getAppFn(e).isInstanceOf[Expr.Proj] then
      Eval.defer(whnfCoreE(e, false, false)).map(n => if n != e then Some(n) else None)
    else Eval.now(None)

  private enum ReductionStatus:
    case Continue, DefUnknown, DefEqual, DefDiff

  /** `lazy_delta_reduction_step`. */
  private def lazyDeltaReductionStep(t: Expr, s: Expr, eager: Boolean): Eval[(ReductionStatus, Expr, Expr)] =
    val dt = isDelta(t)
    val ds = isDelta(s)
    val stepped: Eval[(Expr, Expr)] =
      (dt, ds) match
        case (None, None) => return Eval.now((ReductionStatus.DefUnknown, t, s))
        case (Some(_), None) =>
          Eval.defer(tryUnfoldProjApp(s)).flatMap {
            case Some(sNew) => Eval.now((t, sNew))
            case None =>
              Eval.defer(whnfCoreE(unfoldDefinition(t).get, false, true)).map(tn => (tn, s))
          }
        case (None, Some(_)) =>
          Eval.defer(tryUnfoldProjApp(t)).flatMap {
            case Some(tNew) => Eval.now((tNew, s))
            case None =>
              Eval.defer(whnfCoreE(unfoldDefinition(s).get, false, true)).map(sn => (t, sn))
          }
        case (Some(a), Some(b)) =>
          val c = ReducibilityHints.compare(a.hints, b.hints)
          if c < 0 then Eval.defer(whnfCoreE(unfoldDefinition(t).get, false, true)).map(tn => (tn, s))
          else if c > 0 then Eval.defer(whnfCoreE(unfoldDefinition(s).get, false, true)).map(sn => (t, sn))
          else
            val sameAndRegular =
              t.isInstanceOf[Expr.App] && s.isInstanceOf[Expr.App] && a.name == b.name && a.hints.isRegular
            val shortcut: Eval[Boolean] =
              if sameAndRegular && !failedBefore(t, s) then
                val tl = Expr.getAppFn(t).asInstanceOf[Expr.Const].levels
                val sl = Expr.getAppFn(s).asInstanceOf[Expr.Const].levels
                if isDefEqLevels(tl, sl) then
                  Eval.defer(isDefEqArgs(t, s, eager)).map { ok =>
                    if !ok then cacheFailure(t, s)
                    ok
                  }
                else { cacheFailure(t, s); Eval.False }
              else Eval.False
            shortcut.flatMap { hit =>
              if hit then return Eval.now((ReductionStatus.DefEqual, t, s))
              for
                tn <- Eval.defer(whnfCoreE(unfoldDefinition(t).get, false, true))
                sn <- Eval.defer(whnfCoreE(unfoldDefinition(s).get, false, true))
              yield (tn, sn)
            }
    stepped.flatMap { (tn, sn) =>
      Eval.defer(quickIsDefEq(tn, sn, eager)).map {
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
  private def isDefEqOffset(t: Expr, s: Expr, eager: Boolean): Eval[Option[Boolean]] =
    if isNatZero(t) && isNatZero(s) then Eval.now(Some(true))
    else
      (isNatSucc(t), isNatSucc(s)) match
        case (Some(pt), Some(ps)) => Eval.defer(isDefEqCoreE(pt, ps, eager)).map(Some(_))
        case _                    => Eval.now(None)

  /** `lazy_delta_reduction`. */
  private def lazyDeltaReduction(t0: Expr, s0: Expr, eager: Boolean): Eval[(Option[Boolean], Expr, Expr)] =
    def loop(t: Expr, s: Expr): Eval[(Option[Boolean], Expr, Expr)] =
      Eval.defer(isDefEqOffset(t, s, eager)).flatMap {
        case Some(r) => Eval.now((Some(r), t, s))
        case None =>
          val natPath: Eval[Option[Boolean]] =
            if (!t.hasFVar && !s.hasFVar) || eager then
              Eval.defer(reduceNat(t)).flatMap {
                case Some(tv) => Eval.defer(isDefEqCoreE(tv, s, eager)).map(Some(_))
                case None =>
                  Eval.defer(reduceNat(s)).flatMap {
                    case Some(sv) => Eval.defer(isDefEqCoreE(t, sv, eager)).map(Some(_))
                    case None     => Eval.now(None)
                  }
              }
            else Eval.now(None)
          natPath.flatMap {
            case Some(r) => Eval.now((Some(r), t, s))
            case None =>
              Eval.defer(lazyDeltaReductionStep(t, s, eager)).flatMap { (status, tn, sn) =>
                status match
                  case ReductionStatus.Continue   => Eval.defer(loop(tn, sn))
                  case ReductionStatus.DefUnknown => Eval.now((None, tn, sn))
                  case ReductionStatus.DefEqual   => Eval.now((Some(true), tn, sn))
                  case ReductionStatus.DefDiff    => Eval.now((Some(false), tn, sn))
              }
          }
      }
    loop(t0, s0)

  /** `lazy_delta_proj_reduction`. */
  private def lazyDeltaProjReduction(t0: Expr, s0: Expr, sname: Name, idx: Int, eager: Boolean): Eval[Boolean] =
    def loop(t: Expr, s: Expr): Eval[Boolean] =
      Eval.defer(lazyDeltaReductionStep(t, s, eager)).flatMap { (status, tn, sn) =>
        status match
          case ReductionStatus.Continue => Eval.defer(loop(tn, sn))
          case ReductionStatus.DefEqual => Eval.True
          case _ =>
            Eval.defer(reduceProjCore(tn, sname, idx)).flatMap {
              case Some(a) =>
                Eval.defer(reduceProjCore(sn, sname, idx)).flatMap {
                  case Some(b) => Eval.defer(isDefEqCoreE(a, b, eager))
                  case None    => Eval.defer(isDefEqCoreE(tn, sn, eager))
                }
              case None => Eval.defer(isDefEqCoreE(tn, sn, eager))
            }
      }
    loop(t0, s0)

  /** `is_def_eq_core`. */
  private def isDefEqCoreE(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    step()
    Eval.defer(quickIsDefEq(t, s, eager)).flatMap {
      case Some(r) => Eval.now(r)
      case None =>
        // Proofs by reflection: `decide` produces `Eq.refl true : decide p = true`.
        val reflection: Eval[Boolean] =
          if (!t.hasFVar || eager) && Expr.isConstOf(s, Names.boolTrue) then
            Eval.defer(whnfE(t)).map(w => Expr.isConstOf(w, Names.boolTrue))
          else Eval.False
        reflection.flatMap { hit =>
          if hit then Eval.True
          else
            for
              tn0 <- Eval.defer(whnfCoreE(t, false, true))
              sn0 <- Eval.defer(whnfCoreE(s, false, true))
              r <- {
                val changed = (tn0 ne t) || (sn0 ne s)
                val quick: Eval[Option[Boolean]] =
                  if changed then Eval.defer(quickIsDefEq(tn0, sn0, eager)) else Eval.now(None)
                quick.flatMap {
                  case Some(q) => Eval.now(q)
                  case None =>
                    Eval.defer(isDefEqProofIrrel(tn0, sn0, eager)).flatMap {
                      case Some(pi) => Eval.now(pi)
                      case None =>
                        Eval.defer(lazyDeltaReduction(tn0, sn0, eager)).flatMap { (ld, tn, sn) =>
                          ld match
                            case Some(r) => Eval.now(r)
                            case None    => Eval.defer(isDefEqFinal(tn, sn, eager))
                        }
                    }
                }
              }
            yield r
        }
    }

  private def isDefEqFinal(tn: Expr, sn: Expr, eager: Boolean): Eval[Boolean] =
    (tn, sn) match
      case (a: Expr.Const, b: Expr.Const) if a.name == b.name && isDefEqLevels(a.levels, b.levels) =>
        Eval.True
      case (a: Expr.FVar, b: Expr.FVar) if a.id == b.id => Eval.True
      case _ =>
        val projPath: Eval[Boolean] = (tn, sn) match
          case (a: Expr.Proj, b: Expr.Proj) if a.typeName == b.typeName && a.idx == b.idx =>
            Eval.defer(lazyDeltaProjReduction(a.struct, b.struct, a.typeName, a.idx, eager))
          case _ => Eval.False
        projPath.flatMap { hit =>
          if hit then Eval.True
          else
            for
              tnn <- Eval.defer(whnfCoreE(tn, false, false))
              snn <- Eval.defer(whnfCoreE(sn, false, false))
              r <-
                if (tnn ne tn) || (snn ne sn) then Eval.defer(isDefEqCoreE(tnn, snn, eager))
                else
                  Eval.defer(isDefEqApp(tn, sn, eager)).flatMap { ok =>
                    if ok then Eval.True
                    else
                      Eval.defer(tryEtaExpansion(tn, sn, eager)).flatMap { ok2 =>
                        if ok2 then Eval.True
                        else
                          Eval.defer(tryEtaStruct(tn, sn, eager)).flatMap { ok3 =>
                            if ok3 then Eval.True
                            else
                              Eval.defer(tryStringLitExpansion(tn, sn, eager)).flatMap {
                                case Some(r) => Eval.now(r)
                                case None    => Eval.defer(isDefEqUnitLike(tn, sn, eager))
                              }
                          }
                      }
                  }
            yield r
        }

  private def isDefEqE(t: Expr, s: Expr, eager: Boolean): Eval[Boolean] =
    Eval.defer(isDefEqCoreE(t, s, eager)).map { r
      =>
      if r then { if profile.cacheDefEqSuccess then cacheSuccess(t, s) }
      else recordFailure(t, s)
      r
    }

object TypeChecker:
  val defaultMaxSteps: Long = 1L << 32
  val maxTraceEntries: Int  = 32

  /** `g_dont_care`: placeholder for a binder whose variable does not occur. */
  private[kernel] val dontCare: Expr = Expr.const(Name.mkSimple("_dontCare"))
