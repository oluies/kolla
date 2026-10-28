package kolla.kernel

import scala.collection.mutable

/** Checks an inductive declaration and derives the environment entries for its
  * types, constructors and recursors, mirroring `add_inductive_fn` in
  * `src/kernel/inductive.cpp`.
  *
  * Two things are still missing: the nested-inductive preprocessor, so
  * `numNested` is taken from the declaration rather than computed, and
  * `check_uniform_ind_occs`. See docs/semantics.md K11.
  */
final class InductiveChecker(
    env0: Environment,
    decl: Declaration.InductDecl,
    profile: KernelProfile = KernelProfile.default,
    numNested: Int = 0,
    /** The reduction budget, so `--max-steps` reaches an inductive block too
      * and not only the declarations `DeclarationChecker` checks (K21).
      */
    maxSteps: Long = TypeChecker.defaultMaxSteps,
    /** A wall-clock bound, forwarded with `maxSteps` (K21, S2). */
    timeLimit: Option[TypeChecker.TimeLimit] = None
):
  private val lparams   = decl.levelParams
  private val nparams   = decl.numParams
  private val isUnsafe  = decl.isUnsafe
  private val indTypes  = decl.types.toVector
  private val levels    = Level.paramsToLevels(lparams)
  private val safety    = if isUnsafe then DefinitionSafety.Unsafe else DefinitionSafety.Safe

  private var env   = env0
  private val ngen  = new NameGenerator(Name.mkSimple("_ind_fresh"))
  private var lctx  = LocalContext.empty

  private val nindices   = mutable.ArrayBuffer.empty[Int]
  private val params     = mutable.ArrayBuffer.empty[Expr]
  private val indCnsts   = mutable.ArrayBuffer.empty[Expr]
  private var resultLevel: Level = Level.zero
  private var isNotZero  = false

  private def tc: TypeChecker = new TypeChecker(env, profile, safety, lctx, maxSteps, timeLimit)

  private def bad(detail: String): Nothing =
    throw KernelException(ExceptionKind.InvalidDeclaration, detail)

  private def checkNoMetavarNoFvar(n: Name, e: Expr): Unit =
    if e.hasExprMVar then
      throw KernelException(ExceptionKind.DeclarationHasMetavars, n, "the declaration contains metavariables")
    if e.hasFVar then
      throw KernelException(ExceptionKind.DeclarationHasFreeVars, n, "the declaration contains free variables")

  private def paramType(i: Int): Expr = lctx.get(params(i).asInstanceOf[Expr.FVar].id).tpe

  /** `mk_local_decl_for`: a free variable standing for the binder of `t`. */
  private def localDeclFor(t: Expr): Expr =
    val pi           = t.asInstanceOf[Expr.ForallE]
    val (next, fvar) =
      lctx.mkLocalDecl(ngen, pi.binderName, ExprOps.consumeTypeAnnotations(pi.binderType), pi.binderInfo)
    lctx = next
    fvar

  /** `check_inductive_types`. */
  private def checkInductiveTypes(): Unit =
    var first = true
    indTypes.foreach { indType =>
      env.checkName(indType.name)
      env.checkName(Names.recName(indType.name))
      checkNoMetavarNoFvar(indType.name, indType.tpe)
      tc.check(indType.tpe, lparams)
      nindices += 0
      var i    = 0
      var tpe  = tc.whnf(indType.tpe)
      while tpe.isInstanceOf[Expr.ForallE] do
        val pi = tpe.asInstanceOf[Expr.ForallE]
        if i < nparams then
          if first then
            val param = localDeclFor(tpe)
            params += param
            tpe = ExprOps.instantiate1(pi.body, param)
          else
            if !tc.isDefEq(pi.binderType, paramType(i)) then
              bad("parameters of all inductive datatypes must match")
            tpe = ExprOps.instantiate1(pi.body, params(i))
          i += 1
        else
          val local = localDeclFor(tpe)
          tpe = ExprOps.instantiate1(pi.body, local)
          nindices(nindices.length - 1) += 1
        tpe = tc.whnf(tpe)
      if i != nparams then
        bad("number of parameters mismatch in inductive datatype declaration")
      val sort = tc.ensureSort(tpe, tpe).asInstanceOf[Expr.Sort]
      if first then
        resultLevel = sort.level
        isNotZero = Level.isNotZero(resultLevel)
      else if !Level.isEquiv(sort.level, resultLevel) then
        bad("mutually inductive types must live in the same universe")
      indCnsts += Expr.Const(indType.name, levels)
      first = false
    }

  private def isIndOcc(e: Expr): Boolean = e match
    case c: Expr.Const => indTypes.exists(_.name == c.name)
    case _             => false

  private def hasIndOcc(t: Expr): Boolean =
    var found = false
    ExprOps.forEach(t) { (m, _) =>
      if found then false
      else if isIndOcc(m) then { found = true; false }
      else true
    }
    found

  /** `is_valid_ind_app(t, i)`. */
  private def isValidIndApp(t: Expr, i: Int): Boolean =
    val args = Expr.getAppArgs(t)
    val head = Expr.getAppFn(t)
    if head != indCnsts(i) || args.length != nparams + nindices(i) then false
    else if (0 until nparams).exists(k => params(k) != args(k)) then false
    else
      // An occurrence of a datatype being declared among the indices is unsound.
      !(nparams until args.length).exists(k => hasIndOcc(args(k)))

  private def isValidIndApp(t: Expr): Option[Int] =
    indTypes.indices.find(i => isValidIndApp(t, i))

  /** `check_positivity`. */
  private def checkPositivity(t0: Expr, ctorName: Name, argIdx: Int): Unit =
    var t = tc.whnf(t0)
    var done = false
    while !done do
      if !hasIndOcc(t) then done = true
      else
        t match
          case pi: Expr.ForallE =>
            if hasIndOcc(pi.binderType) then
              throw KernelException(
                ExceptionKind.InvalidDeclaration,
                ctorName,
                s"arg #${argIdx + 1} has a non positive occurrence of the datatypes being declared"
              )
            val local = localDeclFor(t)
            t = tc.whnf(ExprOps.instantiate1(pi.body, local))
          case _ =>
            if isValidIndApp(t).isDefined then done = true
            else
              throw KernelException(
                ExceptionKind.InvalidDeclaration,
                ctorName,
                s"arg #${argIdx + 1} contains a non valid occurrence of the datatypes being declared"
              )

  /** `check_constructors`. */
  private def checkConstructors(): Unit =
    indTypes.zipWithIndex.foreach { (indType, idx) =>
      val seen = mutable.HashSet.empty[Name]
      indType.ctors.foreach { ctor =>
        val n = ctor.name
        if !seen.add(n) then bad(s"duplicate constructor name '$n'")
        env.checkName(n)
        checkNoMetavarNoFvar(n, ctor.tpe)
        tc.check(ctor.tpe, lparams)
        var t = ctor.tpe
        var i = 0
        while t.isInstanceOf[Expr.ForallE] do
          val pi = t.asInstanceOf[Expr.ForallE]
          if i < nparams then
            if !tc.isDefEq(pi.binderType, paramType(i)) then
              throw KernelException(
                ExceptionKind.InvalidDeclaration,
                n,
                s"arg #${i + 1} does not match the inductive datatype's parameters"
              )
            t = ExprOps.instantiate1(pi.body, params(i))
          else
            val s = tc.ensureType(pi.binderType).asInstanceOf[Expr.Sort]
            // Acceptable if the level is at most the datatype's, or the datatype
            // is an inductive predicate.
            val predicate =
              if profile.propByNormalization then Level.normalizesToZero(resultLevel) else resultLevel.isZero
            if !(Level.geq(resultLevel, s.level) || predicate) then
              throw KernelException(
                ExceptionKind.InvalidDeclaration,
                n,
                s"the universe level of the type of arg #${i + 1} is too big for the inductive datatype"
              )
            if !isUnsafe then checkPositivity(pi.binderType, n, i)
            val local = localDeclFor(t)
            t = ExprOps.instantiate1(pi.body, local)
          i += 1
        if !isValidIndApp(t, idx) then
          throw KernelException(ExceptionKind.InvalidDeclaration, n, "invalid return type")
      }
    }

  /** `is_rec`. */
  private def computeIsRec: Boolean =
    indTypes.exists { indType =>
      indType.ctors.exists { ctor =>
        var t = ctor.tpe
        var found = false
        while !found && t.isInstanceOf[Expr.ForallE] do
          val pi = t.asInstanceOf[Expr.ForallE]
          if hasIndOcc(pi.binderType) then found = true
          t = pi.body
        found
      }
    }

  /** `is_reflexive`: some constructor takes a function returning one of the
    * datatypes in the block.
    */
  private def computeIsReflexive: Boolean =
    var found = false
    indTypes.foreach { indType =>
      indType.ctors.foreach { ctor =>
        var t = ctor.tpe
        while !found && t.isInstanceOf[Expr.ForallE] do
          val pi = t.asInstanceOf[Expr.ForallE]
          if pi.binderType.isInstanceOf[Expr.ForallE] && hasIndOcc(pi.binderType) then found = true
          else
            val local = localDeclFor(t)
            t = ExprOps.instantiate1(pi.body, local)
      }
    }
    found

  private def ctorArity(t0: Expr): Int =
    var t = t0
    var n = 0
    while t.isInstanceOf[Expr.ForallE] do
      t = t.asInstanceOf[Expr.ForallE].body
      n += 1
    n

  /** `declare_inductive_types` and `declare_constructors`. */
  private def derive(): (List[InductiveVal], List[ConstructorVal]) =
    val rec       = computeIsRec
    val reflexive = computeIsReflexive
    val all       = indTypes.map(_.name).toList
    val inds = indTypes.zipWithIndex.map { (indType, idx) =>
      InductiveVal(
        ConstantVal(indType.name, lparams, indType.tpe),
        nparams,
        nindices(idx),
        all,
        indType.ctors.map(_.name),
        numNested,
        rec,
        isUnsafe,
        reflexive
      )
    }.toList
    val ctors = indTypes.flatMap { indType =>
      indType.ctors.zipWithIndex.map { (ctor, cidx) =>
        val arity = ctorArity(ctor.tpe)
        if arity < nparams then
          throw KernelException(ExceptionKind.InvalidDeclaration, ctor.name, "fewer arguments than parameters")
        ConstructorVal(
          ConstantVal(ctor.name, lparams, ctor.tpe),
          indType.name,
          cidx,
          nparams,
          arity - nparams,
          isUnsafe
        )
      }
    }.toList
    (inds, ctors)

  // ----------------------------------------------------------- recursors

  private var elimLevel: Level = Level.zero
  private var kTarget: Boolean = false

  private final case class RecInfo(
      motive: Expr,
      indices: Vector[Expr],
      major: Expr,
      minors: mutable.ArrayBuffer[Expr]
  )

  private val recInfos = mutable.ArrayBuffer.empty[RecInfo]

  private def isPredicate: Boolean =
    if profile.propByNormalization then Level.normalizesToZero(resultLevel) else resultLevel.isZero

  /** `is_rec_argument`. */
  private def isRecArgument(t0: Expr): Option[Int] =
    var t = tc.whnf(t0)
    while t.isInstanceOf[Expr.ForallE] do
      val pi    = t.asInstanceOf[Expr.ForallE]
      val local = localDeclFor(t)
      t = tc.whnf(ExprOps.instantiate1(pi.body, local))
    isValidIndApp(t)

  /** `elim_only_at_universe_zero`. */
  private def elimOnlyAtUniverseZero: Boolean =
    if isNotZero then false
    else if indTypes.length > 1 then true
    else
      val ctors = indTypes(0).ctors
      if ctors.length > 1 then true
      else if ctors.isEmpty then false
      else
        // One constructor: every non-parameter argument must live in Prop or
        // occur in the result type.
        var t = ctors.head.tpe
        var i = 0
        val toCheck = mutable.ArrayBuffer.empty[Expr]
        while t.isInstanceOf[Expr.ForallE] do
          val pi   = t.asInstanceOf[Expr.ForallE]
          val fvar = localDeclFor(t)
          if i >= nparams then
            val s = tc.ensureType(pi.binderType).asInstanceOf[Expr.Sort]
            if !Level.normalizesToZero(s.level) then toCheck += fvar
          t = ExprOps.instantiate1(pi.body, fvar)
          i += 1
        val resultArgs = Expr.getAppArgs(t)
        toCheck.exists(arg => !resultArgs.contains(arg))

  /** `init_elim_level`. */
  private def initElimLevel(): Unit =
    if elimOnlyAtUniverseZero then elimLevel = Level.zero
    else
      var u = Name.mkSimple("u")
      var i = 1
      while lparams.contains(u) do
        u = Name.appendIndexAfter(Name.mkSimple("u"), i)
        i += 1
      elimLevel = Level.Param(u)

  /** `init_K_target`. */
  private def initKTarget(): Unit =
    kTarget = indTypes.length == 1 && isPredicate && indTypes(0).ctors.length == 1
    if kTarget then
      // K applies only when the single constructor has no fields.
      var t = indTypes(0).ctors.head.tpe
      var i = 0
      var stop = false
      while !stop && t.isInstanceOf[Expr.ForallE] do
        if i < nparams then
          t = t.asInstanceOf[Expr.ForallE].body
          i += 1
        else
          kTarget = false
          stop = true

  /** `get_I_indices`. */
  private def getIIndices(t: Expr): (Int, Vector[Expr]) =
    val idx = isValidIndApp(t).getOrElse(
      throw KernelException(ExceptionKind.InvalidDeclaration, "expected an application of a datatype being declared")
    )
    val all = Expr.getAppArgs(t)
    (idx, all.slice(nparams, all.length).toVector)

  private def recLevels: List[Level] =
    if elimLevel.isParam then elimLevel :: levels else levels

  private def recLparams: List[Name] =
    elimLevel match
      case p: Level.Param => p.name :: lparams
      case _              => lparams

  /** One pass over a constructor type, as `mk_rec_infos` does: the non-parameter
    * arguments, which of them are recursive, and the result type instantiated
    * with those same free variables.
    *
    * Splitting this into two walks would give the result type a different set of
    * free variables from the arguments.
    */
  private def ctorParts(ctorType: Expr): CtorParts =
    val bu = mutable.ArrayBuffer.empty[Expr]
    val u  = mutable.ArrayBuffer.empty[Expr]
    var t  = ctorType
    var i  = 0
    while t.isInstanceOf[Expr.ForallE] do
      val pi = t.asInstanceOf[Expr.ForallE]
      if i < nparams then t = ExprOps.instantiate1(pi.body, params(i))
      else
        val l = localDeclFor(t)
        bu += l
        if isRecArgument(pi.binderType).isDefined then u += l
        t = ExprOps.instantiate1(pi.body, l)
      i += 1
    CtorParts(bu.toVector, u.toVector, t)

  /** `mk_rec_infos`. */
  private def mkRecInfos(): Unit =
    indTypes.zipWithIndex.foreach { (indType, dIdx) =>
      val indices = mutable.ArrayBuffer.empty[Expr]
      var t = tc.whnf(indType.tpe)
      var i = 0
      while t.isInstanceOf[Expr.ForallE] do
        val pi = t.asInstanceOf[Expr.ForallE]
        if i < nparams then t = ExprOps.instantiate1(pi.body, params(i))
        else
          val idx = localDeclFor(t)
          indices += idx
          t = ExprOps.instantiate1(pi.body, idx)
        i += 1
        t = tc.whnf(t)
      val majorType = Expr.mkAppN(Expr.mkAppN(indCnsts(dIdx), params.toSeq), indices.toSeq)
      val (l1, major) = lctx.mkLocalDecl(ngen, Name.mkSimple("t"), majorType, BinderInfo.Default)
      lctx = l1
      var cTy: Expr = Expr.Sort(elimLevel)
      cTy = lctx.mkPi(Vector(major), cTy)
      cTy = lctx.mkPi(indices.toIndexedSeq, cTy)
      val cName =
        if indTypes.length > 1 then Name.appendIndexAfter(Name.mkSimple("motive"), dIdx + 1)
        else Name.mkSimple("motive")
      val (l2, motive) = lctx.mkLocalDecl(ngen, cName, cTy, BinderInfo.Default)
      lctx = l2
      recInfos += RecInfo(motive, indices.toVector, major, mutable.ArrayBuffer.empty)
    }

    indTypes.zipWithIndex.foreach { (indType, dIdx) =>
      indType.ctors.foreach { ctor =>
        val parts = ctorParts(ctor.tpe)
        val bu    = parts.args
        val u     = parts.recArgs
        val (itIdx, itIndices) = getIIndices(parts.result)
        val introApp = Expr.mkAppN(Expr.mkAppN(Expr.Const(ctor.name, levels), params.toSeq), bu)
        val cApp     = Expr.App(Expr.mkAppN(recInfos(itIdx).motive, itIndices), introApp)
        val v = u.map { ui =>
          var uiTy = tc.whnf(tc.infer(ui))
          val xs   = mutable.ArrayBuffer.empty[Expr]
          while uiTy.isInstanceOf[Expr.ForallE] do
            val pi = uiTy.asInstanceOf[Expr.ForallE]
            val xx = localDeclFor(uiTy)
            xs += xx
            uiTy = tc.whnf(ExprOps.instantiate1(pi.body, xx))
          val (jIdx, jIndices) = getIIndices(uiTy)
          val inner = Expr.App(Expr.mkAppN(recInfos(jIdx).motive, jIndices), Expr.mkAppN(ui, xs.toSeq))
          val viTy  = lctx.mkPi(xs.toIndexedSeq, inner)
          val uiName = lctx.get(ui.asInstanceOf[Expr.FVar].id).userName
          val (l3, vi) =
            lctx.mkLocalDecl(ngen, Name.appendAfter(uiName, "_ih"), viTy, BinderInfo.Default)
          lctx = l3
          vi
        }
        val minorTy   = lctx.mkPi(bu, lctx.mkPi(v, cApp))
        val minorName = Name.replacePrefix(ctor.name, indType.name, Name.anonymous)
        val (l4, minor) = lctx.mkLocalDecl(ngen, minorName, minorTy, BinderInfo.Default)
        lctx = l4
        recInfos(dIdx).minors += minor
      }
    }

  private def collectCs: Vector[Expr]     = recInfos.map(_.motive).toVector
  private def collectMinors: Vector[Expr] = recInfos.flatMap(_.minors).toVector

  /** `mk_rec_rules`. */
  private def mkRecRules(dIdx: Int, cs: Vector[Expr], minors: Vector[Expr], minorIdx0: Int): (List[RecursorRule], Int) =
    var minorIdx = minorIdx0
    val rules = indTypes(dIdx).ctors.map { ctor =>
      val parts = ctorParts(ctor.tpe)
      val bu    = parts.args
      val u     = parts.recArgs
      val v = u.map { ui =>
        var uiTy = tc.whnf(tc.infer(ui))
        val xs   = mutable.ArrayBuffer.empty[Expr]
        while uiTy.isInstanceOf[Expr.ForallE] do
          val pi = uiTy.asInstanceOf[Expr.ForallE]
          val xx = localDeclFor(uiTy)
          xs += xx
          uiTy = tc.whnf(ExprOps.instantiate1(pi.body, xx))
        val (jIdx, jIndices) = getIIndices(uiTy)
        val recApp = Expr.App(
          Expr.mkAppN(
            Expr.mkAppN(
              Expr.mkAppN(
                Expr.mkAppN(Expr.Const(Names.recName(indTypes(jIdx).name), recLevels), params.toSeq),
                cs
              ),
              minors
            ),
            jIndices
          ),
          Expr.mkAppN(ui, xs.toSeq)
        )
        lctx.mkLambda(xs.toIndexedSeq, recApp)
      }
      val eApp    = Expr.mkAppN(Expr.mkAppN(minors(minorIdx), bu), v)
      val compRhs =
        lctx.mkLambda(params.toIndexedSeq, lctx.mkLambda(cs, lctx.mkLambda(minors, lctx.mkLambda(bu, eApp))))
      minorIdx += 1
      RecursorRule(ctor.name, bu.length, compRhs)
    }
    (rules, minorIdx)

  /** `declare_recursors`. */
  private def declareRecursors(): List[RecursorVal] =
    val cs      = collectCs
    val minors  = collectMinors
    val all     = indTypes.map(_.name).toList
    var minorIdx = 0
    val out = mutable.ArrayBuffer.empty[RecursorVal]
    indTypes.indices.foreach { dIdx =>
      val info  = recInfos(dIdx)
      val cApp  = Expr.App(Expr.mkAppN(info.motive, info.indices), info.major)
      var recTy = lctx.mkPi(Vector(info.major), cApp)
      recTy = lctx.mkPi(info.indices, recTy)
      recTy = lctx.mkPi(minors, recTy)
      recTy = lctx.mkPi(cs, recTy)
      recTy = lctx.mkPi(params.toIndexedSeq, recTy)
      recTy = ExprOps.inferImplicit(recTy, strict = true)
      val (rules, nextIdx) = mkRecRules(dIdx, cs, minors, minorIdx)
      minorIdx = nextIdx
      val recName = Names.recName(indTypes(dIdx).name)
      env.checkName(recName)
      val rv = RecursorVal(
        ConstantVal(recName, recLparams, recTy),
        all, nparams, nindices(dIdx), cs.length, minors.length, rules, kTarget, isUnsafe
      )
      env = env.addCore(ConstantInfo.RecInfo(rv))
      out += rv
    }
    out.toList

  /** `check_recursors`: v4.35 type checks the generated recursors and verifies
    * each computation rule is type-preserving.
    */
  private def checkRecursors(): Unit =
    val cs     = collectCs
    val minors = collectMinors
    indTypes.indices.foreach { dIdx =>
      val recName = Names.recName(indTypes(dIdx).name)
      val recCi   = env.get(recName)
      tc.check(recCi.tpe, recLparams)
      val recPre = Expr.mkAppN(
        Expr.mkAppN(Expr.mkAppN(Expr.Const(recName, recLevels), params.toSeq), cs),
        minors
      )
      indTypes(dIdx).ctors.foreach { ctor =>
        val parts = ctorParts(ctor.tpe)
        val bu    = parts.args
        val (_, itIndices) = getIIndices(parts.result)
        val introApp = Expr.mkAppN(Expr.mkAppN(Expr.Const(ctor.name, levels), params.toSeq), bu)
        val lhs      = Expr.App(Expr.mkAppN(recPre, itIndices), introApp)
        val checker  = tc
        val expected = checker.infer(lhs)
        val reduct   = checker.whnf(lhs)
        val actual   = checker.infer(reduct)
        if !checker.isDefEq(actual, expected) then
          throw new KernelException(
            ExceptionKind.InvalidDeclaration,
            Some(ctor.name),
            "the generated recursor computation rule is not type-preserving",
            checker.defeqTrace
          )
      }
    }

  /** Runs the checks and returns the derived entries. The environment is extended
    * with the inductive types before the constructors are checked, as
    * `declare_inductive_types` does, because a constructor's type mentions them.
    */
  def run(): InductiveResult =
    if nparams < 0 then bad("invalid inductive datatype, number of parameters is too big")
    // `check_no_nested_aux` and `check_uniform_ind_occs` belong to
    // `environment::add_inductive`, not here: this is handed the *auxiliary*
    // declaration, which by construction mentions the reserved `_nested` prefix.
    // `AddInductive.add` runs them on the user's declaration.
    env.checkDuplicatedUnivParams(lparams)
    checkInductiveTypes()
    val rec       = computeIsRec
    val reflexive = computeIsReflexive
    val all       = indTypes.map(_.name).toList
    // Declare the types first so that the constructors can refer to them.
    indTypes.zipWithIndex.foreach { (indType, idx) =>
      env = env.addCore(ConstantInfo.InductInfo(InductiveVal(
        ConstantVal(indType.name, lparams, indType.tpe),
        nparams, nindices(idx), all, indType.ctors.map(_.name), numNested, rec, isUnsafe, reflexive
      )))
    }
    checkConstructors()
    val (inds, ctors) = derive()
    ctors.foreach(c => env = env.addCore(ConstantInfo.CtorInfo(c)))
    initElimLevel()
    initKTarget()
    mkRecInfos()
    val recs = declareRecursors()
    if profile.checkRecursors then checkRecursors()
    InductiveResult(env, inds, ctors, recs, resultLevel, nindices.toList, elimLevel, kTarget)

private final case class CtorParts(args: Vector[Expr], recArgs: Vector[Expr], result: Expr)

final case class InductiveResult(
    env: Environment,
    inductives: List[InductiveVal],
    constructors: List[ConstructorVal],
    recursors: List[RecursorVal],
    resultLevel: Level,
    numIndices: List[Int],
    elimLevel: Level,
    kTarget: Boolean
)

object InductiveChecker:

  /** `check_no_nested_aux`: user input must not mention the reserved prefix the
    * nested-inductive preprocessor uses for its auxiliary declarations.
    *
    * `proj` is included because a projection's structure name is resolved the
    * same way, so it could name an auxiliary type without the declaration ever
    * mentioning it as a constant.
    */
  def checkNoNestedAux(decl: Declaration.InductDecl): Unit =
    def check(n: Name, e: Expr): Unit =
      var offender: Option[Name] = None
      ExprOps.forEach(e) { (m, _) =>
        if offender.isDefined then false
        else
          m match
            case c: Expr.Const if Name.isPrefixOf(Names.nested, c.name) => offender = Some(c.name); false
            case p: Expr.Proj if Name.isPrefixOf(Names.nested, p.typeName) => offender = Some(p.typeName); false
            case _ => true
      }
      offender.foreach { _ =>
        throw KernelException(
          ExceptionKind.InvalidDeclaration,
          n,
          s"it uses the reserved prefix '${Names.nested}'"
        )
      }
    decl.types.foreach { t =>
      check(t.name, t.tpe)
      t.ctors.foreach(c => check(c.name, c.tpe))
    }

  /** `check_uniform_ind_occs` (v4.35): every occurrence of a datatype being
    * declared must be applied to exactly the declaration's parameters and
    * universe levels.
    *
    * Later phases inspect constructor types modulo `whnf`, which can erase an
    * occurrence, and a nested occurrence's parametric arguments are dropped from
    * the auxiliary declaration, so a non-uniform occurrence could escape those
    * checks. Reduction never creates an occurrence of a datatype being declared,
    * since none is in the environment yet, so the syntactic occurrences are all
    * of them.
    */
  def checkUniformIndOccs(decl: Declaration.InductDecl): Unit =
    val nparams  = decl.numParams
    val lvls     = Level.paramsToLevels(decl.levelParams)
    val indNames = decl.types.map(_.name).toSet
    decl.types.foreach { indType =>
      indType.ctors.foreach { ctor =>
        ExprOps.forEach(ctor.tpe) { (t, offset) =>
          Expr.getAppFn(t) match
            case fn: Expr.Const if indNames.contains(fn.name) =>
              val args = Expr.getAppArgs(t)
              // An over-applied occurrence is skipped here; the parameter
              // application itself is visited as a subterm and checked then.
              if args.length > nparams then true
              else
                val ok =
                  args.length == nparams && offset >= nparams && fn.levels == lvls &&
                    (0 until nparams).forall { i =>
                      args(i) match
                        case b: Expr.BVar => b.idx == offset - 1 - i
                        case _            => false
                    }
                if !ok then
                  throw KernelException(
                    ExceptionKind.InvalidDeclaration,
                    fn.name,
                    "invalid occurrence of a datatype being declared: it must be applied to the parameters " +
                      "and universe levels of the mutual declaration"
                  )
                false
            case _ => true
        }
      }
    }

  /** Rebuilds the `inductDecl` an export file's environment entries came from.
    *
    * The entries of one block are contiguous in an export file: the inductive
    * types, then their constructors.
    */
  def declarationOf(
      inds: List[InductiveVal],
      ctors: List[ConstructorVal]
  ): Declaration.InductDecl =
    if inds.isEmpty then
      throw KernelException(ExceptionKind.InvalidDeclaration, "an inductive block has no types")
    val head = inds.head
    val lparams = head.toConstantVal.levelParams
    inds.foreach { i =>
      if i.toConstantVal.levelParams != lparams then
        throw KernelException(
          ExceptionKind.InvalidDeclaration,
          i.toConstantVal.name,
          "the types of a mutual inductive block must share their universe parameters"
        )
      if i.numParams != head.numParams then
        throw KernelException(
          ExceptionKind.InvalidDeclaration,
          i.toConstantVal.name,
          "the types of a mutual inductive block must share their parameter count"
        )
    }
    val byInduct = ctors.groupBy(_.induct)
    val types = inds.map { i =>
      val own = i.ctors.map { cn =>
        val cv = byInduct.getOrElse(i.toConstantVal.name, Nil).find(_.toConstantVal.name == cn).getOrElse(
          throw KernelException(
            ExceptionKind.InvalidDeclaration,
            cn,
            s"the export file lists it as a constructor of '${i.toConstantVal.name}' but does not declare it"
          )
        )
        Constructor(cn, cv.toConstantVal.tpe)
      }
      InductiveType(i.toConstantVal.name, i.toConstantVal.tpe, own)
    }
    Declaration.InductDecl(lparams, head.numParams, types, head.isUnsafe)

  /** Compares the entries an export file ships against the ones the kernel
    * derives. `numNested` is taken from the file, so a nested block is accepted
    * on that field alone.
    */
  def validate(
      exportedInds: List[InductiveVal],
      exportedCtors: List[ConstructorVal],
      derivedInds: List[InductiveVal],
      derivedCtors: List[ConstructorVal],
      exportedRecs: List[RecursorVal] = Nil,
      derivedRecs: List[RecursorVal] = Nil
  ): Unit =
    def mismatch(n: Name, field: String, got: Any, want: Any): Nothing =
      throw KernelException(
        ExceptionKind.InvalidDeclaration,
        n,
        s"$field is $got in the export file but the kernel derives $want"
      )
    if exportedInds.length != derivedInds.length then
      mismatch(exportedInds.head.toConstantVal.name, "the number of types", exportedInds.length, derivedInds.length)
    exportedInds.zip(derivedInds).foreach { (got, want) =>
      val n = got.toConstantVal.name
      if n != want.toConstantVal.name then mismatch(n, "the type name", n, want.toConstantVal.name)
      if got.numParams != want.numParams then mismatch(n, "numParams", got.numParams, want.numParams)
      if got.numIndices != want.numIndices then mismatch(n, "numIndices", got.numIndices, want.numIndices)
      if got.ctors != want.ctors then
        mismatch(n, "the constructor list", got.ctors.map(_.toString), want.ctors.map(_.toString))
      if got.all != want.all then mismatch(n, "the mutual block", got.all.map(_.toString), want.all.map(_.toString))
      if got.isRec != want.isRec then mismatch(n, "isRec", got.isRec, want.isRec)
      if got.isReflexive != want.isReflexive then mismatch(n, "isReflexive", got.isReflexive, want.isReflexive)
      if got.isUnsafe != want.isUnsafe then mismatch(n, "isUnsafe", got.isUnsafe, want.isUnsafe)
    }
    if exportedCtors.length != derivedCtors.length then
      throw KernelException(
        ExceptionKind.InvalidDeclaration,
        s"the export file declares ${exportedCtors.length} constructors but the kernel derives ${derivedCtors.length}"
      )
    val derivedByName = derivedCtors.map(c => c.toConstantVal.name -> c).toMap
    exportedCtors.foreach { got =>
      val n    = got.toConstantVal.name
      val want = derivedByName.getOrElse(n, mismatch(n, "the constructor", n, "nothing"))
      if got.induct != want.induct then mismatch(n, "induct", got.induct.toString, want.induct.toString)
      if got.cidx != want.cidx then mismatch(n, "cidx", got.cidx, want.cidx)
      if got.numParams != want.numParams then mismatch(n, "numParams", got.numParams, want.numParams)
      if got.numFields != want.numFields then mismatch(n, "numFields", got.numFields, want.numFields)
      if got.isUnsafe != want.isUnsafe then mismatch(n, "isUnsafe", got.isUnsafe, want.isUnsafe)
    }
    validateRecursors(exportedRecs, derivedRecs)

  /** Compares the recursors an export file ships against the regenerated ones,
    * including every computation rule's right-hand side.
    */
  private def validateRecursors(exported: List[RecursorVal], derived: List[RecursorVal]): Unit =
    def mismatch(n: Name, field: String, got: Any, want: Any): Nothing =
      throw KernelException(
        ExceptionKind.InvalidDeclaration,
        n,
        s"$field is $got in the export file but the kernel derives $want"
      )
    if exported.length != derived.length then
      throw KernelException(
        ExceptionKind.InvalidDeclaration,
        s"the export file declares ${exported.length} recursors but the kernel derives ${derived.length}"
      )
    val derivedByName = derived.map(r => r.toConstantVal.name -> r).toMap
    exported.foreach { got =>
      val n    = got.toConstantVal.name
      val want = derivedByName.getOrElse(n, mismatch(n, "the recursor", n, "nothing"))
      val gcv  = got.toConstantVal
      val wcv  = want.toConstantVal
      if gcv.levelParams.length != wcv.levelParams.length then
        mismatch(n, "the universe parameter count", gcv.levelParams.length, wcv.levelParams.length)
      if got.numParams != want.numParams then mismatch(n, "numParams", got.numParams, want.numParams)
      if got.numIndices != want.numIndices then mismatch(n, "numIndices", got.numIndices, want.numIndices)
      if got.numMotives != want.numMotives then mismatch(n, "numMotives", got.numMotives, want.numMotives)
      if got.numMinors != want.numMinors then mismatch(n, "numMinors", got.numMinors, want.numMinors)
      if got.k != want.k then mismatch(n, "the K-like reduction flag", got.k, want.k)
      if got.isUnsafe != want.isUnsafe then mismatch(n, "isUnsafe", got.isUnsafe, want.isUnsafe)
      if got.all != want.all then
        mismatch(n, "the mutual block", got.all.map(_.toString), want.all.map(_.toString))
      // The exported recursor may name its elimination universe differently.
      val subst = gcv.levelParams.map(Level.Param(_))
      def rename(e: Expr): Expr = ExprOps.instantiateLevelParams(e, wcv.levelParams, subst)
      if rename(wcv.tpe) != gcv.tpe then
        throw KernelException(
          ExceptionKind.InvalidDeclaration,
          n,
          s"the recursor type is\n  ${Pretty.expr(gcv.tpe)}\nbut the kernel derives\n  ${Pretty.expr(rename(wcv.tpe))}"
        )
      // Binder names and `BinderInfo` are deliberately not compared: an export
      // file cannot carry them. lean4export interns expressions in a
      // `HashMap Expr Nat` keyed on Lean's `BEq Expr`, which is `is_equal` and
      // ignores both, so a shape gets whichever binder names were written
      // first. See docs/semantics.md X14.
      if got.rules.length != want.rules.length then
        mismatch(n, "the rule count", got.rules.length, want.rules.length)
      val wantRules = want.rules.map(r => r.ctor -> r).toMap
      got.rules.foreach { gr =>
        val wr = wantRules.getOrElse(gr.ctor, mismatch(n, s"a rule for '${gr.ctor}'", "present", "absent"))
        if gr.nfields != wr.nfields then
          mismatch(gr.ctor, "the rule's nfields", gr.nfields, wr.nfields)
        if rename(wr.rhs) != gr.rhs then
          throw KernelException(
            ExceptionKind.InvalidDeclaration,
            gr.ctor,
            s"the recursor rule is\n  ${Pretty.expr(gr.rhs)}\nbut the kernel derives\n  ${Pretty.expr(rename(wr.rhs))}"
          )
      }
    }
