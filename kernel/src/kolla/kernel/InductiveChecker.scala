package kolla.kernel

import scala.collection.mutable

/** Checks an inductive declaration and derives the environment entries for its
  * types and constructors, mirroring `add_inductive_fn` in
  * `src/kernel/inductive.cpp`.
  *
  * Recursor generation is not implemented yet, so `run` stops after the
  * constructors; `numNested` is taken from the declaration rather than computed,
  * because computing it needs the nested-inductive preprocessor.
  */
final class InductiveChecker(
    env0: Environment,
    decl: Declaration.InductDecl,
    profile: KernelProfile = KernelProfile.default,
    numNested: Int = 0
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

  private def tc: TypeChecker = new TypeChecker(env, profile, safety, lctx)

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
    val (next, fvar) = lctx.mkLocalDecl(ngen, pi.binderName, Expr.consumeMData(pi.binderType), pi.binderInfo)
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

  /** Runs the checks and returns the derived entries. The environment is extended
    * with the inductive types before the constructors are checked, as
    * `declare_inductive_types` does, because a constructor's type mentions them.
    */
  def run(): InductiveResult =
    if nparams < 0 then bad("invalid inductive datatype, number of parameters is too big")
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
    InductiveResult(env, inds, ctors, resultLevel, nindices.toList)

final case class InductiveResult(
    env: Environment,
    inductives: List[InductiveVal],
    constructors: List[ConstructorVal],
    resultLevel: Level,
    numIndices: List[Int]
)

object InductiveChecker:

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
      derivedCtors: List[ConstructorVal]
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
