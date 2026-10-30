package kolla.kernel

/** Declaration checking, mirroring `environment::add_axiom`, `add_definition`,
  * `add_theorem`, `add_opaque` and `add_mutual` in `src/kernel/environment.cpp`.
  *
  * A fresh `TypeChecker` is created per declaration. Its caches are reused
  * from the previous one and emptied first, so nothing cached carries over.
  */
final class DeclarationChecker(
    val profile: KernelProfile = KernelProfile.default,
    /** The reduction budget each declaration gets. Lowering it turns a check
      * that does not finish into a report of what it was doing (K21).
      */
    val maxSteps: Long = TypeChecker.defaultMaxSteps,
    /** A wall-clock bound each declaration gets, alongside `maxSteps`. */
    val timeLimit: Option[TypeChecker.TimeLimit] = None
):

  /** `check_no_metavar_no_fvar`. */
  private def checkNoMetavarNoFvar(n: Name, e: Expr): Unit =
    if e.hasExprMVar then
      throw KernelException(ExceptionKind.DeclarationHasMetavars, n, "the declaration contains metavariables")
    if e.hasFVar then
      throw KernelException(ExceptionKind.DeclarationHasFreeVars, n, "the declaration contains free variables")

  /** `check_constant_val`. */
  private def checkConstantVal(env: Environment, v: ConstantVal, tc: TypeChecker): Unit =
    env.checkName(v.name)
    env.checkDuplicatedUnivParams(v.levelParams)
    checkNoMetavarNoFvar(v.name, v.tpe)
    val sort = tc.check(v.tpe, v.levelParams)
    tc.ensureSort(sort, v.tpe)

  /** A wall-clock window for one declaration.
    *
    * One per declaration, not per `TypeChecker`: checking a single declaration
    * builds two or three, and a budget that restarted for each would bound
    * none of them. Every public entry point opens its own and passes it to
    * each checker it builds, which is why `checker` takes it rather than
    * reading a field: a field has a value for a path that forgot to set it,
    * and the one it had was the run's own limit — already started, and shared
    * by every later declaration. See docs/semantics.md S2.
    */
  private def window(): Option[TypeChecker.TimeLimit] = timeLimit.map(_.fresh())

  /** Shared by every checker built here. Each entry point is done with one
    * checker before it builds the next, so handing them the same caches is
    * the same as giving each its own.
    */
  private val caches = new TypeChecker.Caches

  private def checker(
      env: Environment,
      safety: DefinitionSafety,
      window: Option[TypeChecker.TimeLimit]
  ): TypeChecker =
    new TypeChecker(env, profile, safety, LocalContext.empty, maxSteps, window, caches)

  private def mismatch(n: Name, given0: Expr, expected: Expr, tc: TypeChecker): Nothing =
    throw new KernelException(
      ExceptionKind.DefinitionTypeMismatch,
      Some(n),
      s"declaration has type\n  ${Pretty.expr(expected)}\nbut its value has type\n  ${Pretty.expr(given0)}",
      tc.defeqTrace
    )

  def addAxiom(env: Environment, v: AxiomVal, check: Boolean = true): Environment =
    if check then
      val safety = if v.isUnsafe then DefinitionSafety.Unsafe else DefinitionSafety.Safe
      checkConstantVal(env, v.toConstantVal, checker(env, safety, window()))
    env.addCore(ConstantInfo.AxiomInfo(v))

  def addDefinition(env: Environment, v: DefinitionVal, check: Boolean = true): Environment =
    val cv = v.toConstantVal
    val w  = window()
    if v.isUnsafe then
      // An unsafe definition may be recursive, so its header is checked, the
      // declaration is added, and only then is the body checked.
      if check then checkConstantVal(env, cv, checker(env, DefinitionSafety.Unsafe, w))
      val newEnv = env.addCore(ConstantInfo.DefnInfo(v))
      if check then
        val tc = checker(newEnv, DefinitionSafety.Unsafe, w)
        checkNoMetavarNoFvar(cv.name, v.value)
        val valType = tc.check(v.value, cv.levelParams)
        if !tc.isDefEq(valType, cv.tpe) then mismatch(cv.name, valType, cv.tpe, tc)
      newEnv
    else
      if check then
        val tc = checker(env, DefinitionSafety.Safe, w)
        checkConstantVal(env, cv, tc)
        checkNoMetavarNoFvar(cv.name, v.value)
        val valType = tc.check(v.value, cv.levelParams)
        if !tc.isDefEq(valType, cv.tpe) then mismatch(cv.name, valType, cv.tpe, tc)
      env.addCore(ConstantInfo.DefnInfo(v))

  def addTheorem(env: Environment, v: TheoremVal, check: Boolean = true): Environment =
    val cv = v.toConstantVal
    if check then
      val tc = checker(env, DefinitionSafety.Safe, window())
      checkConstantVal(env, cv, tc)
      if !tc.isProp(cv.tpe) then
        throw KernelException(
          ExceptionKind.TheoremTypeIsNotProp,
          cv.name,
          s"the type of a theorem must be a proposition, got\n  ${Pretty.expr(cv.tpe)}"
        )
      checkNoMetavarNoFvar(cv.name, v.value)
      val valType = tc.check(v.value, cv.levelParams)
      if !tc.isDefEq(valType, cv.tpe) then mismatch(cv.name, valType, cv.tpe, tc)
    env.addCore(ConstantInfo.ThmInfo(v))

  def addOpaque(env: Environment, v: OpaqueVal, check: Boolean = true): Environment =
    val cv = v.toConstantVal
    if check then
      val tc = checker(env, DefinitionSafety.Safe, window())
      checkConstantVal(env, cv, tc)
      checkNoMetavarNoFvar(cv.name, v.value)
      val valType = tc.check(v.value, cv.levelParams)
      if !tc.isDefEq(valType, cv.tpe) then mismatch(cv.name, valType, cv.tpe, tc)
    env.addCore(ConstantInfo.OpaqueInfo(v))

  def addMutual(env: Environment, vs: List[DefinitionVal], check: Boolean = true): Environment =
    if vs.isEmpty then
      throw KernelException(ExceptionKind.InvalidDeclaration, "invalid empty mutual definition")
    val safety = vs.head.safety
    if safety == DefinitionSafety.Safe then
      throw KernelException(
        ExceptionKind.InvalidDeclaration,
        "invalid mutual definition, the declarations are not tagged unsafe or partial"
      )
    val lparams = vs.head.toConstantVal.levelParams
    val w       = window()
    if check then
      val tc = checker(env, safety, w)
      vs.foreach { v =>
        if v.toConstantVal.levelParams != lparams then
          throw KernelException(
            ExceptionKind.InvalidDeclaration,
            v.toConstantVal.name,
            "invalid mutual definition, universe parameters must match"
          )
        if v.safety != safety then
          throw KernelException(
            ExceptionKind.InvalidDeclaration,
            v.toConstantVal.name,
            "invalid mutual definition, safety annotations must match"
          )
        checkConstantVal(env, v.toConstantVal, tc)
      }
    val newEnv = vs.foldLeft(env)((e, v) => e.addCore(ConstantInfo.DefnInfo(v)))
    if check then
      val tc = checker(newEnv, safety, w)
      vs.foreach { v =>
        val cv = v.toConstantVal
        checkNoMetavarNoFvar(cv.name, v.value)
        val valType = tc.check(v.value, cv.levelParams)
        if !tc.isDefEq(valType, cv.tpe) then mismatch(cv.name, valType, cv.tpe, tc)
      }
    newEnv

  /** `environment::add(declaration, check)`. */
  def add(env: Environment, d: Declaration, check: Boolean = true): Environment =
    d match
    case Declaration.AxiomDecl(v)       => addAxiom(env, v, check)
    case Declaration.DefnDecl(v)        => addDefinition(env, v, check)
    case Declaration.ThmDecl(v)         => addTheorem(env, v, check)
    case Declaration.OpaqueDecl(v)      => addOpaque(env, v, check)
    case Declaration.MutualDefnDecl(vs) => addMutual(env, vs, check)
    case Declaration.QuotDecl => Quot.add(env)
    case Declaration.InductDecl(_, _, _, _) =>
      throw KernelException(
        ExceptionKind.InvalidDeclaration,
        "inductive declarations are not implemented yet"
      )

  /** Replays an environment entry from an export file.
    *
    * Axioms, definitions, theorems and opaques are checked exactly as
    * `environment::add` would. Inductive types, constructors and recursors are
    * carried over from the file with their types checked but their mutual
    * consistency not yet validated, so `check` reports whether an entry was
    * fully checked.
    */
  def addInfo(env: Environment, info: ConstantInfo): (Environment, CheckOutcome) =
    info match
    case ConstantInfo.AxiomInfo(v)  => (addAxiom(env, v), CheckOutcome.Checked)
    case ConstantInfo.DefnInfo(v)   => (addDefinition(env, v), CheckOutcome.Checked)
    case ConstantInfo.ThmInfo(v)    => (addTheorem(env, v), CheckOutcome.Checked)
    case ConstantInfo.OpaqueInfo(v) => (addOpaque(env, v), CheckOutcome.Checked)
    case ConstantInfo.QuotInfo(v) =>
      // `add_quot` installs all four constants at once, so the first one an
      // export file mentions triggers the whole package; each exported constant
      // is then validated against the one the kernel built.
      val next = if env.quotInitialized then env else Quot.add(env)
      Quot.validate(next, List(v))
      (next, CheckOutcome.Checked)
    case ConstantInfo.InductInfo(v) =>
      (typeOnly(env, v.toConstantVal, info), CheckOutcome.TypeOnly)
    case ConstantInfo.CtorInfo(v) =>
      (typeOnly(env, v.toConstantVal, info), CheckOutcome.TypeOnly)
    case ConstantInfo.RecInfo(v) =>
      // Only the recursor's own type is checked here. A rule's right-hand side
      // may call a sibling recursor of the same block — a nested inductive's
      // `T.rec` calls `T.rec_1` — and `declare_recursors` installs every
      // recursor of a block before `check_recursors` looks at any rule, so a
      // rule cannot be checked one entry at a time. `InductiveChecker.run` is
      // the path that checks them.
      v.rules.foreach(r => checkNoMetavarNoFvar(v.toConstantVal.name, r.rhs))
      (typeOnly(env, v.toConstantVal, info), CheckOutcome.TypeOnly)

  private def typeOnly(env: Environment, cv: ConstantVal, info: ConstantInfo): Environment =
    val w  = window()
    val tc = checker(env, DefinitionSafety.Safe, w)
    env.checkName(cv.name)
    env.checkDuplicatedUnivParams(cv.levelParams)
    checkNoMetavarNoFvar(cv.name, cv.tpe)
    // An inductive type's own constant is not in the environment while its
    // constructors' types are checked, so the type is added first and the
    // well-formedness check runs against the extended environment.
    val next = env.addCore(info)
    val tc2  = checker(next, DefinitionSafety.Safe, w)
    val sort = tc2.check(cv.tpe, cv.levelParams)
    tc2.ensureSort(sort, cv.tpe)
    next

/** How completely an entry was checked. */
enum CheckOutcome:
  case Checked
  case TypeOnly
