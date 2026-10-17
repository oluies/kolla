package kolla.kernel

/** The quotient package, mirroring `environment::add_quot` in
  * `src/kernel/quot.cpp`.
  *
  * `Declaration.QuotDecl` carries no data: the kernel builds the four constants
  * itself, which is also how they can be validated against an export file that
  * ships them.
  */
object Quot:

  private def arrow(d: Expr, c: Expr): Expr =
    Expr.ForallE(Name.mkSimple("a"), d, c, BinderInfo.Default)

  private val prop: Expr = Expr.Sort(Level.zero)

  /** `check_eq_type`: `Eq` must be the inductive the quotient package expects. */
  def checkEqType(env: Environment): Unit =
    def bad(detail: String): Nothing =
      throw KernelException(ExceptionKind.InvalidDeclaration, Names.eq, detail)
    val eqInfo = env.find(Names.eq).getOrElse(bad("the environment does not have an 'Eq' type"))
    val eqVal = eqInfo match
      case ConstantInfo.InductInfo(v) => v
      case _                          => bad("'Eq' is not an inductive type")
    if eqInfo.levelParams.length != 1 then bad("'Eq' has an unexpected number of universe parameters")
    if eqVal.ctors.length != 1 then bad("'Eq' has an unexpected number of constructors")

    val g = new NameGenerator()
    var lctx = LocalContext.empty
    val u  = eqInfo.levelParams.head
    val lu = Level.Param(u)
    val (l1, alpha) = lctx.mkLocalDecl(g, Name.mkSimple("α"), Expr.Sort(lu), BinderInfo.Implicit)
    lctx = l1
    val expectedEq = lctx.mkPi(Vector(alpha), arrow(alpha, arrow(alpha, prop)))
    if expectedEq != eqInfo.tpe then bad("'Eq' has an unexpected type")

    val reflInfo = env.get(eqVal.ctors.head)
    if reflInfo.levelParams.length != 1 then
      bad("the constructor of 'Eq' has an unexpected number of universe parameters")
    val g2 = new NameGenerator()
    var lctx2 = LocalContext.empty
    val lu2 = Level.Param(reflInfo.levelParams.head)
    val (m1, alpha2) = lctx2.mkLocalDecl(g2, Name.mkSimple("α"), Expr.Sort(lu2), BinderInfo.Implicit)
    lctx2 = m1
    val (m2, a2) = lctx2.mkLocalDecl(g2, Name.mkSimple("a"), alpha2, BinderInfo.Default)
    lctx2 = m2
    val expectedRefl =
      lctx2.mkPi(Vector(alpha2, a2), Expr.mkAppN(Expr.Const(Names.eq, List(lu2)), Seq(alpha2, a2, a2)))
    if expectedRefl != reflInfo.tpe then
      bad("the constructor of 'Eq' has an unexpected type")

  /** The four declarations `add_quot` installs, in the order it installs them. */
  def declarations: List[QuotVal] =
    val g = new NameGenerator()
    val uName = Name.mkSimple("u")
    val vName = Name.mkSimple("v")
    val u  = Level.Param(uName)
    val v  = Level.Param(vName)
    val sortU = Expr.Sort(u)
    val sortV = Expr.Sort(v)

    var lctx = LocalContext.empty
    def decl(n: Name, t: Expr, bi: BinderInfo): Expr =
      val (next, fvar) = lctx.mkLocalDecl(g, n, t, bi)
      lctx = next
      fvar

    // Quot and Quot.mk take `r` explicitly.
    val alpha = decl(Name.mkSimple("α"), sortU, BinderInfo.Implicit)
    val r     = decl(Name.mkSimple("r"), arrow(alpha, arrow(alpha, prop)), BinderInfo.Default)
    val quotR = Expr.mkAppN(Expr.Const(Names.quot, List(u)), Seq(alpha, r))
    val quotType = lctx.mkPi(Vector(alpha, r), sortU)
    val a0    = decl(Name.mkSimple("a"), alpha, BinderInfo.Default)
    val mkType = lctx.mkPi(Vector(alpha, r, a0), quotR)

    // Quot.lift and Quot.ind take `r` implicitly, so the context restarts.
    lctx = LocalContext.empty
    val alphaI = decl(Name.mkSimple("α"), sortU, BinderInfo.Implicit)
    val rI     = decl(Name.mkSimple("r"), arrow(alphaI, arrow(alphaI, prop)), BinderInfo.Implicit)
    val quotRI = Expr.mkAppN(Expr.Const(Names.quot, List(u)), Seq(alphaI, rI))
    val a      = decl(Name.mkSimple("a"), alphaI, BinderInfo.Default)
    val beta   = decl(Name.mkSimple("β"), sortV, BinderInfo.Implicit)
    val f      = decl(Name.mkSimple("f"), arrow(alphaI, beta), BinderInfo.Default)
    val b      = decl(Name.mkSimple("b"), alphaI, BinderInfo.Default)
    val rab    = Expr.mkAppN(rI, Seq(a, b))
    val faEqFb =
      Expr.mkAppN(Expr.Const(Names.eq, List(v)), Seq(beta, Expr.App(f, a), Expr.App(f, b)))
    val sanity = lctx.mkPi(Vector(a, b), arrow(rab, faEqFb))
    val liftType =
      lctx.mkPi(Vector(alphaI, rI, beta, f), arrow(sanity, arrow(quotRI, beta)))

    val betaP   = decl(Name.mkSimple("β"), arrow(quotRI, prop), BinderInfo.Implicit)
    val quotMkA = Expr.mkAppN(Expr.Const(Names.quotMk, List(u)), Seq(alphaI, rI, a))
    val allQuot = lctx.mkPi(Vector(a), Expr.App(betaP, quotMkA))
    val q       = decl(Name.mkSimple("q"), quotRI, BinderInfo.Default)
    val betaQ   = Expr.App(betaP, q)
    val indType =
      lctx.mkPi(
        Vector(alphaI, rI, betaP),
        Expr.ForallE(Name.mkSimple("mk"), allQuot, lctx.mkPi(Vector(q), betaQ), BinderInfo.Default)
      )

    List(
      QuotVal(ConstantVal(Names.quot, List(uName), quotType), QuotKind.Type),
      QuotVal(ConstantVal(Names.quotMk, List(uName), mkType), QuotKind.Ctor),
      QuotVal(ConstantVal(Names.quotLift, List(uName, vName), liftType), QuotKind.Lift),
      QuotVal(ConstantVal(Names.quotInd, List(uName), indType), QuotKind.Ind)
    )

  /** `environment::add_quot`. */
  def add(env: Environment): Environment =
    if env.quotInitialized then env
    else
      checkEqType(env)
      // `add_core` overwrites, so a name already taken would silently replace a
      // constant other declarations were checked against.
      declarations.foreach(d => env.checkName(d.toConstantVal.name))
      declarations
        .foldLeft(env)((e, d) => e.addCore(ConstantInfo.QuotInfo(d)))
        .markQuotInitialized

  /** Validates the quotient constants an export file ships against the ones the
    * kernel builds.
    */
  def validate(env: Environment, exported: List[QuotVal]): Unit =
    val expected = declarations.map(d => d.toConstantVal.name -> d).toMap
    exported.foreach { got =>
      val cv = got.toConstantVal
      expected.get(cv.name) match
        case None =>
          throw KernelException(ExceptionKind.InvalidDeclaration, cv.name, "not a quotient declaration")
        case Some(want) =>
          val wcv = want.toConstantVal
          if got.kind != want.kind then
            throw KernelException(
              ExceptionKind.InvalidDeclaration,
              cv.name,
              s"quotient kind mismatch: expected ${want.kind}, got ${got.kind}"
            )
          if cv.levelParams.length != wcv.levelParams.length then
            throw KernelException(
              ExceptionKind.InvalidDeclaration,
              cv.name,
              s"expected ${wcv.levelParams.length} universe parameters, got ${cv.levelParams.length}"
            )
          val renamed = ExprOps.instantiateLevelParams(
            wcv.tpe, wcv.levelParams, cv.levelParams.map(Level.Param(_))
          )
          if renamed != cv.tpe then
            throw KernelException(
              ExceptionKind.InvalidDeclaration,
              cv.name,
              s"quotient declaration has type\n  ${Pretty.expr(cv.tpe)}\nbut the kernel builds\n  ${Pretty.expr(renamed)}"
            )
    }
