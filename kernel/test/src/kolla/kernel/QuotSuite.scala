package kolla.kernel

class QuotSuite extends munit.FunSuite:

  val u    = Name.mkSimple("u")
  val lu   = Level.Param(u)
  val prop = Expr.Sort(Level.zero)
  def arrow(d: Expr, c: Expr) = Expr.ForallE(Name.mkSimple("a"), d, c, BinderInfo.Default)

  /** `Eq` exactly as `check_eq_type` expects it. */
  def envWithEq: Environment =
    val g = new NameGenerator()
    var lctx = LocalContext.empty
    val (l1, alpha) = lctx.mkLocalDecl(g, Name.mkSimple("α"), Expr.Sort(lu), BinderInfo.Implicit)
    lctx = l1
    val eqType = lctx.mkPi(Vector(alpha), arrow(alpha, arrow(alpha, prop)))
    val (l2, a) = lctx.mkLocalDecl(g, Name.mkSimple("a"), alpha, BinderInfo.Default)
    lctx = l2
    val reflType =
      lctx.mkPi(Vector(alpha, a), Expr.mkAppN(Expr.Const(Names.eq, List(lu)), Seq(alpha, a, a)))
    Environment.empty
      .addCore(ConstantInfo.InductInfo(InductiveVal(
        ConstantVal(Names.eq, List(u), eqType), 2, 1,
        List(Names.eq), List(Name.parse("Eq.refl")), 0, false, false, false
      )))
      .addCore(ConstantInfo.CtorInfo(ConstructorVal(
        ConstantVal(Name.parse("Eq.refl"), List(u), reflType), Names.eq, 0, 2, 0, false
      )))

  test("the package has the four constants in add_quot's order") {
    val ds = Quot.declarations
    assertEquals(ds.map(_.toConstantVal.name.toString), List("Quot", "Quot.mk", "Quot.lift", "Quot.ind"))
    assertEquals(ds.map(_.kind), List(QuotKind.Type, QuotKind.Ctor, QuotKind.Lift, QuotKind.Ind))
    // Only Quot.lift is polymorphic in two universes.
    assertEquals(ds.map(_.toConstantVal.levelParams.length), List(1, 1, 2, 1))
    ds.foreach(d => assert(!d.toConstantVal.tpe.hasLooseBVars, clue(d.toConstantVal.name.toString)))
    ds.foreach(d => assert(!d.toConstantVal.tpe.hasFVar, clue(d.toConstantVal.name.toString)))
  }

  test("add installs the package and is idempotent") {
    val env = Quot.add(envWithEq)
    assert(env.quotInitialized)
    assertEquals(env.size, envWithEq.size + 4)
    Names.quotNames.foreach(n => assert(env.contains(n), clue(n.toString)))
    assertEquals(Quot.add(env).size, env.size)
  }

  test("checkEqType rejects a wrong Eq") {
    assert(clue(intercept[KernelException](Quot.checkEqType(Environment.empty)).getMessage)
      .contains("does not have an 'Eq' type"))

    val badType = Environment.empty.addCore(ConstantInfo.InductInfo(InductiveVal(
      ConstantVal(Names.eq, List(u), Expr.Sort(lu)), 0, 0,
      List(Names.eq), List(Name.parse("Eq.refl")), 0, false, false, false
    ))).addCore(ConstantInfo.CtorInfo(ConstructorVal(
      ConstantVal(Name.parse("Eq.refl"), List(u), Expr.Sort(lu)), Names.eq, 0, 0, 0, false
    )))
    assert(clue(intercept[KernelException](Quot.checkEqType(badType)).getMessage)
      .contains("'Eq' has an unexpected type"))

    val notInductive = Environment.empty.addCore(ConstantInfo.AxiomInfo(
      AxiomVal(ConstantVal(Names.eq, List(u), Expr.Sort(lu)), false)
    ))
    assert(clue(intercept[KernelException](Quot.checkEqType(notInductive)).getMessage)
      .contains("not an inductive type"))
  }

  test("the quotient types are well typed") {
    val env = Quot.add(envWithEq)
    Quot.declarations.foreach { d =>
      val cv = d.toConstantVal
      val tc = new TypeChecker(env, KernelProfile.v4_35)
      val sort = tc.check(cv.tpe, cv.levelParams)
      tc.ensureSort(sort, cv.tpe)
    }
  }

  test("Quot.lift reduces on Quot.mk") {
    val env = Quot.add(envWithEq)
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("A"), Nil, Expr.Sort(Level.one)), false)))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(
        ConstantVal(Name.parse("rel"), Nil, arrow(Expr.const("A"), arrow(Expr.const("A"), prop))), false
      )))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(
        ConstantVal(Name.parse("f"), Nil, arrow(Expr.const("A"), Expr.const("A"))), false
      )))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("a"), Nil, Expr.const("A")), false)))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("h"), Nil, prop), false)))
    val tc = new TypeChecker(env, KernelProfile.v4_35)
    val one = Level.one
    val a   = Expr.const("a")
    val mk  = Expr.mkAppN(Expr.Const(Names.quotMk, List(one)), Seq(Expr.const("A"), Expr.const("rel"), a))
    // Quot.lift.{1,1} A rel A f h (Quot.mk.{1} A rel a)  ==>  f a
    val lift = Expr.mkAppN(
      Expr.Const(Names.quotLift, List(one, one)),
      Seq(Expr.const("A"), Expr.const("rel"), Expr.const("A"), Expr.const("f"), Expr.const("h"), mk)
    )
    assertEquals(tc.whnf(lift), Expr.App(Expr.const("f"), a))
    assert(tc.isDefEq(lift, Expr.App(Expr.const("f"), a)))
  }

  test("Quot.ind reduces on Quot.mk") {
    val env = Quot.add(envWithEq)
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("A"), Nil, Expr.Sort(Level.one)), false)))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(
        ConstantVal(Name.parse("rel"), Nil, arrow(Expr.const("A"), arrow(Expr.const("A"), prop))), false
      )))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("a"), Nil, Expr.const("A")), false)))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("mot"), Nil, prop), false)))
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("pf"), Nil, prop), false)))
    val tc = new TypeChecker(env, KernelProfile.v4_35)
    val one = Level.one
    val a   = Expr.const("a")
    val mk  = Expr.mkAppN(Expr.Const(Names.quotMk, List(one)), Seq(Expr.const("A"), Expr.const("rel"), a))
    val ind = Expr.mkAppN(
      Expr.Const(Names.quotInd, List(one)),
      Seq(Expr.const("A"), Expr.const("rel"), Expr.const("mot"), Expr.const("pf"), mk)
    )
    assertEquals(tc.whnf(ind), Expr.App(Expr.const("pf"), a))
  }

  test("quotient reduction is off until the package is installed") {
    val env = envWithEq
      .addCore(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("A"), Nil, Expr.Sort(Level.one)), false)))
    assert(!env.quotInitialized)
    val tc = new TypeChecker(env, KernelProfile.v4_35)
    val stuck = Expr.mkAppN(Expr.Const(Names.quotLift, List(Level.one, Level.one)), Seq(Expr.const("A")))
    assertEquals(tc.whnfCore(stuck), stuck)
  }

  test("QuotDecl installs the package through the driver") {
    val dc  = new DeclarationChecker(KernelProfile.v4_35)
    val env = dc.add(envWithEq, Declaration.QuotDecl)
    assert(env.quotInitialized)
    Names.quotNames.foreach(n => assert(env.contains(n), clue(n.toString)))
  }
