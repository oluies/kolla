package kolla.kernel

class TypeCheckerSuite extends munit.FunSuite:

  val u    = Name.mkSimple("u")
  val lu   = Level.Param(u)
  val x    = Name.mkSimple("x")
  val a    = Name.mkSimple("a")
  val prop = Expr.Sort(Level.zero)
  val type0 = Expr.Sort(Level.one)

  def cv(n: String, lps: List[Name], t: Expr) = ConstantVal(Name.parse(n), lps, t)
  def ax(n: String, t: Expr, lps: List[Name] = Nil) =
    ConstantInfo.AxiomInfo(AxiomVal(cv(n, lps, t), false))
  def arrow(d: Expr, c: Expr) = Expr.ForallE(Name.mkSimple("_"), d, c, BinderInfo.Default)

  val nat     = Expr.const("Nat")
  val natZero = Expr.const("Nat.zero")
  val natSucc = Expr.const("Nat.succ")
  def lit(n: Int): Expr = Expr.natLit(n)

  /** `Nat`, `Bool`, a two-field structure `P`, a unit-like `U : Prop`, and a
    * couple of definitions.
    */
  val env: Environment =
    val infos = List(
      ConstantInfo.InductInfo(InductiveVal(
        cv("Nat", Nil, type0), 0, 0, List(Name.parse("Nat")),
        List(Name.parse("Nat.zero"), Name.parse("Nat.succ")), 0, true, false, false
      )),
      ConstantInfo.CtorInfo(ConstructorVal(cv("Nat.zero", Nil, nat), Name.parse("Nat"), 0, 0, 0, false)),
      ConstantInfo.CtorInfo(ConstructorVal(cv("Nat.succ", Nil, arrow(nat, nat)), Name.parse("Nat"), 1, 0, 1, false)),
      ConstantInfo.InductInfo(InductiveVal(
        cv("Bool", Nil, type0), 0, 0, List(Name.parse("Bool")),
        List(Name.parse("Bool.false"), Name.parse("Bool.true")), 0, false, false, false
      )),
      ConstantInfo.CtorInfo(ConstructorVal(cv("Bool.false", Nil, Expr.const("Bool")), Name.parse("Bool"), 0, 0, 0, false)),
      ConstantInfo.CtorInfo(ConstructorVal(cv("Bool.true", Nil, Expr.const("Bool")), Name.parse("Bool"), 1, 0, 0, false)),
      // structure P where fst : Nat; snd : Nat
      ConstantInfo.InductInfo(InductiveVal(
        cv("P", Nil, type0), 0, 0, List(Name.parse("P")), List(Name.parse("P.mk")), 0, false, false, false
      )),
      ConstantInfo.CtorInfo(ConstructorVal(
        cv("P.mk", Nil, arrow(nat, arrow(nat, Expr.const("P")))), Name.parse("P"), 0, 0, 2, false
      )),
      // structure U : Prop where (no fields)
      ConstantInfo.InductInfo(InductiveVal(
        cv("U", Nil, prop), 0, 0, List(Name.parse("U")), List(Name.parse("U.mk")), 0, false, false, false
      )),
      ConstantInfo.CtorInfo(ConstructorVal(cv("U.mk", Nil, Expr.const("U")), Name.parse("U"), 0, 0, 0, false)),
      ax("p", prop),
      // `Sort (imax 1 0)`: normalizes to Prop without being syntactically Prop.
      ax("q", Expr.Sort(Level.IMax(Level.one, Level.zero))),
      ax("pa", Expr.const("p")),
      ax("pb", Expr.const("p")),
      // def two : Nat := Nat.succ (Nat.succ Nat.zero)
      ConstantInfo.DefnInfo(DefinitionVal(
        cv("two", Nil, nat), Expr.App(natSucc, Expr.App(natSucc, natZero)),
        ReducibilityHints.Regular(1), DefinitionSafety.Safe, List(Name.parse("two"))
      )),
      // def idNat : Nat -> Nat := fun a => a
      ConstantInfo.DefnInfo(DefinitionVal(
        cv("idNat", Nil, arrow(nat, nat)), Expr.Lam(a, nat, Expr.BVar(0), BinderInfo.Default),
        ReducibilityHints.Regular(1), DefinitionSafety.Safe, List(Name.parse("idNat"))
      )),
      ax("Nat.add", arrow(nat, arrow(nat, nat))),
      ax("Nat.mul", arrow(nat, arrow(nat, nat))),
      ax("Nat.sub", arrow(nat, arrow(nat, nat))),
      ax("Nat.div", arrow(nat, arrow(nat, nat))),
      ax("Nat.mod", arrow(nat, arrow(nat, nat))),
      ax("Nat.gcd", arrow(nat, arrow(nat, nat))),
      ax("Nat.pow", arrow(nat, arrow(nat, nat))),
      ax("Nat.beq", arrow(nat, arrow(nat, Expr.const("Bool")))),
      ax("Nat.ble", arrow(nat, arrow(nat, Expr.const("Bool")))),
      ax("Nat.land", arrow(nat, arrow(nat, nat))),
      ax("Nat.lor", arrow(nat, arrow(nat, nat))),
      ax("Nat.xor", arrow(nat, arrow(nat, nat))),
      ax("Nat.shiftLeft", arrow(nat, arrow(nat, nat))),
      ax("Nat.shiftRight", arrow(nat, arrow(nat, nat)))
    )
    infos.foldLeft(Environment.empty)((e, i) => e.addCore(i))

  def tc(profile: KernelProfile = KernelProfile.v4_35): TypeChecker = new TypeChecker(env, profile)

  // -------------------------------------------------------------- inferType

  test("inferType of the basic forms") {
    val t = tc()
    assertEquals(t.infer(Expr.Sort(Level.zero)), Expr.Sort(Level.one))
    assertEquals(t.infer(Expr.Sort(lu)), Expr.Sort(Level.Succ(lu)))
    assertEquals(t.infer(natZero), nat)
    assertEquals(t.infer(lit(7)), nat)
    assertEquals(t.infer(Expr.strLit("hi")), Expr.const("String"))
    assertEquals(t.infer(Expr.App(natSucc, natZero)), nat)
    assertEquals(t.infer(Expr.Lam(a, nat, Expr.BVar(0), BinderInfo.Default)), arrow(nat, nat))
    assertEquals(t.infer(arrow(nat, nat)), type0)
    assertEquals(t.infer(Expr.LetE(a, nat, natZero, Expr.BVar(0), false)), nat)
    assertEquals(t.infer(Expr.Proj(Name.parse("P"), 0, Expr.mkAppN(Expr.const("P.mk"), Seq(lit(1), lit(2))))), nat)
  }

  test("check enforces the declared universe parameters") {
    assertEquals(tc().check(Expr.Sort(lu), List(u)), Expr.Sort(Level.Succ(lu)))
    // A fresh checker per declaration: the infer cache is keyed on the term, not
    // on the universe parameters in scope, exactly as `m_infer_type` is.
    val e = intercept[KernelException](tc().check(Expr.Sort(lu), Nil))
    assert(clue(e.getMessage).contains("undefined universe level parameter"))
  }

  test("inferType rejects what the kernel rejects") {
    val t = tc()
    assertEquals(intercept[KernelException](t.infer(Expr.BVar(0))).kind, ExceptionKind.Other)
    assertEquals(
      intercept[KernelException](t.infer(Expr.MVar(x))).kind,
      ExceptionKind.DeclarationHasMetavars
    )
    assertEquals(intercept[KernelException](t.infer(Expr.const("nope"))).kind, ExceptionKind.UnknownConstant)
    // Too many universe arguments.
    assert(clue(intercept[KernelException](t.infer(Expr.Const(Name.parse("Nat"), List(Level.zero)))).getMessage)
      .contains("incorrect number of universe levels"))
    // Applying a non-function.
    assertEquals(
      intercept[KernelException](t.check(Expr.App(natZero, natZero))).kind,
      ExceptionKind.FunctionExpected
    )
    // Argument of the wrong type.
    assertEquals(
      intercept[KernelException](t.check(Expr.App(natSucc, Expr.const("Bool.true")))).kind,
      ExceptionKind.AppTypeMismatch
    )
    // A binder whose domain is not a type.
    assertEquals(
      intercept[KernelException](t.check(Expr.Lam(a, natZero, natZero, BinderInfo.Default))).kind,
      ExceptionKind.TypeExpected
    )
  }

  test("a rejected application records a defeq trace") {
    val t = tc()
    val e = intercept[KernelException](t.check(Expr.App(natSucc, Expr.const("Bool.true"))))
    assert(e.trace.nonEmpty)
    assert(clue(e.getMessage).contains("defeq trace"))
  }

  // ---------------------------------------------------------------- whnf

  test("whnf performs beta, zeta and delta") {
    val t = tc()
    assertEquals(t.whnf(Expr.App(Expr.Lam(a, nat, Expr.BVar(0), BinderInfo.Default), lit(3))), lit(3))
    assertEquals(t.whnf(Expr.LetE(a, nat, lit(4), Expr.BVar(0), false)), lit(4))
    // Delta-unfolding exposes `Nat.succ (Nat.succ Nat.zero)`, which `reduce_nat`
    // then folds into a literal.
    assertEquals(t.whnf(Expr.const("two")), lit(2))
    assertEquals(t.whnfCore(Expr.const("two")), Expr.const("two"))
    assertEquals(t.whnf(Expr.App(Expr.const("idNat"), lit(5))), lit(5))
  }

  test("whnf reduces projections") {
    val t = tc()
    val p = Expr.mkAppN(Expr.const("P.mk"), Seq(lit(1), lit(2)))
    assertEquals(t.whnf(Expr.Proj(Name.parse("P"), 0, p)), lit(1))
    assertEquals(t.whnf(Expr.Proj(Name.parse("P"), 1, p)), lit(2))
    // Out of range stays stuck rather than reducing.
    val stuck = Expr.Proj(Name.parse("P"), 5, p)
    assertEquals(t.whnf(stuck), stuck)
  }

  test("whnf evaluates the Nat literal extensions") {
    val t = tc()
    def bin(op: String, i: Int, j: Int): Expr = Expr.mkAppN(Expr.const(op), Seq(lit(i), lit(j)))
    assertEquals(t.whnf(Expr.App(natSucc, lit(4))), lit(5))
    assertEquals(t.whnf(bin("Nat.add", 2, 3)), lit(5))
    assertEquals(t.whnf(bin("Nat.sub", 3, 5)), lit(0))
    assertEquals(t.whnf(bin("Nat.mul", 3, 4)), lit(12))
    assertEquals(t.whnf(bin("Nat.div", 7, 2)), lit(3))
    assertEquals(t.whnf(bin("Nat.div", 7, 0)), lit(0))
    assertEquals(t.whnf(bin("Nat.mod", 7, 2)), lit(1))
    assertEquals(t.whnf(bin("Nat.mod", 7, 0)), lit(7))
    assertEquals(t.whnf(bin("Nat.gcd", 12, 18)), lit(6))
    assertEquals(t.whnf(bin("Nat.pow", 2, 10)), lit(1024))
    assertEquals(t.whnf(bin("Nat.land", 12, 10)), lit(8))
    assertEquals(t.whnf(bin("Nat.lor", 12, 10)), lit(14))
    assertEquals(t.whnf(bin("Nat.xor", 12, 10)), lit(6))
    assertEquals(t.whnf(bin("Nat.shiftLeft", 3, 4)), lit(48))
    assertEquals(t.whnf(bin("Nat.shiftRight", 48, 4)), lit(3))
    assertEquals(t.whnf(bin("Nat.beq", 3, 3)), Expr.const("Bool.true"))
    assertEquals(t.whnf(bin("Nat.beq", 3, 4)), Expr.const("Bool.false"))
    assertEquals(t.whnf(bin("Nat.ble", 3, 4)), Expr.const("Bool.true"))
    assertEquals(t.whnf(bin("Nat.ble", 4, 3)), Expr.const("Bool.false"))
    // Nat.zero counts as a literal.
    assertEquals(t.whnf(Expr.mkAppN(Expr.const("Nat.add"), Seq(natZero, lit(2)))), lit(2))
  }

  test("the Nat numeral size limit is enforced only where the profile says so") {
    val small = KernelProfile.v4_35.copy(natMaxSizeBytes = Some(8L))
    val t     = new TypeChecker(env, small)
    val big   = Expr.mkAppN(Expr.const("Nat.pow"), Seq(lit(2), lit(10000)))
    assert(clue(intercept[KernelException](t.whnf(big)).getMessage).contains("Nat.pow"))
    val unbounded = new TypeChecker(env, KernelProfile.v4_35.copy(natMaxSizeBytes = None))
    assertEquals(unbounded.whnf(big), Expr.natLit(BigInt(2).pow(10000)))
  }

  // --------------------------------------------------------------- isDefEq

  test("isDefEq basics") {
    val t = tc()
    assert(t.isDefEq(nat, nat))
    assert(t.isDefEq(Expr.const("two"), lit(2)))
    assert(t.isDefEq(lit(2), Expr.const("two")))
    assert(!t.isDefEq(Expr.const("two"), lit(3)))
    assert(t.isDefEq(Expr.Sort(Level.Max(Level.zero, Level.one)), Expr.Sort(Level.one)))
    assert(!t.isDefEq(nat, Expr.const("Bool")))
  }

  test("isDefEq uses the Nat successor offset") {
    val t = tc()
    assert(t.isDefEq(Expr.App(natSucc, lit(2)), lit(3)))
    assert(t.isDefEq(lit(3), Expr.App(natSucc, lit(2))))
    assert(t.isDefEq(natZero, lit(0)))
    assert(!t.isDefEq(Expr.App(natSucc, lit(2)), lit(4)))
  }

  test("isDefEq does eta for functions") {
    val t = tc()
    val eta = Expr.Lam(a, nat, Expr.App(natSucc, Expr.BVar(0)), BinderInfo.Default)
    assert(t.isDefEq(eta, natSucc))
    assert(t.isDefEq(natSucc, eta))
  }

  test("isDefEq does eta for structures") {
    val t = tc()
    val p = Expr.mkAppN(Expr.const("P.mk"), Seq(lit(1), lit(2)))
    val expanded = Expr.mkAppN(
      Expr.const("P.mk"),
      Seq(Expr.Proj(Name.parse("P"), 0, p), Expr.Proj(Name.parse("P"), 1, p))
    )
    assert(t.isDefEq(p, expanded))
  }

  test("isDefEq is proof irrelevant in Prop") {
    val t = tc()
    assert(t.isDefEq(Expr.const("pa"), Expr.const("pb")))
    assert(t.isDefEq(Expr.const("pb"), Expr.const("pa")))
    // Not a Prop, so no irrelevance.
    assert(!t.isDefEq(lit(1), lit(2)))
  }

  test("isDefEq accepts unit-like types") {
    val t = tc()
    val u1 = Expr.const("U.mk")
    assert(t.isDefEq(u1, u1))
    assert(t.isProp(Expr.const("U")))
  }

  test("isProp follows the profile") {
    // `imax 1 0` normalizes to zero without being syntactically zero. The smart
    // constructor collapses it, so the raw node is needed; only a hand-made or
    // mutated term can contain one, which is what v4.35's change defends against.
    val odd = Level.IMax(Level.one, Level.zero)
    assert(Level.normalizesToZero(odd))
    assert(!odd.isZero)
    assert(new TypeChecker(env, KernelProfile.v4_35).isProp(Expr.const("q")))
    assert(!new TypeChecker(env, KernelProfile.v4_27).isProp(Expr.const("q")))
    // The sort itself is not a proposition under either profile.
    assert(!new TypeChecker(env, KernelProfile.v4_35).isProp(Expr.Sort(odd)))
  }

  test("string literal expansion uses the profile's constructor") {
    val t35 = new TypeChecker(env, KernelProfile.v4_35)
    val t25 = new TypeChecker(env, KernelProfile.v4_25)
    val lit0 = Expr.strLit("")
    assertEquals(
      Expr.constName(Expr.getAppFn(ExprOps.stringLitToConstructor("", KernelProfile.v4_35))),
      Some(Name.parse("String.ofList"))
    )
    assertEquals(
      Expr.constName(Expr.getAppFn(ExprOps.stringLitToConstructor("", KernelProfile.v4_25))),
      Some(Name.parse("String.mk"))
    )
    assert(t35.isDefEq(lit0, lit0))
    assert(t25.isDefEq(lit0, lit0))
  }

  test("the step budget bounds a runaway reduction") {
    val t = new TypeChecker(env, KernelProfile.v4_35, maxSteps = 50L)
    val deep = (0 until 500).foldLeft(natZero: Expr)((e, _) => Expr.App(natSucc, e))
    assertEquals(intercept[KernelException](t.whnf(deep)).kind, ExceptionKind.DeepRecursion)
  }

  test("deep terms do not overflow the stack") {
    val t = tc()
    val depth = 20000
    val deep  = (0 until depth).foldLeft(natZero: Expr)((e, _) => Expr.App(natSucc, e))
    assertEquals(t.whnf(deep), lit(depth))
    assertEquals(t.infer(deep), nat)
    assert(t.isDefEq(deep, lit(depth)))
    val nested = (0 until depth).foldLeft(natZero: Expr)((e, _) =>
      Expr.App(Expr.Lam(a, nat, Expr.BVar(0), BinderInfo.Default), e)
    )
    assertEquals(t.whnf(nested), natZero)
  }
