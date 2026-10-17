package kolla.kernel

class InductiveSuite extends munit.FunSuite:

  val type0 = Expr.Sort(Level.one)
  val prop  = Expr.Sort(Level.zero)
  val u     = Name.mkSimple("u")
  val lu    = Level.Param(u)
  def arrow(d: Expr, c: Expr) = Expr.ForallE(Name.mkSimple("a"), d, c, BinderInfo.Default)
  def pi(n: String, d: Expr, b: Expr) = Expr.ForallE(Name.mkSimple(n), d, b, BinderInfo.Default)

  // An enum case constructor widens to `Declaration`, so match it back.
  def runInd(d: Declaration, env: Environment = Environment.empty, nnested: Int = 0): InductiveResult =
    d match
      case i: Declaration.InductDecl => new InductiveChecker(env, i, KernelProfile.v4_35, nnested).run()
      case other                     => fail(s"expected an inductive declaration, got $other")

  val natDecl = Declaration.InductDecl(
    Nil, 0,
    List(InductiveType(
      Name.parse("Nat"), type0,
      List(
        Constructor(Name.parse("Nat.zero"), Expr.const("Nat")),
        // The argument is named `n`, as Lean's own `Nat.succ` names it, so the
        // generated induction hypothesis is `n_ih`.
        Constructor(Name.parse("Nat.succ"), pi("n", Expr.const("Nat"), Expr.const("Nat")))
      )
    )),
    false
  )

  test("a simple recursive type") {
    val r = runInd(natDecl)
    assertEquals(r.inductives.length, 1)
    val iv = r.inductives.head
    assertEquals(iv.numParams, 0)
    assertEquals(iv.numIndices, 0)
    assert(iv.isRec)
    assert(!iv.isReflexive)
    assertEquals(iv.ctors.map(_.toString), List("Nat.zero", "Nat.succ"))
    assertEquals(r.constructors.map(c => (c.toConstantVal.name.toString, c.cidx, c.numFields)),
      List(("Nat.zero", 0, 0), ("Nat.succ", 1, 1)))
    assertEquals(r.resultLevel, Level.one)
    assert(r.env.contains(Name.parse("Nat")))
    assert(r.env.contains(Name.parse("Nat.succ")))
  }

  test("a non-recursive type with parameters and indices") {
    // inductive V (A : Type) : Nat -> Type where mk : (n : Nat) -> V A n
    val nat = runInd(natDecl)
    val vDecl = Declaration.InductDecl(
      Nil, 1,
      List(InductiveType(
        Name.parse("V"),
        pi("A", type0, arrow(Expr.const("Nat"), type0)),
        List(Constructor(
          Name.parse("V.mk"),
          pi("A", type0, pi("n", Expr.const("Nat"),
            Expr.mkAppN(Expr.const("V"), Seq(Expr.BVar(1), Expr.BVar(0)))))
        ))
      )),
      false
    )
    val r = runInd(vDecl, nat.env)
    val iv = r.inductives.head
    assertEquals(iv.numParams, 1)
    assertEquals(iv.numIndices, 1)
    assert(!iv.isRec)
    assertEquals(r.constructors.head.numParams, 1)
    assertEquals(r.constructors.head.numFields, 1)
  }

  test("a reflexive type") {
    // inductive R where mk : (Nat -> R) -> R
    val nat = runInd(natDecl)
    val rDecl = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("R"), type0,
        List(Constructor(Name.parse("R.mk"), arrow(arrow(Expr.const("Nat"), Expr.const("R")), Expr.const("R"))))
      )),
      false
    )
    val r = runInd(rDecl, nat.env)
    assert(r.inductives.head.isRec)
    assert(r.inductives.head.isReflexive)
  }

  test("a non-positive occurrence is rejected") {
    // inductive Bad where mk : (Bad -> Bad) -> Bad
    val bad = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("Bad"), type0,
        List(Constructor(Name.parse("Bad.mk"), arrow(arrow(Expr.const("Bad"), Expr.const("Bad")), Expr.const("Bad"))))
      )),
      false
    )
    val e = intercept[KernelException](runInd(bad))
    assert(clue(e.getMessage).contains("non positive occurrence"))
  }

  test("an unsafe declaration skips the positivity check") {
    val bad = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("Bad"), type0,
        List(Constructor(Name.parse("Bad.mk"), arrow(arrow(Expr.const("Bad"), Expr.const("Bad")), Expr.const("Bad"))))
      )),
      true
    )
    val r = runInd(bad)
    assert(r.inductives.head.isUnsafe)
    assert(r.constructors.head.isUnsafe)
  }

  test("a field in too large a universe is rejected") {
    // inductive Small : Type where mk : Type 1 -> Small   (Type 1 does not fit)
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("Small"), type0,
        List(Constructor(Name.parse("Small.mk"), arrow(Expr.Sort(Level.ofNat(2)), Expr.const("Small"))))
      )),
      false
    )
    assert(clue(intercept[KernelException](runInd(d)).getMessage).contains("too big"))
  }

  test("an inductive predicate may quantify over any universe") {
    // inductive P : Prop where mk : Type 5 -> P
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("P"), prop,
        List(Constructor(Name.parse("P.mk"), arrow(Expr.Sort(Level.ofNat(5)), Expr.const("P"))))
      )),
      false
    )
    val r = runInd(d)
    assertEquals(r.resultLevel, Level.zero)
    assertEquals(r.constructors.head.numFields, 1)
  }

  test("a duplicate constructor name is rejected") {
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("D"), type0,
        List(
          Constructor(Name.parse("D.mk"), Expr.const("D")),
          Constructor(Name.parse("D.mk"), Expr.const("D"))
        )
      )),
      false
    )
    assert(clue(intercept[KernelException](runInd(d)).getMessage).contains("duplicate constructor"))
  }

  test("a wrong return type is rejected") {
    val nat = runInd(natDecl)
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("W"), type0,
        List(Constructor(Name.parse("W.mk"), Expr.const("Nat")))
      )),
      false
    )
    assert(clue(intercept[KernelException](runInd(d, nat.env)).getMessage).contains("invalid return type"))
  }

  test("a wrong parameter count is rejected") {
    val d = Declaration.InductDecl(
      Nil, 2,
      List(InductiveType(Name.parse("Z"), type0, Nil)),
      false
    )
    assert(clue(intercept[KernelException](runInd(d)).getMessage).contains("number of parameters mismatch"))
  }

  test("mutual types must share their parameters and universe") {
    val mismatched = Declaration.InductDecl(
      Nil, 1,
      List(
        InductiveType(Name.parse("A"), pi("x", type0, type0), Nil),
        InductiveType(Name.parse("B"), pi("x", prop, type0), Nil)
      ),
      false
    )
    assert(clue(intercept[KernelException](runInd(mismatched)).getMessage).contains("parameters of all inductive"))

    val differentUniverse = Declaration.InductDecl(
      Nil, 0,
      List(
        InductiveType(Name.parse("A"), type0, Nil),
        InductiveType(Name.parse("B"), Expr.Sort(Level.ofNat(2)), Nil)
      ),
      false
    )
    assert(clue(intercept[KernelException](runInd(differentUniverse)).getMessage)
      .contains("must live in the same universe"))
  }

  test("a mutual block shares its derived fields") {
    // mutual inductive A where mk : B -> A | B where mk : A -> B
    val d = Declaration.InductDecl(
      Nil, 0,
      List(
        InductiveType(Name.parse("A"), type0, List(Constructor(Name.parse("A.mk"), arrow(Expr.const("B"), Expr.const("A"))))),
        InductiveType(Name.parse("B"), type0, List(Constructor(Name.parse("B.mk"), arrow(Expr.const("A"), Expr.const("B")))))
      ),
      false
    )
    val r = runInd(d)
    assertEquals(r.inductives.length, 2)
    assertEquals(r.inductives.map(_.all.map(_.toString)), List(List("A", "B"), List("A", "B")))
    r.inductives.foreach(i => assert(i.isRec, clue(i.toConstantVal.name.toString)))
    assertEquals(r.constructors.map(c => (c.induct.toString, c.cidx)), List(("A", 0), ("B", 0)))
  }

  test("a declaration with free variables or metavariables is rejected") {
    val withFvar = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(Name.parse("F"), Expr.FVar(Name.mkSimple("v")), Nil)),
      false
    )
    assertEquals(
      intercept[KernelException](runInd(withFvar)).kind,
      ExceptionKind.DeclarationHasFreeVars
    )
  }

  test("the recursor for a simple recursive type") {
    val r = runInd(natDecl)
    assertEquals(r.recursors.length, 1)
    val rv = r.recursors.head
    assertEquals(rv.toConstantVal.name, Name.parse("Nat.rec"))
    // A fresh elimination universe is added in front of the declaration's.
    assertEquals(rv.toConstantVal.levelParams.map(_.toString), List("u"))
    assertEquals(r.elimLevel, Level.Param(Name.mkSimple("u")))
    assertEquals(rv.numParams, 0)
    assertEquals(rv.numIndices, 0)
    assertEquals(rv.numMotives, 1)
    assertEquals(rv.numMinors, 2)
    assert(!rv.k)
    assertEquals(rv.majorIdx, 3)
    assertEquals(rv.rules.map(_.ctor.toString), List("Nat.zero", "Nat.succ"))
    assertEquals(rv.rules.map(_.nfields), List(0, 1))
    // The induction hypothesis is named `<arg>_ih`, as `append_after` produces.
    val succRule = rv.rules.find(_.ctor == Name.parse("Nat.succ")).get
    assert(Pretty.expr(succRule.rhs, 400).contains("n_ih"), clue(Pretty.expr(succRule.rhs, 400)))
    assert(r.env.contains(Name.parse("Nat.rec")))
    // The generated recursor is well typed and its rules are type-preserving;
    // `check_recursors` ran as part of `run` under the v4.35 profile.
    val tc = new TypeChecker(r.env, KernelProfile.v4_35)
    tc.check(rv.toConstantVal.tpe, rv.toConstantVal.levelParams)
  }

  test("the elimination universe collides with a declared parameter") {
    // The datatype already uses `u`, so the recursor must pick another name.
    val d = Declaration.InductDecl(
      List(u), 0,
      List(InductiveType(
        Name.parse("Box"), Expr.Sort(Level.Succ(lu)),
        List(Constructor(Name.parse("Box.mk"), arrow(Expr.Sort(lu), Expr.Const(Name.parse("Box"), List(lu)))))
      )),
      false
    )
    val r = runInd(d)
    // `name::append_after(unsigned)` separates the index with an underscore, so
    // the fresh universe is `u_1`, which is what Lean's own exports contain.
    assertEquals(r.elimLevel, Level.Param(Name.mkSimple("u_1")))
    assertEquals(r.recursors.head.toConstantVal.levelParams.map(_.toString), List("u_1", "u"))
  }

  test("an inductive predicate eliminates only into Prop") {
    // inductive Two : Prop where a : Two | b : Two
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("Two"), prop,
        List(
          Constructor(Name.parse("Two.a"), Expr.const("Two")),
          Constructor(Name.parse("Two.b"), Expr.const("Two"))
        )
      )),
      false
    )
    val r = runInd(d)
    // More than one constructor, so the recursor cannot leave Prop.
    assertEquals(r.elimLevel, Level.zero)
    assertEquals(r.recursors.head.toConstantVal.levelParams, Nil)
    assert(!r.kTarget)
  }

  test("an empty inductive predicate eliminates anywhere") {
    val d = Declaration.InductDecl(Nil, 0, List(InductiveType(Name.parse("Empty0"), prop, Nil)), false)
    val r = runInd(d)
    assert(r.elimLevel.isParam)
    assertEquals(r.recursors.head.numMinors, 0)
    assert(!r.kTarget)
  }

  test("a field-less single-constructor predicate is a K target") {
    // inductive K0 : Prop where mk : K0
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(Name.parse("K0"), prop, List(Constructor(Name.parse("K0.mk"), Expr.const("K0"))))),
      false
    )
    val r = runInd(d)
    assert(r.kTarget)
    assertEquals(r.recursors.head.k, true)
    // One constructor with no fields, so it eliminates anywhere.
    assert(r.elimLevel.isParam)
  }

  test("a single-constructor predicate with a field is not a K target") {
    val nat = runInd(natDecl)
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("K1"), prop,
        List(Constructor(Name.parse("K1.mk"), arrow(Expr.const("Nat"), Expr.const("K1"))))
      )),
      false
    )
    val r = runInd(d, nat.env)
    assert(!r.kTarget)
    // The field is not in Prop and does not occur in the result, so elimination
    // is restricted to Prop.
    assertEquals(r.elimLevel, Level.zero)
  }

  test("a mutual block gets one recursor per type sharing the motives") {
    val d = Declaration.InductDecl(
      Nil, 0,
      List(
        InductiveType(Name.parse("A"), type0, List(Constructor(Name.parse("A.mk"), arrow(Expr.const("B"), Expr.const("A"))))),
        InductiveType(Name.parse("B"), type0, List(Constructor(Name.parse("B.mk"), arrow(Expr.const("A"), Expr.const("B")))))
      ),
      false
    )
    val r = runInd(d)
    assertEquals(r.recursors.length, 2)
    assertEquals(r.recursors.map(_.toConstantVal.name.toString), List("A.rec", "B.rec"))
    r.recursors.foreach { rv =>
      assertEquals(rv.numMotives, 2, clue(rv.toConstantVal.name.toString))
      assertEquals(rv.numMinors, 2, clue(rv.toConstantVal.name.toString))
      assertEquals(rv.all.map(_.toString), List("A", "B"))
    }
    // Mutual predicates would be Prop-only, but these live in Type.
    assert(r.elimLevel.isParam)
  }

  test("the recursor rules reduce") {
    val r  = runInd(natDecl)
    val tc = new TypeChecker(r.env, KernelProfile.v4_35)
    val natC = Expr.const("Nat")
    val zero = Expr.const("Nat.zero")
    val one  = Level.one
    // Nat.rec.{1} (motive := fun _ => Nat) zero (fun n ih => n) Nat.zero  ==>  zero
    val motive = Expr.Lam(Name.mkSimple("t"), natC, natC, BinderInfo.Default)
    val minorZ = zero
    val minorS = Expr.Lam(Name.mkSimple("n"), natC,
      Expr.Lam(Name.mkSimple("ih"), natC, Expr.BVar(1), BinderInfo.Default), BinderInfo.Default)
    def rec(major: Expr) = Expr.mkAppN(
      Expr.Const(Name.parse("Nat.rec"), List(one)), Seq(motive, minorZ, minorS, major)
    )
    assertEquals(tc.whnf(rec(zero)), zero)
    // `whnf` folds `Nat.succ` applications into literals, and the major premise
    // is expanded back with `nat_lit_to_constructor`, so the result is a literal.
    val two = Expr.App(Expr.const("Nat.succ"), Expr.App(Expr.const("Nat.succ"), zero))
    assertEquals(tc.whnf(two), Expr.natLit(2))
    assertEquals(tc.whnf(rec(two)), Expr.natLit(1))
    assert(tc.isDefEq(rec(two), Expr.App(Expr.const("Nat.succ"), zero)))
  }

  test("a non-uniform occurrence of a declared datatype is rejected") {
    // inductive T (A : Type) where mk : T Nat -> T A
    // The occurrence `T Nat` is applied to something other than the parameter.
    val nat = runInd(natDecl)
    val d = Declaration.InductDecl(
      Nil, 1,
      List(InductiveType(
        Name.parse("T"), pi("A", type0, type0),
        List(Constructor(
          Name.parse("T.mk"),
          pi("A", type0, pi("_", Expr.App(Expr.const("T"), Expr.const("Nat")),
            Expr.App(Expr.const("T"), Expr.BVar(1))))
        ))
      )),
      false
    )
    val e = intercept[KernelException](runInd(d, nat.env))
    assert(clue(e.getMessage).contains("invalid occurrence of a datatype being declared"))

    // Earlier releases do not have the check, so it must be profile-gated.
    val e2 = intercept[KernelException](
      new InductiveChecker(nat.env, d.asInstanceOf[Declaration.InductDecl], KernelProfile.v4_27, 0).run()
    )
    // It still fails, but on a later check rather than this one.
    assert(!e2.getMessage.contains("invalid occurrence of a datatype being declared"), clue(e2.getMessage))
  }

  test("a uniform occurrence is accepted and over-application descends") {
    // inductive T (A : Type) where mk : A -> T A
    val d = Declaration.InductDecl(
      Nil, 1,
      List(InductiveType(
        Name.parse("T"), pi("A", type0, type0),
        List(Constructor(
          Name.parse("T.mk"),
          pi("A", type0, pi("a", Expr.BVar(0), Expr.App(Expr.const("T"), Expr.BVar(1))))
        ))
      )),
      false
    )
    val r = runInd(d)
    assertEquals(r.inductives.head.numParams, 1)
    // Checking the declaration directly must not raise either.
    InductiveChecker.checkUniformIndOccs(d.asInstanceOf[Declaration.InductDecl])
  }

  test("the reserved nested prefix is rejected in user input") {
    val auxName = Names.nested.str("List")
    val d = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("U"), type0,
        List(Constructor(Name.parse("U.mk"), arrow(Expr.const(auxName), Expr.const("U"))))
      )),
      false
    )
    assert(clue(intercept[KernelException](runInd(d)).getMessage).contains("reserved prefix"))

    // A projection's structure name is resolved the same way.
    val viaProj = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(
        Name.parse("V"), type0,
        List(Constructor(
          Name.parse("V.mk"),
          arrow(Expr.Proj(auxName, 0, Expr.const("U")), Expr.const("V"))
        ))
      )),
      false
    )
    assert(clue(intercept[KernelException](runInd(viaProj)).getMessage).contains("reserved prefix"))

    // The check applies to the inductive's own type too.
    val viaType = Declaration.InductDecl(
      Nil, 0, List(InductiveType(Name.parse("W"), Expr.const(auxName), Nil)), false
    )
    assert(clue(intercept[KernelException](runInd(viaType)).getMessage).contains("reserved prefix"))
  }

  test("a nested block is refused rather than silently accepted") {
    val e = intercept[KernelException](runInd(natDecl, Environment.empty, nnested = 1))
    assert(clue(e.getMessage).contains("nested inductive types are not implemented yet"))
    // numNested = 0 is the ordinary path.
    assertEquals(runInd(natDecl, Environment.empty, nnested = 0).inductives.head.numNested, 0)
  }

  test("declarationOf rebuilds a block from exported entries") {
    val r = runInd(natDecl)
    val rebuilt = InductiveChecker.declarationOf(r.inductives, r.constructors)
    assertEquals(rebuilt.numParams, 0)
    assertEquals(rebuilt.types.length, 1)
    assertEquals(rebuilt.types.head.ctors.map(_.name.toString), List("Nat.zero", "Nat.succ"))
    // Round-trips through the checker.
    val again = runInd(rebuilt)
    InductiveChecker.validate(r.inductives, r.constructors, again.inductives, again.constructors)
  }

  test("declarationOf rejects an inconsistent block") {
    val r = runInd(natDecl)
    val missing = InductiveChecker.declarationOf(r.inductives, r.constructors)
    assert(clue(intercept[KernelException](
      InductiveChecker.declarationOf(r.inductives, Nil)
    ).getMessage).contains("does not declare it"))
  }
