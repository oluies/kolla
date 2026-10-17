package kolla.kernel

import kolla.kernel.Generators.given
import org.scalacheck.Prop.forAll

class ExprOpsSuite extends munit.ScalaCheckSuite:

  val nat   = Expr.const("Nat")
  val x     = Name.mkSimple("x")
  val y     = Name.mkSimple("y")
  val u     = Name.mkSimple("u")
  val lu    = Level.Param(u)
  def bv(i: Int): Expr = Expr.BVar(i)
  def lam(b: Expr): Expr = Expr.Lam(x, nat, b, BinderInfo.Default)
  def pi(b: Expr): Expr  = Expr.ForallE(x, nat, b, BinderInfo.Default)

  test("hasLooseBVar") {
    assert(ExprOps.hasLooseBVar(bv(0), 0))
    assert(!ExprOps.hasLooseBVar(bv(0), 1))
    assert(ExprOps.hasLooseBVar(lam(bv(1)), 0))
    assert(!ExprOps.hasLooseBVar(lam(bv(0)), 0))
    assert(ExprOps.hasLooseBVar(Expr.App(bv(2), bv(5)), 5))
    assert(!ExprOps.hasLooseBVar(nat, 0))
    // The binder type is outside the binder's scope.
    assert(ExprOps.hasLooseBVar(Expr.Lam(x, bv(0), nat, BinderInfo.Default), 0))
    // A let body is under one binder, its type and value are not.
    assert(ExprOps.hasLooseBVar(Expr.LetE(x, bv(0), nat, nat, false), 0))
    assert(!ExprOps.hasLooseBVar(Expr.LetE(x, nat, nat, bv(0), false), 0))
  }

  test("liftLooseBVars") {
    assertEquals(ExprOps.liftLooseBVars(bv(0), 0, 3), bv(3))
    assertEquals(ExprOps.liftLooseBVars(bv(0), 1, 3), bv(0))
    assertEquals(ExprOps.liftLooseBVars(lam(bv(0)), 0, 3), lam(bv(0)))
    assertEquals(ExprOps.liftLooseBVars(lam(bv(1)), 0, 3), lam(bv(4)))
    assertEquals(ExprOps.liftLooseBVars(nat, 0, 3), nat)
    assertEquals(ExprOps.liftLooseBVars(bv(0), 0, 0), bv(0))
  }

  test("lowerLooseBVars") {
    assertEquals(ExprOps.lowerLooseBVars(bv(3), 1, 1), bv(2))
    assertEquals(ExprOps.lowerLooseBVars(lam(bv(4)), 1, 1), lam(bv(3)))
    assertEquals(ExprOps.lowerLooseBVars(lam(bv(0)), 1, 1), lam(bv(0)))
    intercept[KernelException](ExprOps.lowerLooseBVars(bv(0), 0, 1))
  }

  test("instantiate1 opens the outermost binder") {
    assertEquals(ExprOps.instantiate1(bv(0), nat), nat)
    assertEquals(ExprOps.instantiate1(bv(1), nat), bv(0))
    assertEquals(ExprOps.instantiate1(lam(bv(1)), nat), lam(nat))
    assertEquals(ExprOps.instantiate1(nat, bv(0)), nat)
    // The substituted term is lifted over the binders it passes under.
    assertEquals(ExprOps.instantiate1(lam(bv(1)), bv(0)), lam(bv(1)))
  }

  test("instantiateRev substitutes the innermost binder last") {
    val body = Expr.App(Expr.App(bv(0), bv(1)), bv(2))
    val a    = Expr.const("A")
    val b    = Expr.const("B")
    val c    = Expr.const("C")
    assertEquals(ExprOps.instantiateRev(body, Vector(c, b, a)), Expr.App(Expr.App(a, b), c))
  }

  test("instantiateRange lowers the bvars above the window") {
    val e = Expr.App(bv(0), Expr.App(bv(1), bv(2)))
    assertEquals(
      ExprOps.instantiateRange(e, 0, Vector(nat)),
      Expr.App(nat, Expr.App(bv(0), bv(1)))
    )
    assertEquals(ExprOps.instantiateRange(e, 1, Vector(nat)), Expr.App(bv(0), Expr.App(nat, bv(1))))
  }

  test("abstract replaces free variables") {
    val f = Expr.FVar(Name.mkSimple("f0"))
    val g = Expr.FVar(Name.mkSimple("g0"))
    assertEquals(ExprOps.abstract1(f, f), bv(0))
    assertEquals(ExprOps.abstract_(Expr.App(f, g), Vector(g, f)), Expr.App(bv(0), bv(1)))
    assertEquals(ExprOps.abstract1(nat, f), nat)
    assertEquals(ExprOps.abstract1(lam(f), f), lam(bv(1)))
    intercept[KernelException](ExprOps.abstract1(f, nat))
  }

  test("abstract and instantiateRev are inverse on fvars") {
    val f = Expr.FVar(Name.mkSimple("f0"))
    val g = Expr.FVar(Name.mkSimple("g0"))
    val e = Expr.App(Expr.App(f, g), lam(Expr.App(f, bv(0))))
    val fvars = Vector(f, g)
    assertEquals(ExprOps.instantiateRev(ExprOps.abstract_(e, fvars), fvars), e)
  }

  test("instantiateLevelParams") {
    val e = Expr.App(Expr.Sort(lu), Expr.Const(Name.parse("f"), List(lu, Level.zero)))
    val r = ExprOps.instantiateLevelParams(e, List(u), List(Level.one))
    assertEquals(r, Expr.App(Expr.Sort(Level.one), Expr.Const(Name.parse("f"), List(Level.one, Level.zero))))
    assertEquals(ExprOps.instantiateLevelParams(nat, List(u), List(Level.one)), nat)
    assert(!r.hasLevelParam)
  }

  test("undefinedLevelParam") {
    val e = Expr.App(Expr.Sort(lu), Expr.Const(Name.parse("f"), List(Level.Param(y))))
    assertEquals(ExprOps.undefinedLevelParam(e, List(u, y)), None)
    assertEquals(ExprOps.undefinedLevelParam(e, List(u)), Some(y))
    assertEquals(ExprOps.undefinedLevelParam(nat, Nil), None)
    // `get_undef_param` reports the first in `for_each_fn` order, which visits
    // `app_fn` before `app_arg`.
    assertEquals(
      ExprOps.undefinedLevelParam(Expr.App(Expr.Sort(lu), Expr.Sort(Level.Param(y))), Nil),
      Some(u)
    )
    assertEquals(
      ExprOps.undefinedLevelParam(Expr.Lam(x, Expr.Sort(lu), Expr.Sort(Level.Param(y)), BinderInfo.Default), Nil),
      Some(u)
    )
    assertEquals(
      ExprOps.undefinedLevelParam(
        Expr.LetE(x, Expr.Sort(lu), Expr.Sort(Level.Param(y)), Expr.Sort(Level.Param(Name.mkSimple("z"))), false),
        Nil
      ),
      Some(u)
    )
  }

  test("forEach visits children in for_each_fn order") {
    val a = Expr.const("A")
    val b = Expr.const("B")
    val c = Expr.const("C")
    def order(e: Expr): List[String] =
      val seen = List.newBuilder[String]
      ExprOps.forEach(e) { (m, _) =>
        Expr.constName(m).foreach(n => seen += n.toString)
        true
      }
      seen.result()
    assertEquals(order(Expr.App(a, b)), List("A", "B"))
    assertEquals(order(Expr.Lam(x, a, b, BinderInfo.Default)), List("A", "B"))
    assertEquals(order(Expr.ForallE(x, a, b, BinderInfo.Default)), List("A", "B"))
    assertEquals(order(Expr.LetE(x, a, b, c, false)), List("A", "B", "C"))
    assertEquals(order(Expr.mkAppN(a, Seq(b, c))), List("A", "B", "C"))
  }

  test("cheapBetaReduce") {
    assertEquals(ExprOps.cheapBetaReduce(Expr.App(lam(nat), nat)), nat)
    assertEquals(ExprOps.cheapBetaReduce(Expr.App(lam(bv(0)), nat)), nat)
    assertEquals(ExprOps.cheapBetaReduce(nat), nat)
    // Not cheap: the body is a term mentioning the binder non-trivially.
    val stuck = Expr.App(lam(Expr.App(bv(0), bv(0))), nat)
    assertEquals(ExprOps.cheapBetaReduce(stuck), stuck)
    assertEquals(
      ExprOps.cheapBetaReduce(Expr.mkAppN(lam(lam(bv(1))), Seq(nat, Expr.const("B")))),
      nat
    )
  }

  test("betaReduce applies as many arguments as there are lambdas") {
    // `(fun x y => x y) a b` reduces to `a b`: the outer binder #1 takes the
    // first argument and the inner binder #0 the second.
    val f = lam(lam(Expr.App(bv(1), bv(0))))
    val a = Expr.const("A")
    val b = Expr.const("B")
    assertEquals(ExprOps.betaReduce(f, Vector(a, b)), Expr.App(a, b))
    assertEquals(ExprOps.betaReduce(lam(lam(bv(1))), Vector(a, b)), a)
    assertEquals(ExprOps.betaReduce(lam(lam(bv(0))), Vector(a, b)), b)
    // A surplus argument stays applied.
    assertEquals(ExprOps.betaReduce(lam(bv(0)), Vector(a, b)), Expr.App(a, b))
    assertEquals(ExprOps.betaReduce(nat, Vector(a)), Expr.App(nat, a))
  }

  test("litType") {
    assertEquals(ExprOps.litType(Literal.NatVal(3)), Expr.const("Nat"))
    assertEquals(ExprOps.litType(Literal.StrVal("x")), Expr.const("String"))
  }

  test("natLitToConstructor") {
    assertEquals(ExprOps.natLitToConstructor(0), Expr.const(Names.natZero))
    assertEquals(
      ExprOps.natLitToConstructor(3),
      Expr.App(Expr.const(Names.natSucc), Expr.natLit(2))
    )
  }

  test("stringLitToConstructor uses the profile's constructor") {
    val e35 = ExprOps.stringLitToConstructor("ab", KernelProfile.v4_35)
    val e25 = ExprOps.stringLitToConstructor("ab", KernelProfile.v4_25)
    assertEquals(Expr.getAppFn(e35), Expr.const(Names.stringOfListFor(KernelProfile.v4_35)))
    assertEquals(Expr.constName(Expr.getAppFn(e35)), Some(Name.parse("String.ofList")))
    assertEquals(Expr.constName(Expr.getAppFn(e25)), Some(Name.parse("String.mk")))
    assertEquals(ExprOps.stringLitToConstructor("", KernelProfile.v4_35),
      Expr.App(Expr.const(Name.parse("String.ofList")),
        Expr.App(Expr.Const(Names.listNil, List(Level.zero)), Expr.const(Names.char))))
  }

  test("stringLitToConstructor decodes code points, not UTF-16 units") {
    // U+1F600 is one code point and two UTF-16 units.
    val e  = ExprOps.stringLitToConstructor("😀", KernelProfile.v4_35)
    val cs = ExprOps.codePoints("😀")
    assertEquals(cs.toList, List(0x1F600))
    // `List.cons.{0} Char (Char.ofNat 128512) (List.nil.{0} Char)`
    val list = Expr.getAppArgs(e).head
    assertEquals(Expr.constName(Expr.getAppFn(list)), Some(Names.listCons))
    val listArgs = Expr.getAppArgs(list)
    assertEquals(listArgs.length, 3)
    assertEquals(listArgs(0), Expr.const(Names.char))
    assertEquals(listArgs(1), Expr.App(Expr.const(Names.charOfNat), Expr.natLit(0x1F600)))
  }

  test("consumeTypeAnnotations strips the gadgets") {
    val sortW = Expr.Sort(Level.one)
    def app(n: Name, args: Expr*) = Expr.mkAppN(Expr.const(n), args)
    assertEquals(ExprOps.consumeTypeAnnotations(app(Names.outParam, sortW)), sortW)
    assertEquals(ExprOps.consumeTypeAnnotations(app(Names.semiOutParam, sortW)), sortW)
    // optParam and autoParam take the type first and the default second.
    assertEquals(ExprOps.consumeTypeAnnotations(app(Names.optParam, sortW, nat)), sortW)
    assertEquals(ExprOps.consumeTypeAnnotations(app(Names.autoParam, sortW, nat)), sortW)
    // Nested.
    assertEquals(
      ExprOps.consumeTypeAnnotations(app(Names.outParam, app(Names.optParam, sortW, nat))),
      sortW
    )
    // Wrong arity is not an annotation.
    assertEquals(ExprOps.consumeTypeAnnotations(app(Names.outParam, sortW, nat)), app(Names.outParam, sortW, nat))
    assertEquals(ExprOps.consumeTypeAnnotations(app(Names.optParam, sortW)), app(Names.optParam, sortW))
    // Not nested under a binder, as Lean documents.
    val underBinder = pi(app(Names.outParam, sortW))
    assertEquals(ExprOps.consumeTypeAnnotations(underBinder), underBinder)
    assertEquals(ExprOps.consumeTypeAnnotations(nat), nat)
  }

  test("inferImplicit marks binders whose variable is used later") {
    // forall (A : Type), A -> A   =>   A becomes implicit
    val t = Expr.ForallE(
      Name.mkSimple("A"), Expr.Sort(Level.one),
      Expr.ForallE(Name.mkSimple("a"), bv(0), bv(1), BinderInfo.Default),
      BinderInfo.Default
    )
    val r = ExprOps.inferImplicit(t, strict = true).asInstanceOf[Expr.ForallE]
    assertEquals(r.binderInfo, BinderInfo.Implicit)
    assertEquals(r.body.asInstanceOf[Expr.ForallE].binderInfo, BinderInfo.Default)
    // Nothing to infer when the variable is unused.
    val u2 = Expr.ForallE(Name.mkSimple("A"), Expr.Sort(Level.one), nat, BinderInfo.Default)
    assertEquals(ExprOps.inferImplicit(u2, strict = true), u2)
    // Annotations are invisible to `==`, so this only shows up with isBiEqual.
    assert(r == t)
    assert(!Expr.isBiEqual(r, t))
  }

  test("deep terms do not overflow") {
    val depth = 50000
    val deep  = (0 until depth).foldLeft(bv(0))((e, _) => Expr.App(e, bv(1)))
    assertEquals(ExprOps.liftLooseBVars(deep, 0, 1).looseBVarRange, 3)
    assert(ExprOps.hasLooseBVar(deep, 1))
    // `nested` is 50000 lambdas over `#50000`, so exactly one bvar is loose.
    val nested = (0 until depth).foldLeft(bv(depth))((e, _) => lam(e))
    assertEquals(nested.looseBVarRange, 1)
    val opened = ExprOps.instantiate1(nested, nat)
    assertEquals(opened.looseBVarRange, 0)
    assertEquals(ExprOps.instantiate1(opened, nat), opened)
  }

  property("abstract with no free variables is the identity") {
    forAll { (e: Expr) => ExprOps.abstract_(e, Vector.empty) eq e }
  }

  property("instantiateRev undoes abstract") {
    // The term has to be closed: `abstract_` leaves loose bound variables alone,
    // but `instantiateRev` would substitute any that fall inside its window.
    val f0 = Expr.FVar(Name.mkSimple("_roundTrip0"))
    val f1 = Expr.FVar(Name.mkSimple("_roundTrip1"))
    val fvars = Vector(f0, f1)
    forAll { (e: Expr) =>
      val closed = (0 until e.looseBVarRange).foldLeft(e)((x, _) => lam(x))
      val t      = Expr.App(Expr.App(Expr.const("f"), closed), Expr.App(f0, Expr.App(f1, f0)))
      !t.hasLooseBVars && ExprOps.instantiateRev(ExprOps.abstract_(t, fvars), fvars) == t
    }
  }

  property("liftLooseBVars by 0 is the identity") {
    forAll { (e: Expr) => ExprOps.liftLooseBVars(e, 0, 0) == e }
  }

  property("lift then lower round-trips") {
    forAll { (e: Expr) =>
      ExprOps.lowerLooseBVars(ExprOps.liftLooseBVars(e, 0, 2), 2, 2) == e
    }
  }

  property("instantiating a closed term is the identity") {
    forAll { (e: Expr) =>
      val closed = (0 until e.looseBVarRange).foldLeft(e)((x, _) => lam(x))
      !closed.hasLooseBVars && ExprOps.instantiate1(closed, nat) == closed
    }
  }

  property("instantiate lowers the loose bvar range") {
    forAll { (e: Expr) =>
      val r = ExprOps.instantiate1(e, nat)
      r.looseBVarRange == math.max(e.looseBVarRange - 1, 0)
    }
  }

  property("replace with a constant function rebuilds nothing") {
    forAll { (e: Expr) => ExprOps.replace(e)((m, _) => Some(m)) eq e }
  }
