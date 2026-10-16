package kolla.kernel

class LocalContextSuite extends munit.FunSuite:

  val nat = Expr.const("Nat")
  val x   = Name.mkSimple("x")
  val y   = Name.mkSimple("y")

  test("fresh identifiers are distinct") {
    val g = new NameGenerator()
    val (c1, f1) = LocalContext.empty.mkLocalDecl(g, x, nat, BinderInfo.Default)
    val (c2, f2) = c1.mkLocalDecl(g, x, nat, BinderInfo.Default)
    assertNotEquals(f1, f2)
    assertEquals(c2.size, 2)
    assertEquals(c2.find(f1).map(_.idx), Some(0))
    assertEquals(c2.find(f2).map(_.idx), Some(1))
    assertEquals(c2.find(f1).map(_.tpe), Some(nat))
  }

  test("let declarations carry a value") {
    val g = new NameGenerator()
    val (c, f) = LocalContext.empty.mkLetDecl(g, x, nat, Expr.natLit(3))
    assertEquals(c.find(f).flatMap(_.value), Some(Expr.natLit(3)))
    assert(c.isLetFVar(f))
    val (c2, f2) = c.mkLocalDecl(g, y, nat, BinderInfo.Default)
    assert(!c2.isLetFVar(f2))
    assert(!c2.isLetFVar(nat))
  }

  test("unknown free variables are rejected") {
    intercept[KernelException](LocalContext.empty.get(x))
    assertEquals(LocalContext.empty.find(x), None)
  }

  test("mkPi rebuilds the binders the fvars stand for") {
    val g = new NameGenerator()
    val (c1, a) = LocalContext.empty.mkLocalDecl(g, x, Expr.Sort(Level.one), BinderInfo.Implicit)
    val (c2, b) = c1.mkLocalDecl(g, y, a, BinderInfo.Default)
    val body    = Expr.App(Expr.App(Expr.const("f"), a), b)
    val pi      = c2.mkPi(Vector(a, b), body)
    assertEquals(
      pi,
      Expr.ForallE(
        x,
        Expr.Sort(Level.one),
        Expr.ForallE(y, Expr.BVar(0), Expr.App(Expr.App(Expr.const("f"), Expr.BVar(1)), Expr.BVar(0)), BinderInfo.Default),
        BinderInfo.Implicit
      )
    )
    assert(Expr.isBiEqual(pi, pi))
    val lam = c2.mkLambda(Vector(a, b), body)
    assertEquals(
      lam,
      Expr.Lam(
        x,
        Expr.Sort(Level.one),
        Expr.Lam(y, Expr.BVar(0), Expr.App(Expr.App(Expr.const("f"), Expr.BVar(1)), Expr.BVar(0)), BinderInfo.Default),
        BinderInfo.Implicit
      )
    )
  }

  test("mkPi rebuilds a let for a let-bound fvar") {
    val g = new NameGenerator()
    val (c, v) = LocalContext.empty.mkLetDecl(g, x, nat, Expr.natLit(1))
    assertEquals(
      c.mkPi(Vector(v), Expr.App(Expr.const("f"), v)),
      Expr.LetE(x, nat, Expr.natLit(1), Expr.App(Expr.const("f"), Expr.BVar(0)), false)
    )
  }

  test("removeDeadLet drops a let whose variable does not occur") {
    val g = new NameGenerator()
    val (c, v) = LocalContext.empty.mkLetDecl(g, x, nat, Expr.natLit(1))
    assertEquals(c.mkPi(Vector(v), nat, removeDeadLet = true), nat)
    assertEquals(
      c.mkPi(Vector(v), nat, removeDeadLet = false),
      Expr.LetE(x, nat, Expr.natLit(1), nat, false)
    )
  }

  test("abstraction is nested correctly for many binders") {
    val g = new NameGenerator()
    var c = LocalContext.empty
    val fvars = (0 until 2000).map { i =>
      val (c2, f) = c.mkLocalDecl(g, x, nat, BinderInfo.Default)
      c = c2
      f
    }
    val pi = c.mkPi(fvars, fvars.last)
    assertEquals(pi.looseBVarRange, 0)
    var inner = pi
    var depth = 0
    while inner.isInstanceOf[Expr.ForallE] do
      inner = inner.asInstanceOf[Expr.ForallE].body
      depth += 1
    assertEquals(depth, 2000)
    assertEquals(inner, Expr.BVar(0))
  }
