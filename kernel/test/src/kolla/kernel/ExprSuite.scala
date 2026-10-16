package kolla.kernel

import kolla.kernel.Generators.given
import org.scalacheck.Prop.forAll

class ExprSuite extends munit.ScalaCheckSuite:

  val nat   = Expr.const("Nat")
  val u     = Level.param("u")
  val x     = Name.mkSimple("x")
  val y     = Name.mkSimple("y")

  test("loose bvar range") {
    assertEquals(Expr.BVar(0).looseBVarRange, 1)
    assertEquals(Expr.BVar(3).looseBVarRange, 4)
    assertEquals(nat.looseBVarRange, 0)
    assertEquals(Expr.Lam(x, nat, Expr.BVar(0), BinderInfo.Default).looseBVarRange, 0)
    assertEquals(Expr.Lam(x, nat, Expr.BVar(1), BinderInfo.Default).looseBVarRange, 1)
    assertEquals(Expr.App(Expr.BVar(2), Expr.BVar(0)).looseBVarRange, 3)
    assertEquals(
      Expr.LetE(x, nat, Expr.BVar(0), Expr.BVar(1), false).looseBVarRange,
      1
    )
    assert(Expr.BVar(0).hasLooseBVars)
    assert(!nat.hasLooseBVars)
  }

  test("flag propagation") {
    val f = Expr.FVar(x)
    assert(f.hasFVar)
    assert(Expr.App(nat, f).hasFVar)
    assert(!Expr.App(nat, nat).hasFVar)
    assert(Expr.MVar(x).hasExprMVar)
    assert(Expr.Sort(u).hasLevelParam)
    assert(!Expr.Sort(Level.zero).hasLevelParam)
    assert(Expr.Const(x, List(u)).hasLevelParam)
    assert(Expr.Sort(Level.mvar(x)).hasLevelMVar)
    assert(Expr.Lam(x, Expr.Sort(u), nat, BinderInfo.Default).hasLevelParam)
    assert(Expr.Proj(x, 0, f).hasFVar)
  }

  test("equality ignores binder names and annotations") {
    val a = Expr.Lam(x, nat, Expr.BVar(0), BinderInfo.Default)
    val b = Expr.Lam(y, nat, Expr.BVar(0), BinderInfo.Implicit)
    assertEquals(a, b)
    assertEquals(a.hashCode, b.hashCode)
    assert(!Expr.isBiEqual(a, b))
    assert(Expr.isBiEqual(a, Expr.Lam(x, nat, Expr.BVar(0), BinderInfo.Default)))
  }

  test("equality compares the let nondep flag") {
    val a = Expr.LetE(x, nat, nat, Expr.BVar(0), false)
    val b = Expr.LetE(x, nat, nat, Expr.BVar(0), true)
    assertNotEquals(a, b)
    assertEquals(a, Expr.LetE(y, nat, nat, Expr.BVar(0), false))
  }

  test("app spines") {
    val e = Expr.mkAppN(nat, Seq(Expr.BVar(0), Expr.BVar(1), Expr.BVar(2)))
    assertEquals(Expr.getAppFn(e), nat)
    assertEquals(Expr.getAppNumArgs(e), 3)
    assertEquals(Expr.getAppArgs(e).toList, List(Expr.BVar(0), Expr.BVar(1), Expr.BVar(2)))
    assertEquals(Expr.getRevArgD(e, 0, nat), Expr.BVar(2))
    assertEquals(Expr.getRevArgD(e, 2, nat), Expr.BVar(0))
    assertEquals(Expr.getAppFn(nat), nat)
    assertEquals(Expr.getAppArgs(nat).toList, Nil)
  }

  test("mdata is transparent to consumeMData") {
    val e = Expr.MData(KVMap.empty, Expr.MData(KVMap.empty, nat))
    assertEquals(Expr.consumeMData(e), nat)
    assertNotEquals(e: Expr, nat)
  }

  test("literals") {
    assertEquals(Expr.natLit(3), Expr.Lit(Literal.NatVal(BigInt(3))): Expr)
    assertNotEquals(Expr.natLit(3), Expr.strLit("3"))
    assert(Literal.lt(Literal.NatVal(1), Literal.StrVal("")))
    assert(Literal.lt(Literal.NatVal(1), Literal.NatVal(2)))
  }

  test("deep applications do not overflow the stack") {
    val deep  = (0 until 200000).foldLeft(nat)((e, _) => Expr.App(e, nat))
    val deep2 = (0 until 200000).foldLeft(nat)((e, _) => Expr.App(e, nat))
    assertEquals(Expr.getAppNumArgs(deep), 200000)
    assertEquals(deep, deep2)
    assertEquals(Expr.getAppFn(deep), nat)
    assert(deep.toString.length <= Pretty.defaultMaxChars + 1)
  }

  test("deep binders do not overflow the stack") {
    val deep  = (0 until 200000).foldLeft(nat)((e, _) => Expr.Lam(x, nat, e, BinderInfo.Default))
    val deep2 = (0 until 200000).foldLeft(nat)((e, _) => Expr.Lam(y, nat, e, BinderInfo.Implicit))
    assertEquals(deep, deep2)
  }

  test("too many loose bvars is rejected") {
    intercept[KernelException](Expr.BVar(Expr.maxLooseBVarRange))
  }

  property("equal expressions have equal data") {
    forAll { (a: Expr, b: Expr) => !(a == b) || a.data == b.data }
  }

  property("equality is reflexive, symmetric") {
    forAll { (a: Expr, b: Expr) => (a == a) && ((a == b) == (b == a)) }
  }

  property("bi-equality refines equality") {
    forAll { (a: Expr, b: Expr) => !Expr.isBiEqual(a, b) || a == b }
  }

  property("app spine round-trips") {
    forAll { (a: Expr) =>
      Expr.mkAppN(Expr.getAppFn(a), Expr.getAppArgs(a).toSeq) == a
    }
  }

  property("looseBVarRange bounds the bvars that occur") {
    forAll { (a: Expr) => a.looseBVarRange >= 0 && a.looseBVarRange <= Expr.maxLooseBVarRange }
  }
