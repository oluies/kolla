package kolla.dsl

import kolla.kernel.*
import kolla.dsl.LeanDsl.*

class LeanDslSuite extends munit.FunSuite:

  val natN = Name.parse("Nat")
  val nat  = Expr.const("Nat")
  def bv(i: Int) = Expr.BVar(i)

  test("binders abstract automatically") {
    // The bound variable is a Scala value; the de Bruijn index is computed.
    assertEquals(
      Lam("x".n, nat)(x => x),
      Expr.Lam(Name.mkSimple("x"), nat, bv(0), BinderInfo.Default)
    )
    assertEquals(
      Pi("x".n, nat)(x => x),
      Expr.ForallE(Name.mkSimple("x"), nat, bv(0), BinderInfo.Default)
    )
    // The outer variable is #1 inside the inner binder.
    assertEquals(
      Lam("x".n, nat)(x => Lam("y".n, nat)(_ => x)),
      Expr.Lam(Name.mkSimple("x"), nat,
        Expr.Lam(Name.mkSimple("y"), nat, bv(1), BinderInfo.Default), BinderInfo.Default)
    )
    // A variable used twice at different depths gets different indices.
    assertEquals(
      Lam("x".n, nat)(x => Lam("y".n, nat)(y => App(x, y, x))),
      LeanParser.parseOrThrow("fun (x : Nat) (y : Nat) => x y x")
    )
  }

  test("a binder's domain may use the enclosing variables") {
    val e = Pi("A".n, Type0)(a => Pi("a".n, a)(_ => a))
    assertEquals(e, LeanParser.parseOrThrow("forall (A : Sort 1) (a : A), A"))
  }

  test("let binds its variable") {
    assertEquals(
      Let("x".n, nat, natLit(3))(x => x),
      Expr.LetE(Name.mkSimple("x"), nat, Expr.natLit(3), bv(0), false)
    )
  }

  test("fresh variables do not collide across terms") {
    val a = Lam("x".n, nat)(x => x)
    val b = Lam("x".n, nat)(x => x)
    assertEquals(a, b)
    assert(!a.hasFVar)
    assert(!b.hasFVar)
  }

  test("binder annotations") {
    assertEquals(
      Lam("x".n, nat, BinderInfo.Implicit)(x => x).asInstanceOf[Expr.Lam].binderInfo,
      BinderInfo.Implicit
    )
  }

  test("sorts, constants and applications") {
    assertEquals(Sort(zero), Expr.Sort(Level.zero))
    assertEquals(Prop, Expr.Sort(Level.zero))
    assertEquals(Type0, Expr.Sort(Level.one))
    assertEquals(Type(2), Expr.Sort(Level.ofNat(3)))
    assertEquals(Const("Nat"), nat)
    assertEquals(Const(natN, param("u")), Expr.Const(natN, List(Level.Param(Name.mkSimple("u")))))
    assertEquals(App(Const("f"), Const("a"), Const("b")), LeanParser.parseOrThrow("f a b"))
    assertEquals("Nat".c, nat)
    assertEquals("u".u, Level.Param(Name.mkSimple("u")))
  }

  test("the arrow operator is right associative") {
    // Distinct constants: `Nat ->: Nat` is symmetric and cannot detect a
    // reversed arrow, which is the regression D6 records.
    val a = Expr.const("A")
    val b = Expr.const("B")
    val c = Expr.const("C")
    assertEquals(a ->: b, LeanParser.parseOrThrow("A -> B"))
    assertEquals(a ->: b ->: c, LeanParser.parseOrThrow("A -> B -> C"))
    assertNotEquals(a ->: b, b ->: a)
    // The domain really is the left operand.
    assertEquals((a ->: b).asInstanceOf[Expr.ForallE].binderType, a)
  }

  test("application via apply") {
    assertEquals(Const("f")(Const("a")), Expr.App(Expr.const("f"), Expr.const("a")))
  }

  test("nested binders build correctly at a hand-written scale") {
    // Each binder abstracts its own variable, so this is quadratic; the builder
    // is for hand-written terms, not generated telescopes.
    val depth = 200
    def build(n: Int): Expr =
      if n == 0 then natLit(0) else Lam("x".n, nat)(_ => build(n - 1))
    val e = build(depth)
    var cur = e
    var k = 0
    while cur.isInstanceOf[Expr.Lam] do
      cur = cur.asInstanceOf[Expr.Lam].body
      k += 1
    assertEquals(k, depth)
    assertEquals(cur, natLit(0))
    assert(!e.hasFVar)
  }

  test("a generated telescope uses the local context instead") {
    val g = new NameGenerator()
    var lctx = LocalContext.empty
    val fvars = (0 until 2000).map { _ =>
      val (next, f) = lctx.mkLocalDecl(g, Name.mkSimple("x"), nat, BinderInfo.Default)
      lctx = next
      f
    }
    val e = lctx.mkPi(fvars, fvars.last)
    assertEquals(e.looseBVarRange, 0)
    var cur = e
    var k = 0
    while cur.isInstanceOf[Expr.ForallE] do
      cur = cur.asInstanceOf[Expr.ForallE].body
      k += 1
    assertEquals(k, 2000)
    assertEquals(cur, bv(0))
  }
