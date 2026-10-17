package kolla.dsl

import kolla.kernel.*

class LeanParserSuite extends munit.FunSuite:

  def p(s: String): Expr = LeanParser.parseOrThrow(s)
  def err(s: String): String =
    LeanParser.parse(s) match
      case Left(e)  => e.message
      case Right(r) => fail(s"expected a parse error, got $r")

  val nat = Expr.const("Nat")
  def bv(i: Int) = Expr.BVar(i)

  test("constants, literals and bound variables") {
    assertEquals(p("Nat"), nat)
    assertEquals(p("Nat.add"), Expr.const("Nat.add"))
    assertEquals(p("42"), Expr.natLit(42))
    assertEquals(p("\"hi\\n\""), Expr.strLit("hi\n"))
    assertEquals(p("#3"), bv(3))
    assertEquals(p("(Nat)"), nat)
  }

  test("universe arguments") {
    assertEquals(p("List.{u}"), Expr.Const(Name.parse("List"), List(Level.Param(Name.mkSimple("u")))))
    assertEquals(p("f.{0}"), Expr.Const(Name.parse("f"), List(Level.zero)))
    assertEquals(p("f.{1, u}"), Expr.Const(Name.parse("f"), List(Level.one, Level.Param(Name.mkSimple("u")))))
    assertEquals(
      p("f.{max u v}"),
      Expr.Const(Name.parse("f"), List(Level.Max(Level.Param(Name.mkSimple("u")), Level.Param(Name.mkSimple("v")))))
    )
    assertEquals(
      p("f.{imax u 0}"),
      Expr.Const(Name.parse("f"), List(Level.imax(Level.Param(Name.mkSimple("u")), Level.zero)))
    )
    assertEquals(p("f.{succ u}"), Expr.Const(Name.parse("f"), List(Level.Succ(Level.Param(Name.mkSimple("u"))))))
    assertEquals(p("f.{}"), Expr.Const(Name.parse("f"), Nil))
  }

  test("sorts") {
    assertEquals(p("Sort 0"), Expr.Sort(Level.zero))
    assertEquals(p("Sort 1"), Expr.Sort(Level.one))
    assertEquals(p("Sort u"), Expr.Sort(Level.Param(Name.mkSimple("u"))))
    assertEquals(p("Sort (max u v)"), Expr.Sort(Level.Max(Level.Param(Name.mkSimple("u")), Level.Param(Name.mkSimple("v")))))
  }

  test("application is left associative") {
    assertEquals(p("f a b"), Expr.App(Expr.App(Expr.const("f"), Expr.const("a")), Expr.const("b")))
    assertEquals(p("f (g a)"), Expr.App(Expr.const("f"), Expr.App(Expr.const("g"), Expr.const("a"))))
  }

  test("lambda binds its variable") {
    assertEquals(
      p("fun (x : Nat) => x"),
      Expr.Lam(Name.mkSimple("x"), nat, bv(0), BinderInfo.Default)
    )
    // The outer binder is #1 inside the inner one.
    assertEquals(
      p("fun (x : Nat) (y : Nat) => x"),
      Expr.Lam(Name.mkSimple("x"), nat,
        Expr.Lam(Name.mkSimple("y"), nat, bv(1), BinderInfo.Default), BinderInfo.Default)
    )
    assertEquals(p("λ (x : Nat) => x"), p("fun (x : Nat) => x"))
    // Several names in one group share the type.
    assertEquals(p("fun (x y : Nat) => x"), p("fun (x : Nat) (y : Nat) => x"))
  }

  test("forall binds its variable") {
    assertEquals(
      p("forall (x : Nat), x"),
      Expr.ForallE(Name.mkSimple("x"), nat, bv(0), BinderInfo.Default)
    )
    assertEquals(p("∀ (x : Nat), x"), p("forall (x : Nat), x"))
  }

  test("binder annotations") {
    def bi(s: String): BinderInfo = p(s).asInstanceOf[Expr.Lam].binderInfo
    assertEquals(bi("fun (x : Nat) => x"), BinderInfo.Default)
    assertEquals(bi("fun {x : Nat} => x"), BinderInfo.Implicit)
    assertEquals(bi("fun ⦃x : Nat⦄ => x"), BinderInfo.StrictImplicit)
    assertEquals(bi("fun [x : Nat] => x"), BinderInfo.InstImplicit)
  }

  test("a binder's type sees the earlier binders") {
    // forall (A : Sort 1) (a : A), A
    val r = p("forall (A : Sort 1) (a : A), A")
    val outer = r.asInstanceOf[Expr.ForallE]
    assertEquals(outer.binderType, Expr.Sort(Level.one))
    val inner = outer.body.asInstanceOf[Expr.ForallE]
    assertEquals(inner.binderType, bv(0))
    assertEquals(inner.body, bv(1))
  }

  test("the arrow is non-dependent and right associative") {
    assertEquals(p("Nat -> Nat"), Expr.ForallE(Name.mkSimple("a"), nat, nat, BinderInfo.Default))
    assertEquals(p("Nat → Nat"), p("Nat -> Nat"))
    // a -> (b -> c)
    val r = p("Nat -> Nat -> Nat").asInstanceOf[Expr.ForallE]
    assertEquals(r.binderType, nat)
    assertEquals(r.body.asInstanceOf[Expr.ForallE].binderType, nat)
    // The codomain is under one more binder, so a constant stays a constant.
    assertEquals(p("Nat -> Nat").asInstanceOf[Expr.ForallE].body, nat)
  }

  test("an arrow codomain does not capture the domain's scope") {
    // `A -> A` inside a binder: both occurrences refer to the same binder.
    val r = p("forall (A : Sort 1), A -> A").asInstanceOf[Expr.ForallE]
    val arr = r.body.asInstanceOf[Expr.ForallE]
    assertEquals(arr.binderType, bv(0))
    // Under the arrow's own binder, `A` is one level further out.
    assertEquals(arr.body, bv(1))
  }

  test("let") {
    assertEquals(
      p("let x : Nat := 3; x"),
      Expr.LetE(Name.mkSimple("x"), nat, Expr.natLit(3), bv(0), false)
    )
    // The value is outside the binder.
    val r = p("let x : Nat := 3; fun (y : Nat) => x").asInstanceOf[Expr.LetE]
    assertEquals(r.value, Expr.natLit(3))
    assertEquals(r.body.asInstanceOf[Expr.Lam].body, bv(1))
  }

  test("projections and splice markers") {
    assertEquals(LeanParser.spliceIndex(p("$0")), Some(0))
    assertEquals(LeanParser.spliceIndex(p("$7")), Some(7))
    assertEquals(LeanParser.spliceIndex(nat), None)
    assertEquals(p("f $0 $1"), Expr.App(Expr.App(Expr.const("f"), p("$0")), p("$1")))
  }

  test("errors carry an offset and a message") {
    assert(clue(err("fun x => x")).contains("expected a binder group"))
    assert(clue(err("fun (x : Nat) x")).contains("expected '=>'"))
    assert(clue(err("(Nat")).contains("expected ')'"))
    assert(clue(err("")).contains("expected an expression"))
    assert(clue(err("Nat Nat)")).contains("unexpected trailing input"))
    assert(clue(err("let x := 3; x")).contains("expected ':'"))
    // A keyword cannot appear as an argument.
    assert(clue(err("f fun")).contains("cannot start an argument"))
    assert(clue(err("fun (x : Nat) => fun")).contains("expected a binder group"))
    LeanParser.parse("(Nat") match
      case Left(e)  => assert(e.offset > 0, clue(e.offset))
      case Right(_) => fail("expected an error")
  }

  test("whitespace and newlines are insignificant") {
    assertEquals(p("  fun  (x : Nat)\n  =>\n  x  "), p("fun (x : Nat) => x"))
  }

  test("nesting up to the limit parses") {
    // Each `fun ... =>` costs one level of `expr`.
    val depth = LeanParser.maxDepth - 2
    val src = ("fun (x : Nat) => " * depth) + "x"
    var cur = p(src)
    var n = 0
    while cur.isInstanceOf[Expr.Lam] do
      cur = cur.asInstanceOf[Expr.Lam].body
      n += 1
    assertEquals(n, depth)
    assertEquals(cur, bv(0))
  }

  test("nesting beyond the limit is a parse error, not a crash") {
    val src = ("fun (x : Nat) => " * (LeanParser.maxDepth * 2)) + "x"
    assert(clue(err(src)).contains("nesting deeper than"))
    // Parenthesis nesting is bounded the same way.
    val parens = "(" * (LeanParser.maxDepth * 2) + "Nat" + ")" * (LeanParser.maxDepth * 2)
    assert(clue(err(parens)).contains("nesting deeper than"))
  }

  test("parseName reads an all-digit component as a numeral") {
    assertEquals(LeanParser.parseName("Foo.3.bar"), Name.parse("Foo").num(3).str("bar"))
    assertEquals(LeanParser.parseName("Nat.add"), Name.parse("Nat.add"))
    assertEquals(LeanParser.parseName(""), Name.anonymous)
    // The kernel's own splitter keeps every component a string.
    assertNotEquals(LeanParser.parseName("Foo.3"), Name.parse("Foo.3"))
    assertEquals(p("Foo.3"), Expr.Const(Name.parse("Foo").num(3), Nil))
  }
