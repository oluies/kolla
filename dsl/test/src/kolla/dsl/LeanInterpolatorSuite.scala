package kolla.dsl

import kolla.kernel.*
import kolla.dsl.LeanInterpolator.lean

class LeanInterpolatorSuite extends munit.FunSuite:

  val nat = Expr.const("Nat")
  def bv(i: Int) = Expr.BVar(i)

  test("the interpolator agrees with the parser") {
    assertEquals(lean"Nat", nat)
    assertEquals(lean"fun (x : Nat) => x", LeanParser.parseOrThrow("fun (x : Nat) => x"))
    assertEquals(lean"forall (x : Nat), x", LeanParser.parseOrThrow("forall (x : Nat), x"))
    assertEquals(lean"Nat -> Nat", LeanParser.parseOrThrow("Nat -> Nat"))
    assertEquals(lean"let x : Nat := 3; x", LeanParser.parseOrThrow("let x : Nat := 3; x"))
    assertEquals(lean"Sort (max u v)", LeanParser.parseOrThrow("Sort (max u v)"))
    assertEquals(lean"List.{u} Nat", LeanParser.parseOrThrow("List.{u} Nat"))
  }

  test("binder names and annotations are preserved exactly") {
    val e = lean"fun {A : Sort u} (a : A) => a"
    assert(Expr.isBiEqual(e, LeanParser.parseOrThrow("fun {A : Sort u} (a : A) => a")))
    val outer = e.asInstanceOf[Expr.Lam]
    assertEquals(outer.binderName, Name.mkSimple("A"))
    assertEquals(outer.binderInfo, BinderInfo.Implicit)
    val inner = outer.body.asInstanceOf[Expr.Lam]
    assertEquals(inner.binderName, Name.mkSimple("a"))
    assertEquals(inner.binderInfo, BinderInfo.Default)
    assertEquals(inner.body, bv(0))
  }

  test("literals survive, including large numerals") {
    assertEquals(lean"42", Expr.natLit(42))
    assertEquals(lean"123456789012345678901234567890", Expr.natLit(BigInt("123456789012345678901234567890")))
    assertEquals(lean""""hi"""", Expr.strLit("hi"))
  }

  test("numeral name components survive") {
    assertEquals(lean"Foo.3.bar", Expr.const(Name.parse("Foo").num(3).str("bar")))
  }

  test("an Expr splice is inserted") {
    val two = Expr.natLit(2)
    assertEquals(lean"Nat.add $two 3", Expr.mkAppN(Expr.const("Nat.add"), Seq(two, Expr.natLit(3))))
    val f = lean"fun (x : Nat) => x"
    assertEquals(lean"$f 5", Expr.App(f, Expr.natLit(5)))
  }

  test("a Level splice becomes a sort and a Name splice a constant") {
    val u: Level = Level.Param(Name.mkSimple("u"))
    assertEquals(lean"$u", Expr.Sort(u))
    val n: Name = Name.parse("Nat.add")
    assertEquals(lean"$n", Expr.const("Nat.add"))
  }

  test("several splices are matched positionally") {
    val a = Expr.const("A")
    val b = Expr.const("B")
    assertEquals(lean"f $a $b", Expr.mkAppN(Expr.const("f"), Seq(a, b)))
    assertEquals(lean"f $b $a", Expr.mkAppN(Expr.const("f"), Seq(b, a)))
  }

  test("a splice inside a binder is inserted unchanged") {
    // The splice is closed, so no index shifting is needed.
    val body = Expr.const("C")
    assertEquals(
      lean"fun (x : Nat) => $body",
      Expr.Lam(Name.mkSimple("x"), nat, body, BinderInfo.Default)
    )
  }

  test("the identity function type checks") {
    // id : forall (A : Sort u), A -> A := fun (A : Sort u) (a : A) => a
    val idType = lean"forall (A : Sort u) (a : A), A"
    val idValue = lean"fun (A : Sort u) (a : A) => a"
    val u = Name.mkSimple("u")
    val env = Environment.empty
    val tc  = new TypeChecker(env, KernelProfile.v4_35)
    val inferred = tc.check(idValue, List(u))
    assert(tc.isDefEq(inferred, idType), clue(Pretty.expr(inferred)))
    // And the type itself is a sort.
    tc.ensureSort(tc.check(idType, List(u)), idType)
  }

  test("a syntax error is a compile error") {
    // Checked by the negative compilation tests below; this records the intent.
    assert(compileErrors("""import kolla.dsl.LeanInterpolator.lean; lean"fun x => x"""").nonEmpty)
    assert(compileErrors("""import kolla.dsl.LeanInterpolator.lean; lean"(Nat"""").nonEmpty)
    assert(
      compileErrors("""import kolla.dsl.LeanInterpolator.lean; lean"Nat Nat)"""").contains("syntax error")
    )
  }

  test("a splice of the wrong type is a compile error") {
    assert(
      compileErrors(
        "import kolla.dsl.LeanInterpolator.lean; val x: Int = 1; lean\"f $x\""
      ).nonEmpty
    )
  }
