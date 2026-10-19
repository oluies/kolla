package kolla.dsl

import kolla.kernel.*
import kolla.leanexport.*

/** Reduction against a real environment, which is what makes the answers
  * meaningful: `Nat.add` has to be the `Nat.add` Lean exported.
  */
class EvaluateSuite extends munit.FunSuite:

  private val profile = KernelProfile.v4_35

  /** The `nat-add` fixture's environment, replayed through the kernel. */
  private lazy val env: Environment =
    val in = getClass.getResourceAsStream("/nat-add-3.1.0.ndjson")
    assert(in != null, "missing test resource nat-add-3.1.0.ndjson")
    val src   = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    val items = ExportReader.fromLines(lines).items
    val r     = new Replay(items, profile, true)
    while r.hasNext do
      val step = r.next()
      assertEquals(step.outcome, ReplayOutcome.Checked, clue(step.names.toString))
    r.environment

  private def eval(src: String): Evaluate.Result =
    val term = LeanParser.parseOrThrow(src)
    Evaluate(env, profile, term) match
      case Right(r)  => r
      case Left(msg) => fail(s"$src: $msg")

  test("the environment really contains Nat.add") {
    // Without this the reductions below could be passing on an empty
    // environment, which would make them vacuous.
    assert(env.contains(Name.parse("Nat.add")), clue(env.size))
    assert(env.contains(Name.parse("Nat")))
  }

  test("a literal reduces to itself and types as Nat") {
    val r = eval("2")
    assertEquals(r.value, Expr.natLit(2))
    assertEquals(r.tpe, Expr.Const(Name.parse("Nat"), Nil))
  }

  test("addition on literals is computed") {
    assertEquals(eval("Nat.add 2 3").value, Expr.natLit(5))
    assertEquals(eval("Nat.add 0 0").value, Expr.natLit(0))
  }

  test("the arithmetic is arbitrary precision, as the kernel's is") {
    val big = BigInt(2).pow(80)
    assertEquals(eval(s"Nat.add ${big} 1").value, Expr.natLit(big + 1))
  }

  test("a nested application reduces throughout the spine") {
    assertEquals(eval("Nat.add (Nat.add 1 2) (Nat.add 3 4)").value, Expr.natLit(10))
  }

  test("a successor of a literal reduces") {
    assertEquals(eval("Nat.succ 41").value, Expr.natLit(42))
  }

  test("an ill-typed term is refused with the kernel's own reason") {
    val term = LeanParser.parseOrThrow("Nat.add 1 Nat")
    Evaluate(env, profile, term) match
      case Left(msg) => assert(msg.nonEmpty, clue(msg))
      case Right(r)  => fail(s"expected a rejection, got ${r.value}")
  }

  test("an unknown constant is refused") {
    val term = LeanParser.parseOrThrow("No.Such.Constant")
    assert(Evaluate(env, profile, term).isLeft)
  }

  test("reduction does not go under a binder, and says so by example") {
    // The documented limit: the body keeps its redex.
    val r = eval("fun (x : Nat) => Nat.add 2 3")
    r.value match
      case l: Expr.Lam => assertNotEquals(l.body, Expr.natLit(5))
      case other       => fail(s"expected a lambda, got $other")
  }
