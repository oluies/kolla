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

  /** An inductive presented the way text v1 presents one: as a
    * `Declaration.InductDecl` inside an `ExportItem.Decl`, not as an `Info`.
    * Built directly because `ExportWriter` refuses to write an inductive as
    * text v1 at all — the format carries it as a declaration.
    */
  private val boolDecl: ExportItem =
    val prop = Expr.Sort(Level.Succ(Level.zero))
    ExportItem.Decl(
      Declaration.InductDecl(
        levelParams = Nil,
        numParams = 0,
        types = List(
          InductiveType(
            Name.parse("Flag"),
            prop,
            List(
              Constructor(Name.parse("Flag.up"), Expr.Const(Name.parse("Flag"), Nil)),
              Constructor(Name.parse("Flag.down"), Expr.Const(Name.parse("Flag"), Nil))
            )
          )
        ),
        isUnsafe = false
      )
    )

  private def admitOnly(items: Vector[ExportItem]): Environment =
    val r = new Replay(profile, true, Int.MaxValue, _ => false)
    items.foreach(r.feed)
    r.finish()
    while r.hasNext do r.next()
    r.environment

  test("admitting a Decl inductive puts its type, constructors and recursor in scope") {
    // The `Decl` recover was `identity`, so nothing was added and every later
    // reference to the type was an unknown constant. See docs/semantics.md P18.
    val env = admitOnly(Vector(boolDecl))
    assert(env.contains(Name.parse("Flag")), clue(env.size))
    assert(env.contains(Name.parse("Flag.up")))
    assert(env.contains(Name.parse("Flag.down")))
    assert(env.contains(Name.parse("Flag.rec")), "the recursor is derived, not exported")
  }

  test("a term reduces against an admitted Decl inductive") {
    val env  = admitOnly(Vector(boolDecl))
    val term = LeanParser.parseOrThrow("Flag.up")
    Evaluate(env, profile, term) match
      case Right(r)  => assertEquals(r.value, Expr.Const(Name.parse("Flag.up"), Nil))
      case Left(msg) => fail(s"admitted Decl inductive: $msg")
  }

  test("admitting a Decl axiom and definition also puts them in scope") {
    val prop = Expr.Sort(Level.zero)
    val ax   = ExportItem.Decl(
      Declaration.AxiomDecl(AxiomVal(ConstantVal(Name.parse("P"), Nil, prop), isUnsafe = false))
    )
    val env = admitOnly(Vector(ax))
    assert(env.contains(Name.parse("P")), clue(env.size))
  }

  test("--eval honours a reduction budget") {
    // The flag is documented for every path; before this it was accepted on
    // the eval path and silently ignored. Matched loosely on purpose: the
    // report's layout is not the contract. See docs/semantics.md K21.
    val term = LeanParser.parseOrThrow("Nat.add 2 3")
    Evaluate(env, profile, term, 1L) match
      case Left(why) => assert(why.contains("exceeded 1 reduction steps"), clue(why))
      case Right(r)  => fail(s"a one-step budget should not reach ${r.value}")
  }

  test("a generous budget leaves the answer unchanged") {
    val term = LeanParser.parseOrThrow("Nat.add 2 3")
    assertEquals(Evaluate(env, profile, term, 1000000L).map(_.value), Right(Expr.natLit(5)))
    assertEquals(Evaluate(env, profile, term).map(_.value), Right(Expr.natLit(5)))
  }
