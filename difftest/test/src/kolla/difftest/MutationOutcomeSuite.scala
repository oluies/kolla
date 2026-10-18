package kolla.difftest

import kolla.kernel.Name

class MutationOutcomeSuite extends munit.FunSuite:

  private def n(s: String): Name = Name.parse(s)

  private def mutation(kind: MutationKind): Mutation =
    Mutation(kind, 1L, n("Target"), s"${kind.slug} on Target", Vector.empty)

  private def run(rs: (String, Verdict)*): CheckerRun =
    CheckerRun(
      KollaChecker.name, "leanprover/lean4:v4.35.0", "case-eta", "jvm",
      rs.toVector.map((name, v) => DeclResult(n(name), v, 1L)), 1L, 0L
    )

  private def outcome(kind: MutationKind, baseline: Set[Name], rs: (String, Verdict)*): MutationOutcome =
    MutationOutcome(mutation(kind), "leanprover/lean4:v4.35.0", "case-eta", run(rs*), baseline)

  test("a rejection the baseline already had is not the mutation's") {
    // docs/semantics.md P11: otherwise a corpus with a pre-existing failure
    // makes every mutant look correct, including the one kind that must stay
    // accepted.
    val o = outcome(
      MutationKind.ChangeDefinitionalHeight,
      Set(n("appendLit")),
      "A" -> Verdict.Accepted,
      "appendLit" -> Verdict.Rejected("type mismatch")
    )
    assert(!o.expectedRejection)
    assert(!o.rejected)
    assertEquals(o.rejectedName, None)
    assert(o.asExpected)
  }

  test("a rejection the baseline did not have is the mutation's") {
    val o = outcome(
      MutationKind.SwapConstructorIndices,
      Set(n("appendLit")),
      "appendLit" -> Verdict.Rejected("type mismatch"),
      "Nat" -> Verdict.Rejected("constructor index")
    )
    assert(o.expectedRejection)
    assert(o.rejected)
    assertEquals(o.rejectedName, Some("Nat"))
    assertEquals(o.newRejections.map(_.name), Vector(n("Nat")))
    assert(o.asExpected)
    assert(clue(o.render).contains("Nat"))
  }

  test("a mutation that should have been caught and was not is reported bad") {
    val o = outcome(MutationKind.AlterRecursorRuleRhs, Set.empty, "A" -> Verdict.Accepted)
    assert(o.expectedRejection)
    assert(!o.rejected)
    assert(!o.asExpected)
    assert(clue(o.render).startsWith("  BAD "))
  }

  test("a height change that is rejected is reported bad") {
    // The kind exists to show that a reducibility hint only steers which side
    // `is_def_eq` unfolds first, so a rejection here is a real failure.
    val o = outcome(MutationKind.ChangeDefinitionalHeight, Set.empty, "Nat" -> Verdict.Rejected("x"))
    assert(!o.expectedRejection)
    assert(o.rejected)
    assert(!o.asExpected)
  }

  test("a run that failed outright is never as expected") {
    val base = outcome(MutationKind.RetypeAxiom, Set.empty, "A" -> Verdict.Rejected("x"))
    assert(base.asExpected)
    assert(!base.copy(run = base.run.copy(failure = Some("export unreadable"))).asExpected)
  }

  test("the baseline size is recorded in the json") {
    val o = outcome(MutationKind.RemoveLetValue, Set(n("a"), n("b")), "c" -> Verdict.Rejected("x"))
    assert(clue(o.json).contains("\"baselineRejected\":2"))
    assert(o.json.contains("\"rejectedName\":\"c\""))
  }
