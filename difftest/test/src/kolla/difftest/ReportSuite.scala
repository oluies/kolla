package kolla.difftest

import kolla.kernel.Name

class ReportSuite extends munit.FunSuite:

  def n(s: String): Name = Name.parse(s)

  def run(checker: String, corpus: String, rs: (String, Verdict)*): CheckerRun =
    CheckerRun(
      checker, "leanprover/lean4:v4.35.0", corpus, "jvm",
      rs.toVector.map((name, v) => DeclResult(n(name), v, 1000L)), 10_000L, 4096L
    )

  def report(runs: CheckerRun*): Report =
    Report("abc123", "2026-01-01T00:00:00Z", runs.toVector, Vector.empty, Vector.empty)

  test("a run with only acceptances agrees") {
    val r = report(run("kolla", "case-eta", "A" -> Verdict.Accepted, "B" -> Verdict.Accepted))
    assert(r.agrees)
    assertEquals(r.falseRejections.length, 0)
  }

  test("a rejection on a positive corpus is a false rejection, with no reference needed") {
    val r = report(run("kolla", "case-eta", "A" -> Verdict.Accepted, "B" -> Verdict.Rejected("bad")))
    assert(!r.agrees)
    assertEquals(r.falseRejections.length, 1)
    assertEquals(r.falseRejections.head.unexpected.map(_.name), Vector(n("B")))
    assert(clue(r.render).contains("false rejections"))
    assert(clue(r.render).contains("DISAGREE"))
  }

  test("an error on a positive corpus counts too") {
    val r = report(run("kolla", "case-eta", "A" -> Verdict.Error("crash")))
    assert(!r.agrees)
    assertEquals(r.falseRejections.head.unexpected.length, 1)
  }

  test("a reference checker rejecting is not a false rejection of kolla's") {
    // Only kolla's runs are held to the positive-corpus expectation; a
    // reference that rejects is reported through the comparison instead.
    val r = report(run(Lean4Checker.name, "case-eta", "A" -> Verdict.Rejected("bad")))
    assertEquals(r.falseRejections.length, 0)
  }

  test("a negative corpus must reject something") {
    val accepting = run("kolla", "bad-addfalse", "A" -> Verdict.Accepted).copy(expectRejection = true)
    val r = report(accepting)
    assert(!r.agrees)
    assertEquals(r.missedRejections.length, 1)
    assertEquals(r.falseRejections.length, 0)
    assert(clue(r.render).contains("missed rejections"))
  }

  test("a rejection on a negative corpus is what was asked for") {
    val rejecting =
      run("kolla", "bad-addfalse", "A" -> Verdict.Accepted, "B" -> Verdict.Rejected("type mismatch"))
        .copy(expectRejection = true)
    val r = report(rejecting)
    assert(r.agrees)
    assertEquals(r.falseRejections.length, 0)
    assertEquals(r.missedRejections.length, 0)
  }

  test("a reference that accepts a negative corpus is caught too") {
    val r = report(run(Lean4Checker.name, "bad-addfalse", "c" -> Verdict.Accepted).copy(expectRejection = true))
    assertEquals(r.missedRejections.length, 1)
  }

  test("a run that failed outright does not agree") {
    val r = report(run("kolla", "case-eta").copy(failure = Some("export unreadable")))
    assert(!r.agrees)
    assert(clue(r.render).contains("FAILED"))
  }

  test("the json carries the false-rejection count") {
    val r = report(run("kolla", "case-eta", "A" -> Verdict.Rejected("bad"), "B" -> Verdict.Rejected("bad")))
    assert(clue(r.json).contains("\"falseRejections\":2"), clue(r.json.take(400)))
  }

  test("a corpus-level verdict summarises a run") {
    assertEquals(run("kolla", "c", "A" -> Verdict.Accepted).overall, Verdict.Accepted: Verdict)
    assertEquals(
      run("kolla", "c", "A" -> Verdict.Accepted, "B" -> Verdict.Rejected("bad")).overall.label,
      "rejected"
    )
    // Nothing judged is not acceptance.
    assertEquals(
      run("kolla", "c", "A" -> Verdict.NotChecked("carried over")).overall.label,
      "not-checked"
    )
    assertEquals(run("kolla", "c").copy(failure = Some("boom")).overall.label, "error")
  }

  test("a rejection is reported ahead of an error in the corpus verdict") {
    val r = run("kolla", "c", "A" -> Verdict.Error("crash"), "B" -> Verdict.Rejected("bad"))
    assertEquals(r.overall.label, "rejected")
    assert(clue(r.overall.detail.get).contains("B"))
  }

  test("overall agreement needs a judgement on both sides") {
    val ref  = run(Lean4Checker.name, "c", "<corpus>" -> Verdict.Accepted)
    val subj = run("kolla", "c", "A" -> Verdict.Accepted)
    assert(Compare.overall(ref, subj).agrees)

    val rejecting = run("kolla", "c", "A" -> Verdict.Rejected("bad"))
    assert(!Compare.overall(ref, rejecting).agrees)

    val unknown = run(Lean4Checker.name, "c").copy(failure = Some("unavailable"))
    assert(!Compare.overall(unknown, subj).agrees)
    assert(clue(Compare.overall(unknown, subj).render).contains("DISAGREES"))
  }

  test("history rows round-trip through the tsv") {
    val r   = report(run("kolla", "case-eta", "A" -> Verdict.Accepted, "B" -> Verdict.Rejected("bad")))
    val row = History.row(r.commit, r.startedAt, r.runs.head)
    val back = History.parse(History.header + "\n" + row.tsv + "\n")
    assertEquals(back, List(row))
    assertEquals(row.declarations, 2)
    assertEquals(row.accepted, 1)
    assertEquals(row.rejected, 1)
    assertEquals(row.peakHeapBytes, 4096L)
  }

  test("history skips a malformed line rather than failing") {
    assertEquals(History.parse(History.header + "\nnot\ta\trow\n"), Nil)
  }
