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

    // An unavailable reference does not agree, because it judged nothing. It
    // is no longer rendered as a disagreement: it said nothing about the
    // corpus, and calling that a difference of opinion is what P17 corrects.
    val unknown = run(Lean4Checker.name, "c").copy(failure = Some("unavailable"))
    val o       = Compare.overall(unknown, subj)
    assert(!o.agrees)
    assert(!o.comparable)
    assert(o.referenceUnavailable)
    assert(clue(o.render).contains("NO REFERENCE VERDICT"))
    assert(!clue(o.render).contains("DISAGREES"))
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

  /** A corpus-level reference run, as `lean4checker` and nanoda produce. */
  def overallRun(checker: String, corpus: String, v: Verdict): CheckerRun =
    CheckerRun(
      checker, "leanprover/lean4:v4.28.0", corpus, "jvm",
      Vector(DeclResult(n(s"<corpus:$corpus>"), v, 1000L)), 10_000L, 0L,
      perDeclaration = false
    )

  def reportWithOverall(runs: Vector[CheckerRun], os: Vector[OverallAgreement]): Report =
    Report("abc123", "2026-01-01T00:00:00Z", runs, Vector.empty, os)

  test("a reference that reached no verdict is not a disagreement") {
    // The v4.28.0 mathlib-sample case: kolla accepted all 17,240 declarations
    // and lean4checker timed out. Silence from the reference says nothing
    // about the corpus, so it must not fail the run.
    val kolla = overallRun("kolla", "mathlib-sample", Verdict.Accepted)
    val ref   = overallRun("lean4checker", "mathlib-sample", Verdict.Error("timed out after 1800s"))
    val o     = Compare.overall(ref, kolla)
    assert(!o.agrees)
    assert(!o.comparable)
    assert(o.referenceUnavailable)
    assert(reportWithOverall(Vector(kolla, ref), Vector(o)).agrees)
    assert(clue(o.render).contains("NO REFERENCE VERDICT"))
  }

  test("a real disagreement still fails") {
    val kolla = overallRun("kolla", "std", Verdict.Accepted)
    val ref   = overallRun("lean4checker", "std", Verdict.Rejected("Nat.add: bad"))
    val o     = Compare.overall(ref, kolla)
    assert(!o.agrees)
    assert(o.comparable, "both sides judged, so it is comparable")
    assert(!o.referenceUnavailable)
    assert(!reportWithOverall(Vector(kolla, ref), Vector(o)).agrees)
    assert(clue(o.render).contains("DISAGREES"))
  }

  test("a subject that reached no verdict still fails") {
    // The asymmetry is the point: silence from kolla is not excused.
    val kolla = overallRun("kolla", "std", Verdict.Error("ran out of memory"))
    val ref   = overallRun("lean4checker", "std", Verdict.Accepted)
    val o     = Compare.overall(ref, kolla)
    assert(!o.agrees)
    assert(!o.comparable)
    assert(!o.referenceUnavailable, "the reference judged; it is the subject that did not")
    assert(!reportWithOverall(Vector(kolla, ref), Vector(o)).agrees)
  }

  test("neither side judging still fails") {
    val kolla = overallRun("kolla", "std", Verdict.NotChecked("nothing"))
    val ref   = overallRun("lean4checker", "std", Verdict.Error("timed out"))
    val o     = Compare.overall(ref, kolla)
    assert(!o.referenceUnavailable)
    assert(!reportWithOverall(Vector(kolla, ref), Vector(o)).agrees)
  }

  test("agreement still agrees") {
    val kolla = overallRun("kolla", "init", Verdict.Accepted)
    val ref   = overallRun("lean4checker", "init", Verdict.Accepted)
    val o     = Compare.overall(ref, kolla)
    assert(o.agrees && o.comparable && !o.referenceUnavailable)
    assert(reportWithOverall(Vector(kolla, ref), Vector(o)).agrees)
  }
