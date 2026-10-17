package kolla.difftest

import kolla.kernel.Name

class CompareSuite extends munit.FunSuite:

  def n(s: String): Name = Name.parse(s)
  def run(
      checker: String,
      rs: (String, Verdict)*
  ): CheckerRun =
    CheckerRun(checker, "v4.35.0", "handwritten", "jvm",
      rs.toVector.map((name, v) => DeclResult(n(name), v, 1000L)), 10_000L, 0L)

  test("identical judgements agree") {
    val a = run("lean4checker", "A" -> Verdict.Accepted, "B" -> Verdict.Rejected("x"))
    val b = run("kolla", "A" -> Verdict.Accepted, "B" -> Verdict.Rejected("y"))
    val c = Compare(a, b)
    assert(c.agrees)
    assertEquals(c.comparable, 2)
    // The rejection reasons need not match, only the verdicts.
    assertEquals(c.disagreements.length, 0)
  }

  test("a differing verdict is a disagreement") {
    val a = run("lean4checker", "A" -> Verdict.Accepted)
    val b = run("kolla", "A" -> Verdict.Rejected("type mismatch"))
    val c = Compare(a, b)
    assert(!c.agrees)
    assertEquals(c.disagreements.length, 1)
    assertEquals(c.disagreements.head.name, n("A"))
    assertEquals(c.disagreements.head.reference, Verdict.Accepted: Verdict)
    assert(clue(c.render).contains("type mismatch"))
  }

  test("a disagreement carries kolla's defeq trace") {
    val a = run("lean4checker", "A" -> Verdict.Accepted)
    val b = CheckerRun("kolla", "v4.35.0", "handwritten", "jvm",
      Vector(DeclResult(n("A"), Verdict.Rejected("mismatch"), 1L, List("x =?= y"))), 1L, 0L)
    val c = Compare(a, b)
    assertEquals(c.disagreements.head.trace, List("x =?= y"))
    assert(clue(c.render).contains("x =?= y"))
    assert(clue(c.json).contains("x =?= y"))
  }

  test("not-checked is not agreement") {
    val a = run("lean4checker", "A" -> Verdict.Accepted)
    val b = run("kolla", "A" -> Verdict.NotChecked("carried over from the file"))
    val c = Compare(a, b)
    assert(!c.agrees, "a NotChecked subject must not count as agreement")
    assertEquals(c.disagreements.length, 0)
    assertEquals(c.onlyInReference, Vector(n("A")))
    assertEquals(c.comparable, 0)
  }

  test("a declaration missing from one side is reported") {
    val a = run("lean4checker", "A" -> Verdict.Accepted, "B" -> Verdict.Accepted)
    val b = run("kolla", "A" -> Verdict.Accepted)
    val c = Compare(a, b)
    assert(!c.agrees)
    assertEquals(c.onlyInReference, Vector(n("B")))
    assertEquals(c.onlyInSubject, Vector.empty)
  }

  test("an error verdict is never agreement") {
    val a = run("lean4checker", "A" -> Verdict.Accepted)
    val b = run("kolla", "A" -> Verdict.Error("timed out"))
    assert(!Compare(a, b).agrees)
  }

  test("the time ratio is subject over reference") {
    val a = CheckerRun("lean4checker", "t", "c", "jvm", Vector.empty, 100L, 0L)
    val b = CheckerRun("kolla", "t", "c", "jvm", Vector.empty, 250L, 0L)
    assertEquals(Compare(a, b).timeRatio, 2.5)
    val z = CheckerRun("lean4checker", "t", "c", "jvm", Vector.empty, 0L, 0L)
    assert(Compare(z, b).timeRatio.isNaN)
  }

  test("disagreements are reported in name order") {
    val a = run("lean4checker", "Z" -> Verdict.Accepted, "A" -> Verdict.Accepted)
    val b = run("kolla", "Z" -> Verdict.Rejected("z"), "A" -> Verdict.Rejected("a"))
    assertEquals(Compare(a, b).disagreements.map(_.name.toString), Vector("A", "Z"))
  }

  test("the report is well-formed JSON") {
    val a = run("lean4checker", "A" -> Verdict.Accepted)
    val b = run("kolla", "A" -> Verdict.Rejected("bad \"quote\" and \\slash"))
    val j = Compare(a, b).json
    // Parse it back with the export module's parser.
    val parsed = kolla.leanexport.Json.parse(j)
    val fields = parsed.asInstanceOf[kolla.leanexport.Json.Obj].fields
    assertEquals(fields("agrees"), kolla.leanexport.Json.Bool(false))
    assertEquals(fields("comparable"), kolla.leanexport.Json.Num(BigInt(1)))
  }

  test("counts are reported per verdict kind") {
    val r = run("kolla",
      "A" -> Verdict.Accepted,
      "B" -> Verdict.Rejected("x"),
      "C" -> Verdict.NotChecked("y"),
      "D" -> Verdict.Error("z")
    )
    assertEquals(r.accepted, 1)
    assertEquals(r.rejected, 1)
    assertEquals(r.notChecked, 1)
    assertEquals(r.errored, 1)
    assert(kolla.leanexport.Json.parse(r.json).isInstanceOf[kolla.leanexport.Json.Obj])
  }
