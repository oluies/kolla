package kolla.difftest

import kolla.kernel.Name
import kolla.leanexport.{ReplayJson, ReplayOutcome, ReplayStep, ReplayTally}

class PlatformsSuite extends munit.FunSuite:

  private def n(s: String): Name = Name.parse(s)

  private val template =
    CheckerRun(KollaChecker.name, "leanprover/lean4:v4.35.0", "case-eta", "native", Vector.empty, 0L, 0L)

  private def decl(name: String, o: ReplayOutcome, nanos: Long = 1L): String =
    ReplayJson.declaration(n(name), o, nanos)

  private def summary(t: ReplayTally, wall: Long = 5L): String =
    ReplayJson.summary("x.export", "v4.35.0", "native", t, wall)

  private def tally(steps: (String, ReplayOutcome)*): ReplayTally =
    steps.foldLeft(ReplayTally())((t, s) => t.add(ReplayStep(List(n(s._1)), s._2)))

  test("a complete stream parses into verdicts") {
    val steps = Vector("A" -> ReplayOutcome.Checked, "B" -> ReplayOutcome.Rejected("bad", List("a =?= b")))
    val out   = steps.map((nm, o) => decl(nm, o)) :+ summary(tally(steps*))
    val r     = Platforms.parse(out.mkString("\n"), template, 0L)
    assertEquals(r.failure, None)
    assertEquals(r.results.length, 2)
    assertEquals(r.results(0), DeclResult(n("A"), Verdict.Accepted, 1L))
    assertEquals(r.results(1).verdict, Verdict.Rejected("bad"): Verdict)
    assertEquals(r.results(1).trace, List("a =?= b"))
    assertEquals(r.wallNanos, 5L)
  }

  test("a truncated stream is a failure, not a short run") {
    // Comparing a truncated stream against a full one would report agreement
    // on the part that arrived.
    val steps = Vector("A" -> ReplayOutcome.Checked, "B" -> ReplayOutcome.Checked)
    val out   = Vector(decl("A", ReplayOutcome.Checked), summary(tally(steps*)))
    val r     = Platforms.parse(out.mkString("\n"), template, 0L)
    assert(clue(r.failure).exists(_.contains("summary says 2")))
    assert(r.failure.exists(_.contains("1 were read")))
  }

  test("a stream with no summary is a failure") {
    val r = Platforms.parse(decl("A", ReplayOutcome.Checked), template, 0L)
    assertEquals(r.failure, Some("no summary line"))
  }

  test("an unreadable line is reported, and the first one wins") {
    val out = Vector(decl("A", ReplayOutcome.Checked), "{not json", "also not json")
    val r   = Platforms.parse(out.mkString("\n"), template, 0L)
    assert(clue(r.failure).exists(_.contains("unreadable output line")))
    assert(r.failure.exists(_.contains("{not json")))
  }

  test("every verdict label round-trips") {
    val outcomes = List(
      ReplayOutcome.Checked,
      ReplayOutcome.CarriedOver("from the file"),
      ReplayOutcome.Rejected("bad", Nil),
      ReplayOutcome.Failed("torn")
    )
    val out = outcomes.zipWithIndex.map((o, i) => decl(s"D$i", o)) :+
      summary(outcomes.zipWithIndex.foldLeft(ReplayTally())((t, p) => t.add(ReplayStep(List(n(s"D${p._2}")), p._1))))
    val r = Platforms.parse(out.mkString("\n"), template, 0L)
    assertEquals(r.failure, None)
    assertEquals(r.results.map(_.verdict.label), Vector("accepted", "not-checked", "rejected", "error"))
    assertEquals(r.accepted, 1)
    assertEquals(r.rejected, 1)
    assertEquals(r.notChecked, 1)
    assertEquals(r.errored, 1)
  }

  test("an unknown verdict is an error rather than silently accepted") {
    val line = """{"name":"A","verdict":"maybe","detail":null,"nanos":1,"trace":[]}"""
    val r    = Platforms.parse(s"$line\n${summary(tally("A" -> ReplayOutcome.Checked))}", template, 0L)
    assertEquals(r.results.head.verdict.label, "error")
    assert(clue(r.results.head.verdict.detail).exists(_.contains("maybe")))
  }

  test("a name with a numeric component survives the round trip") {
    // The wire format is `Name.toString`; a name that does not round-trip is a
    // name two platforms appear to disagree about. See docs/semantics.md N4.
    val name = Name.anonymous.str("_private").str("Init").str("Core").num(0).str("helper")
    val out  = Vector(decl(name.toString, ReplayOutcome.Checked), summary(tally(name.toString -> ReplayOutcome.Checked)))
    val r    = Platforms.parse(out.mkString("\n"), template, 0L)
    assertEquals(r.results.head.name, name)
    // And so the comparison finds it on both sides rather than on neither.
    val other = r.copy(platform = "js")
    assert(Compare.platforms(r, other).agrees)
  }

  test("blank lines are ignored") {
    val out = s"\n${decl("A", ReplayOutcome.Checked)}\n\n${summary(tally("A" -> ReplayOutcome.Checked))}\n"
    assertEquals(Platforms.parse(out, template, 0L).failure, None)
  }

  test("the wall time falls back to the measured one when the summary omits it") {
    val line = """{"summary":"x","profile":"v4.35.0","platform":"native","ok":true,"counts":{"total":0}}"""
    assertEquals(Platforms.parse(line, template, 77L).wallNanos, 77L)
  }
