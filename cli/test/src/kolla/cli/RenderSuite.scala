package kolla.cli

import kolla.kernel.Name
import kolla.leanexport.{ReplayOutcome, ReplayStep, ReplayTally}

class RenderSuite extends munit.FunSuite:

  def n(s: String): Name = Name.parse(s)

  def step(names: List[String], o: ReplayOutcome): ReplayStep = ReplayStep(names.map(n), o)

  test("a tally counts every name a step declared, not every step") {
    // An inductive block is one step and many declarations.
    val t = ReplayTally().add(step(List("Nat", "Nat.zero", "Nat.succ", "Nat.rec"), ReplayOutcome.Checked))
    assertEquals(t.accepted, 4)
    assertEquals(t.total, 4)
    assert(t.ok)
  }

  test("nothing judged is not a pass") {
    assert(!ReplayTally().ok)
    assert(!ReplayTally().add(step(List("A"), ReplayOutcome.CarriedOver("from the file"))).ok)
  }

  test("the first rejection is kept and later ones do not replace it") {
    val t = ReplayTally()
      .add(step(List("A"), ReplayOutcome.Checked))
      .add(step(List("B"), ReplayOutcome.Rejected("bad B", List("x =?= y"))))
      .add(step(List("C"), ReplayOutcome.Rejected("bad C", Nil)))
    assertEquals(t.rejected, 2)
    assertEquals(t.firstRejection.map(_._1), Some(n("B")))
    assertEquals(t.firstRejection.map(_._3), Some(List("x =?= y")))
    assert(!t.ok)
  }

  test("an error counts apart from a rejection and also fails the run") {
    val t = ReplayTally().add(step(List("A"), ReplayOutcome.Checked)).add(step(List("B"), ReplayOutcome.Failed("torn")))
    assertEquals(t.failed, 1)
    assertEquals(t.rejected, 0)
    assert(!t.ok)
  }

  test("not-reached declarations are counted but judged nothing") {
    val t = ReplayTally().add(step(List("A"), ReplayOutcome.Checked)).addNotReached(9)
    assertEquals(t.notReached, 9)
    assertEquals(t.total, 10)
    assert(clue(t.counts).contains("9 not reached"))
    // They do not make the run fail: the first rejection already did that.
    assert(t.ok)
  }

  test("the summary names the first rejection and its trace") {
    val t = ReplayTally().add(step(List("B"), ReplayOutcome.Rejected("type mismatch", List("a =?= b"))))
    val s = Render.summary("x.export", "v4.35.0", t, 2_000_000L)
    assert(clue(s).contains("x.export"))
    assert(s.contains("v4.35.0"))
    assert(s.contains("2ms"))
    assert(s.contains("first rejection: B"))
    assert(s.contains("type mismatch"))
    assert(s.contains("a =?= b"))
  }

  test("a clean summary has no rejection section") {
    val s = Render.summary("x", "v4.35.0", ReplayTally().add(step(List("A"), ReplayOutcome.Checked)), 0L)
    assert(!clue(s).contains("first rejection"))
  }

  test("the per-declaration json carries the verdict, detail and trace") {
    val j = Render.json(n("B"), ReplayOutcome.Rejected("bad", List("a =?= b")), 42L)
    assert(clue(j).contains("\"name\":\"B\""))
    assert(j.contains("\"verdict\":\"rejected\""))
    assert(j.contains("\"detail\":\"bad\""))
    assert(j.contains("\"nanos\":42"))
    assert(j.contains("\"trace\":[\"a =?= b\"]"))
  }

  test("an accepted declaration has a null detail and an empty trace") {
    val j = Render.json(n("A"), ReplayOutcome.Checked, 1L)
    assert(clue(j).contains("\"detail\":null"))
    assert(j.contains("\"trace\":[]"))
  }

  test("the summary json names the platform it ran on") {
    val t = ReplayTally().add(step(List("A"), ReplayOutcome.Checked))
    val j = Render.summaryJson("x", "v4.35.0", "native", t, 5L)
    assert(clue(j).contains("\"platform\":\"native\""))
    assert(j.contains("\"ok\":true"))
    assert(j.contains("\"total\":1"))
  }

  test("json escapes what a Lean name or a kernel message can contain") {
    assertEquals(Json.str("a\"b\\c"), "\"a\\\"b\\\\c\"")
    assertEquals(Json.str("a\nb"), "\"a\\nb\"")
    assertEquals(Json.str("\u0001"), "\"\\u0001\"")
  }

  test("every outcome has a distinct label") {
    val labels = List(
      ReplayOutcome.Checked,
      ReplayOutcome.CarriedOver("x"),
      ReplayOutcome.Rejected("x", Nil),
      ReplayOutcome.Failed("x")
    ).map(Render.label)
    assertEquals(labels, List("accepted", "carried-over", "rejected", "error"))
    assertEquals(labels.distinct.length, 4)
  }
