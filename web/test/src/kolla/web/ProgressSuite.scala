package kolla.web

import kolla.kernel.Name
import kolla.leanexport.{ReplayOutcome, ReplayStep, ReplayTally}

class ProgressSuite extends munit.FunSuite:

  private def step(name: String, o: ReplayOutcome): ReplayStep = ReplayStep(List(Name.parse(name)), o)

  private def accepted(k: Int): ReplayTally =
    (1 to k).foldLeft(ReplayTally())((t, i) => t.add(step(s"D$i", ReplayOutcome.Checked)))

  test("a run in progress reports where it is, not a verdict") {
    val p = Progress(accepted(10), 10, 40, 5L, done = false)
    assertEquals(p.percent, 25)
    assertEquals(p.status, "checking 10 of 40")
    assertEquals(p.verdictClass, "running")
  }

  test("a finished clean run is accepted") {
    val p = Progress(accepted(40), 40, 40, 12L, done = true)
    assertEquals(p.percent, 100)
    assertEquals(p.status, "accepted 40 declarations")
    assertEquals(p.verdictClass, "accepted")
    assertEquals(p.timing, "12ms")
    assertEquals(p.firstRejection, None)
  }

  test("a finished run with a rejection is rejected and names the first one") {
    val t = accepted(3).add(step("B", ReplayOutcome.Rejected("type mismatch\nin B", Nil)))
    val p = Progress(t, 4, 4, 1L, done = true)
    assertEquals(p.verdictClass, "rejected")
    assertEquals(p.status, "rejected 1 of 4")
    // The browser shows one line, so the kernel's multi-line reason is flattened.
    assertEquals(p.firstRejection, Some("B: type mismatch in B"))
  }

  test("an empty file is neither accepted nor rejected") {
    val p = Progress(ReplayTally(), 0, 0, 0L, done = true)
    assertEquals(p.verdictClass, "empty")
    assertEquals(p.status, "nothing to check")
    assertEquals(p.timing, "")
    // The bar is full rather than stuck at nothing, which would look like a hang.
    assertEquals(p.percent, 100)
  }

  test("an errored declaration fails the run like a rejection") {
    val t = accepted(1).add(step("B", ReplayOutcome.Failed("torn file")))
    val p = Progress(t, 2, 2, 1L, done = true)
    assertEquals(p.verdictClass, "rejected")
    assertEquals(p.firstRejection, Some("B: torn file"))
  }

  test("the percentage is monotone and never exceeds a hundred") {
    val sizes = List(1, 7, 40, 3527)
    sizes.foreach { size =>
      val seen = (0 to size).map(i => Progress(ReplayTally(), i, size, 0L, done = false).percent)
      assert(seen.forall(p => p >= 0 && p <= 100), clue((size, seen.filter(p => p < 0 || p > 100))))
      assertEquals(seen, seen.sorted, clue(size))
      assertEquals(seen.last, 100, clue(size))
    }
  }
