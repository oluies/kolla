package kolla.leanexport

import kolla.kernel.*

/** Checking a declaration against an environment built by admitting the rest
  * must give the same verdict as checking everything.
  *
  * On a Mathlib closure it does not: two declarations under `Nat.Prime` are
  * accepted when their dependencies are checked and rejected when they are
  * admitted, with environments that differ only in the binder names of
  * derived declarations. See docs/semantics.md P21.
  */
class AdmitVerdictSuite extends munit.FunSuite:

  private def verdicts(xs: Vector[ExportItem], p: KernelProfile, check: Name => Boolean) =
    val r = new Replay(p, true, Int.MaxValue, check)
    xs.foreach(r.feed)
    r.finish()
    val out = Vector.newBuilder[(String, String)]
    while r.hasNext do
      val st = r.next()
      st.names.foreach(n => out += ((n.toString, ReplayTally.label(st.outcome))))
    out.result()

  test("admitting the rest does not change a checked declaration's verdict") {
    // Each fixture, each declaration checked alone against an admitted
    // environment, compared with the all-checked verdict for that same name.
    val compared = scala.collection.mutable.LinkedHashMap.empty[String, Int]
    for f <- FixtureFiles.names do
      val p   = FixtureFiles.profileOf(f)
      val xs  = FixtureFiles.items(f)
      val all = verdicts(xs, p, _ => true).toMap
      for (name, expected) <- all if expected == "accepted" do
        val one = verdicts(xs, p, _.toString == name).toMap
        assertEquals(one.get(name), Some(expected), clue((f, name)))
        compared.update(f, compared.getOrElse(f, 0) + 1)
    // Without this the loops could iterate nothing: if no declaration came
    // back accepted, the assertion above would never run and the test would
    // pass having compared nothing. Every fixture has to contribute, which is
    // derived from the fixtures rather than a number chosen by hand.
    val silent = FixtureFiles.names.filterNot(compared.contains)
    assertEquals(silent, Nil, clue(compared))
  }

  test("an uninstallable quotient package still puts its name in scope") {
    // `Quot.add` refuses when `Eq` is missing or misshapen, and a `recover`
    // runs inside a `Try`, so letting that escape would leave none of the four
    // constants in scope and turn one disagreement into a cascade of
    // unknown-constant failures. P6 is what that would break.
    val xs = FixtureFiles.items("quot-sound-3.1.0.ndjson")
    // Drop `Eq` entirely, which is what makes the package uninstallable.
    val without = xs.filterNot(_.names.exists(_.toString == "Eq"))
    assertNotEquals(without.length, xs.length, "the fixture should declare Eq")

    val r = new Replay(KernelProfile.v4_35, true, Int.MaxValue, _ => false)
    without.foreach(r.feed)
    r.finish()
    while r.hasNext do r.next()
    val env = r.environment
    // The point: `Quot` is present even though the package could not be
    // installed, so later declarations resolve rather than cascading.
    assert(env.contains(Name.parse("Quot")), clue(env.size))
    assert(!env.quotInitialized, "the package was not installed, and says so")
  }
