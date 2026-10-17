package kolla.difftest

import org.scalacheck.{Arbitrary, Gen}
import org.scalacheck.Prop.forAll

class DiffSuite extends munit.ScalaCheckSuite:

  /** Short lines from a small alphabet, so collisions and runs are common. */
  private val line: Gen[String] = Gen.oneOf("a", "b", "c", "d", "e", "", "x y", "#")
  private val lines: Gen[Vector[String]] = Gen.choose(0, 24).flatMap(Gen.listOfN(_, line)).map(_.toVector)

  given Arbitrary[Vector[String]] = Arbitrary(lines)

  property("applying a diff reproduces the target") {
    forAll { (a: Vector[String], b: Vector[String]) =>
      Diff.apply(a, Diff.unified(a, b)) == b
    }
  }

  property("a diff of equal inputs is empty") {
    forAll { (a: Vector[String]) => Diff.unified(a, a).isEmpty }
  }

  property("hunk headers are in increasing order and non-overlapping") {
    forAll { (a: Vector[String], b: Vector[String]) =>
      val hunks = """@@ -(\d+),(\d+) \+(\d+),(\d+) @@""".r
        .findAllMatchIn(Diff.unified(a, b))
        .map(m => (m.group(1).toInt, m.group(2).toInt))
        .toList
      hunks.sliding(2).forall {
        case List((s1, l1), (s2, _)) => s1 + l1 <= s2
        case _                       => true
      }
    }
  }

  test("the large-input fallback still round-trips") {
    // Above the LCS table limit the diff degrades to a line-by-line comparison,
    // which must still apply correctly.
    val n = 2100
    val a = Vector.tabulate(n)(i => s"line $i")
    val b = a.updated(5, "changed").updated(n - 1, "also changed")
    assert(n.toLong * n.toLong > 4_000_000L, "this input must exceed the table limit")
    val p = Diff.unified(a, b)
    assertEquals(Diff.apply(a, p), b)
  }
