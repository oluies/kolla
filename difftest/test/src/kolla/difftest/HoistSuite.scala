package kolla.difftest

import kolla.kernel.*
import kolla.leanexport.*

class HoistSuite extends munit.FunSuite:

  private def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src   = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(lines).items

  private val fixtures =
    List("nat-add-3.1.0.ndjson", "nested-3.1.0.ndjson", "quot-sound-3.1.0.ndjson")

  private def n(s: String): Name = Name.parse(s)

  /** The items an inductive block spans, by group, as the checker loop sees it. */
  private def blocks(xs: Vector[ExportItem]): List[List[String]] =
    val starts = KollaChecker.groupStarts(xs)
    val ends   = starts.drop(1) :+ xs.length
    starts.indices.toList.map(g => (starts(g) until ends(g)).toList.flatMap(i => xs(i).names.map(_.toString)))

  test("an inductive block is one group") {
    val xs = items("nat-add-3.1.0.ndjson")
    val nat = blocks(xs).find(_.contains("Nat")).get
    assert(nat.contains("Nat.zero"), clue(nat))
    assert(nat.contains("Nat.succ"))
    assert(nat.contains("Nat.rec"))
  }

  test("a mutual and a nested block each stay in one group") {
    val xs = blocks(items("nested-3.1.0.ndjson"))
    val tree = xs.find(_.contains("Tree")).get
    assert(tree.contains("Tree.leaf") && tree.contains("Tree.node") && tree.contains("Tree.rec"), clue(tree))
    val even = xs.find(_.contains("EvenList")).get
    assert(even.contains("OddList"), clue(even))
    assert(even.contains("EvenList.rec") && even.contains("OddList.rec"))
  }

  test("every group start is a group start of the hoisted file too") {
    // Hoisting moves whole groups, so the grouping is preserved: every block in
    // the input is a block in the output.
    fixtures.foreach { f =>
      val xs = items(f)
      KernelProfile.all.foreach { p =>
        val out  = KollaChecker.hoistExtensionConstants(xs, p)
        val want = blocks(xs).map(_.toSet).toSet
        val got  = blocks(out).map(_.toSet).toSet
        assertEquals(got, want, clue((f, p.label)))
      }
    }
  }

  test("hoisting is a permutation and is idempotent") {
    fixtures.foreach { f =>
      val xs = items(f)
      KernelProfile.all.foreach { p =>
        val out = KollaChecker.hoistExtensionConstants(xs, p)
        assertEquals(out.length, xs.length, clue((f, p.label)))
        assertEquals(out.toSet, xs.toSet, clue((f, p.label)))
        assertEquals(KollaChecker.hoistExtensionConstants(out, p), out, clue((f, p.label)))
      }
    }
  }

  /** The index in `xs` of each item of `out`. */
  private def trace(xs: Vector[ExportItem], out: Vector[ExportItem]): Vector[Int] =
    val pos = xs.zipWithIndex.toMap
    out.map(pos)

  test("hoisting is a stable partition, so dependencies still precede their uses") {
    // Both halves keep their input order, which is what makes the reordering
    // safe: within each half every declaration still follows its dependencies.
    fixtures.foreach { f =>
      val xs = items(f)
      KernelProfile.all.foreach { p =>
        val t = trace(xs, KollaChecker.hoistExtensionConstants(xs, p))
        val descents = t.sliding(2).count(w => w.length == 2 && w(1) < w(0))
        assert(descents <= 1, clue((f, p.label, descents)))
      }
    }
  }

  /** The same items with the group holding `name` moved to the end.
    *
    * None of the committed fixtures is itself mis-ordered, so the hazard is
    * reproduced by moving a block the kernel needs behind its first use.
    */
  private def demote(xs: Vector[ExportItem], name: String): Vector[ExportItem] =
    val starts = KollaChecker.groupStarts(xs)
    val ends   = starts.drop(1) :+ xs.length
    val g      = starts.indices.find(k => (starts(k) until ends(k)).exists(i => xs(i).names.exists(_.toString == name)))
    assert(g.isDefined, s"no group declares $name")
    val span = (starts(g.get) until ends(g.get)).toSet
    xs.zipWithIndex.filter((_, i) => !span.contains(i)).map(_._1) ++
      xs.zipWithIndex.filter((_, i) => span.contains(i)).map(_._1)

  test("a demoted Nat block is rejected unhoisted and accepted hoisted") {
    import cats.effect.unsafe.implicits.global
    val xs = items("nat-add-3.1.0.ndjson")
    val p  = KernelProfile.v4_35
    val bad = demote(xs, "Nat")
    assertNotEquals(bad, xs)

    // Without the pass the Nat literal has nothing to expand to.
    val raw = KollaChecker.check(bad, p, "t", "t", hoist = false).unsafeRunSync()
    assert(raw.rejected > 0, clue(raw.results.map(r => r.name.toString -> r.verdict.label).toString))

    // With it the file checks, and the order is the one the file started with.
    val fixed = KollaChecker.hoistExtensionConstants(bad, p)
    assertEquals(fixed.map(_.names), xs.map(_.names))
    val good = KollaChecker.check(bad, p, "t", "t").unsafeRunSync()
    assertEquals(good.unexpected.length, 0, clue(good.unexpected.map(_.name.toString).toString))
    assertEquals(good.accepted, xs.length)
  }

  test("every extension constant present lands in the hoisted half") {
    // The point of the pass: in the v4.25.0 export of case-strlit, `appendLit`
    // is item 406 and `String.mk` is item 1822, so the string-literal expansion
    // has nothing to expand to. See docs/semantics.md P10.
    val xs = items("nat-add-3.1.0.ndjson")
    val p  = KernelProfile.v4_35
    val out = KollaChecker.hoistExtensionConstants(xs, p)
    val t   = trace(xs, out)
    // The hoisted half is the first increasing run.
    val boundary = t.sliding(2).indexWhere(w => w.length == 2 && w(1) < w(0)) match
      case -1 => t.length
      case k  => k + 1
    val hoisted = out.take(boundary).flatMap(_.names).toSet
    val present = KollaChecker.extensionConstants(p).filter(c => xs.exists(_.names.contains(c)))
    assert(present.nonEmpty, clue(xs.flatMap(_.names).map(_.toString).take(40).toString))
    present.foreach(c => assert(hoisted.contains(c), clue(s"$c is not in the hoisted half")))
  }

  test("the hoisted half really is a prefix when the file needs reordering") {
    val xs  = demote(items("nat-add-3.1.0.ndjson"), "Nat")
    val out = KollaChecker.hoistExtensionConstants(xs, KernelProfile.v4_35)
    val t   = trace(xs, out)
    val boundary = t.sliding(2).indexWhere(w => w.length == 2 && w(1) < w(0)) + 1
    assert(boundary > 0 && boundary < out.length, clue((boundary, out.length)))
    val hoisted = out.take(boundary).flatMap(_.names).map(_.toString).toSet
    assert(hoisted.contains("Nat") && hoisted.contains("Nat.succ"), clue(hoisted.toString))
  }

  test("a constant the kernel never reaches for is not hoisted") {
    assert(!KollaChecker.extensionConstants(KernelProfile.v4_35).contains(n("List.append")))
    assert(KollaChecker.extensionConstants(KernelProfile.v4_25).contains(n("String.mk")))
    assert(KollaChecker.extensionConstants(KernelProfile.v4_35).contains(n("String.ofList")))
    assert(!KollaChecker.extensionConstants(KernelProfile.v4_35).contains(n("String.mk")))
  }
