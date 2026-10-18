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

  /** The constants an item mentions, as a dependency edge's target names. */
  private def mentions(it: ExportItem): Set[Name] =
    val into = scala.collection.mutable.HashSet.empty[Name]
    def walk(e: Expr): Unit =
      ExprOps.forEach(e) { (x, _) =>
        x match
          case c: Expr.Const => into += c.name
          case pr: Expr.Proj => into += pr.typeName
          case _             => ()
        true
      }
    it match
      case ExportItem.Info(info) =>
        walk(info.tpe)
        info match
          case ConstantInfo.DefnInfo(v)   => walk(v.value)
          case ConstantInfo.ThmInfo(v)    => walk(v.value)
          case ConstantInfo.OpaqueInfo(v) => walk(v.value)
          case ConstantInfo.RecInfo(v)    => v.rules.foreach(r => walk(r.rhs))
          case _                          => ()
      case ExportItem.Decl(d) =>
        d match
          case Declaration.AxiomDecl(v)       => walk(v.toConstantVal.tpe)
          case Declaration.DefnDecl(v)        => walk(v.toConstantVal.tpe); walk(v.value)
          case Declaration.ThmDecl(v)         => walk(v.toConstantVal.tpe); walk(v.value)
          case Declaration.OpaqueDecl(v)      => walk(v.toConstantVal.tpe); walk(v.value)
          case Declaration.QuotDecl           => ()
          case Declaration.MutualDefnDecl(ds) => ds.foreach(v => { walk(v.toConstantVal.tpe); walk(v.value) })
          case Declaration.InductDecl(_, _, ts, _) =>
            ts.foreach(t => { walk(t.tpe); t.ctors.foreach(c => walk(c.tpe)) })
      case ExportItem.DefnWithoutHints(_, _, t, v) => walk(t); walk(v)
    into.toSet

  /** Every dependency edge the file satisfies, as (user, dependency) positions. */
  private def satisfiedEdges(xs: Vector[ExportItem]): Set[(Int, Int)] =
    val declaredAt = xs.zipWithIndex.flatMap((it, i) => it.names.map(_ -> i)).toMap
    (for
      (it, i) <- xs.zipWithIndex
      d       <- mentions(it)
      j       <- declaredAt.get(d)
      if j < i
    yield (i, j)).toSet

  /** An axiom item named `name` whose type mentions each of `deps`. */
  private def axiom(name: String, deps: String*): ExportItem =
    val tpe = deps.foldLeft(Expr.sort(Level.Zero): Expr)((acc, d) => Expr.App(acc, Expr.const(n(d))))
    ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(n(name), Nil, tpe), isUnsafe = false)))

  /** A file where an extension constant depends on something declared earlier.
    *
    * None of the committed fixtures has this shape, and it is the only shape
    * that exercises the `require` closure: hoisting `String.ofList` has to pull
    * `Helper` along, or `Helper` is left behind in the back half and ends up
    * after the group that needs it.
    */
  private val withBackwardDep: Vector[ExportItem] =
    Vector(
      axiom("Unrelated"),
      axiom("Helper", "Unrelated"),
      axiom("String.ofList", "Helper"),
      axiom("User", "String.ofList")
    )

  test("an extension constant drags its earlier dependencies into the prefix") {
    val out = KollaChecker.hoistExtensionConstants(withBackwardDep, KernelProfile.v4_35)
    val order = out.flatMap(_.names).map(_.toString)
    assertEquals(order, Vector("Unrelated", "Helper", "String.ofList", "User"))
    // `Helper` and `Unrelated` are not extension constants; they are in the
    // prefix only because `String.ofList` depends on them.
    val t = trace(withBackwardDep, out)
    val boundary = t.sliding(2).indexWhere(w => w.length == 2 && w(1) < w(0)) + 1
    assertEquals(boundary, 0, clue(t))
  }

  test("hoisting never turns a satisfied dependency into an unsatisfied one") {
    // This is the guarantee the pass actually makes (docs/semantics.md P10): it
    // does not repair a file that was not topologically ordered, it declines to
    // break one that was. The demoted fixture is included because it is the only
    // input here the pass actually reorders.
    val inputs =
      fixtures.map(items) ++ List(
        demote(items("nat-add-3.1.0.ndjson"), "Nat"),
        withBackwardDep,
        // The extension constant last, so the whole closure has to move.
        withBackwardDep.reverse.updated(0, withBackwardDep(3)).updated(3, withBackwardDep(0)),
        axiom("Filler") +: withBackwardDep
      )
    inputs.foreach { xs =>
      val names = xs.map(_.names)
      KernelProfile.all.foreach { p =>
        val out      = KollaChecker.hoistExtensionConstants(xs, p)
        val outIndex = out.zipWithIndex.toMap
        val inIndex  = xs.zipWithIndex.toMap
        satisfiedEdges(xs).foreach { (user, dep) =>
          val u = outIndex(xs(user))
          val d = outIndex(xs(dep))
          assert(
            d < u,
            clue(s"${names(dep)} moved after ${names(user)} under ${p.label} " +
              s"(input ${inIndex(xs(dep))} -> $d, ${inIndex(xs(user))} -> $u)")
          )
        }
      }
    }
  }

  test("the demoted fixture really has edges to break") {
    // Otherwise the invariant above would hold vacuously on the one input that
    // is reordered at all.
    val xs  = demote(items("nat-add-3.1.0.ndjson"), "Nat")
    val out = KollaChecker.hoistExtensionConstants(xs, KernelProfile.v4_35)
    assertNotEquals(out, xs)
    val edges = satisfiedEdges(xs)
    assert(edges.size >= 5, clue(edges.size))
    // And at least one of them crosses the partition, so the `require` closure
    // is doing work rather than the halves happening not to interleave.
    val outIndex = out.zipWithIndex.toMap
    val moved    = xs.zipWithIndex.count((it, i) => outIndex(it) != i)
    assert(moved > 0, clue(moved))
  }

  test("a constant the kernel never reaches for is not hoisted") {
    assert(!KollaChecker.extensionConstants(KernelProfile.v4_35).contains(n("List.append")))
    assert(KollaChecker.extensionConstants(KernelProfile.v4_25).contains(n("String.mk")))
    assert(KollaChecker.extensionConstants(KernelProfile.v4_35).contains(n("String.ofList")))
    assert(!KollaChecker.extensionConstants(KernelProfile.v4_35).contains(n("String.mk")))
  }
