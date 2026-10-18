package kolla.leanexport

import kolla.kernel.*

/** What the cache key has to be sensitive to, and what it must not be.
  *
  * A cache that reports a hit after something relevant changed is a false
  * accept, so these are soundness tests, not plumbing tests.
  */
class DigestSuite extends munit.FunSuite:

  private def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src   = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(lines).items

  private class Recording extends ReplayCache:
    val seen = scala.collection.mutable.LinkedHashSet.empty[Digest]
    var hits = 0
    def contains(d: Digest): Boolean =
      val h = seen.contains(d)
      if h then hits += 1
      h
    def accepted(d: Digest): Unit = seen += d

  private def runWith(
      xs: Vector[ExportItem],
      p: KernelProfile,
      cache: Option[ReplayCache]
  ): Vector[ReplayStep] =
    val r   = new Replay(p, true, Int.MaxValue, _ => true, cache)
    xs.foreach(r.feed)
    r.finish()
    val out = Vector.newBuilder[ReplayStep]
    while r.hasNext do out += r.next()
    out.result()

  test("hex round-trips through parse") {
    val d = Digest.mixString(Digest.seed, "Nat.succ")
    assertEquals(Digest.parse(d.hex), Some(d))
    assertEquals(d.hex.length, 32)
  }

  test("a malformed digest does not parse") {
    assertEquals(Digest.parse(""), None)
    assertEquals(Digest.parse("abc"), None)
    assertEquals(Digest.parse("z" * 32), None)
  }

  test("a second run over the same file hits the cache for everything") {
    val xs    = items("nat-add-3.1.0.ndjson")
    val cache = new Recording
    val first = runWith(xs, KernelProfile.v4_35, Some(cache))
    assert(first.forall(_.outcome == ReplayOutcome.Checked), clue(first.map(_.outcome).toString))
    assertEquals(cache.hits, 0)

    val second = runWith(xs, KernelProfile.v4_35, Some(cache))
    assert(second.forall(_.outcome.isInstanceOf[ReplayOutcome.Cached]), clue(second.map(_.outcome).toString))
    assertEquals(second.length, first.length)
  }

  test("a cached run is still ok but reports nothing as accepted") {
    val xs    = items("nat-add-3.1.0.ndjson")
    val cache = new Recording
    runWith(xs, KernelProfile.v4_35, Some(cache))
    val tally = runWith(xs, KernelProfile.v4_35, Some(cache)).foldLeft(ReplayTally())(_.add(_))
    assertEquals(tally.accepted, 0)
    assert(tally.cached > 0)
    assertEquals(tally.rejected, 0)
    assert(tally.ok, "a fully cached run has been judged, by an earlier run")
  }

  test("a cache from another profile is not reused") {
    // The same declaration can be accepted on one profile and rejected on
    // another, so the profile is part of the key.
    val xs    = items("nat-add-3.1.0.ndjson")
    val cache = new Recording
    runWith(xs, KernelProfile.v4_35, Some(cache))
    val other = runWith(xs, KernelProfile.v4_27, Some(cache))
    assertEquals(other.count(_.outcome.isInstanceOf[ReplayOutcome.Cached]), 0)
  }

  test("changing a dependency misses the cache for what depends on it") {
    // The heart of it: `Nat.add`'s own bytes are untouched, but `Nat` is not
    // the `Nat` it was checked against, so its digest must differ.
    val xs    = items("nat-add-3.1.0.ndjson")
    val cache = new Recording
    runWith(xs, KernelProfile.v4_35, Some(cache))

    val bumped = xs.map {
      case ExportItem.Info(ConstantInfo.InductInfo(v)) if v.toConstantVal.name.toString == "Nat" =>
        ExportItem.Info(ConstantInfo.InductInfo(v.copy(numParams = v.numParams + 1)))
      case other => other
    }
    assertNotEquals(bumped, xs)

    val after   = runWith(bumped, KernelProfile.v4_35, Some(cache))
    val reused  = after.count(_.outcome.isInstanceOf[ReplayOutcome.Cached])
    val total   = after.length
    assert(reused < total, clue((reused, total)))
    // Specifically, the block itself and `Nat.add` must both be fresh.
    val fresh = after.filterNot(_.outcome.isInstanceOf[ReplayOutcome.Cached]).flatMap(_.names).map(_.toString)
    assert(fresh.exists(_ == "Nat"), clue(fresh))
    assert(fresh.exists(_.startsWith("Nat.add")), clue(fresh))
  }

  test("binder names do not change the digest") {
    // `Expr.==` is `is_equal`, which ignores them, so two declarations that
    // differ only in a binder name are one declaration to the kernel and must
    // not miss. See docs/semantics.md X14.
    val base = Expr.ForallE(Name.parse("x"), Expr.Sort(Level.zero), Expr.BVar(0), BinderInfo.Default)
    val renamed = Expr.ForallE(Name.parse("y"), Expr.Sort(Level.zero), Expr.BVar(0), BinderInfo.Default)
    val implicitly_ = Expr.ForallE(Name.parse("x"), Expr.Sort(Level.zero), Expr.BVar(0), BinderInfo.Implicit)
    val d0 = Digest.mixExpr(Digest.seed, base, _ => None)
    assertEquals(Digest.mixExpr(Digest.seed, renamed, _ => None), d0)
    assertEquals(Digest.mixExpr(Digest.seed, implicitly_, _ => None), d0)
  }

  test("structure does change the digest") {
    val a = Expr.App(Expr.Sort(Level.zero), Expr.BVar(0))
    val b = Expr.App(Expr.BVar(0), Expr.Sort(Level.zero))
    assertNotEquals(Digest.mixExpr(Digest.seed, a, _ => None), Digest.mixExpr(Digest.seed, b, _ => None))
    val n0 = Expr.Lit(Literal.NatVal(BigInt(1)))
    val n1 = Expr.Lit(Literal.NatVal(BigInt(2)))
    assertNotEquals(Digest.mixExpr(Digest.seed, n0, _ => None), Digest.mixExpr(Digest.seed, n1, _ => None))
  }

  test("a resolved constant digests differently from an unresolved one") {
    val e   = Expr.Const(Name.parse("Nat"), Nil)
    val one = Digest.mixExpr(Digest.seed, e, _ => None)
    val two = Digest.mixExpr(Digest.seed, e, _ => Some(Digest.seed))
    assertNotEquals(one, two)
  }

  test("no cache means no outcome changes") {
    val xs = items("nat-add-3.1.0.ndjson")
    assertEquals(runWith(xs, KernelProfile.v4_35, None).map(_.outcome),
                 runWith(xs, KernelProfile.v4_35, None).map(_.outcome))
  }

  test("a cache survives turning --defeq-cache on") {
    // The claim the digest keys on `release` for: the flag changes no verdict,
    // so a digest accepted without it has to be reused with it. Keying on
    // `label` instead would make every one of these miss, which is the
    // exhaust-then-rerun regression K18 and P15 describe.
    val xs    = items("nat-add-3.1.0.ndjson")
    val cache = new Recording
    val plain = runWith(xs, KernelProfile.v4_27, Some(cache))
    assert(plain.forall(_.outcome == ReplayOutcome.Checked), clue(plain.map(_.outcome).toString))

    val amended = runWith(xs, KernelProfile.v4_27.withDefEqSuccessCache, Some(cache))
    assertEquals(amended.length, plain.length)
    assert(
      amended.forall(_.outcome.isInstanceOf[ReplayOutcome.Cached]),
      clue(amended.map(s => s.names.toString -> s.outcome).toString)
    )
  }

  test("and survives turning it back off") {
    // The other direction, which P15 notes is the less conservative one.
    val xs    = items("nat-add-3.1.0.ndjson")
    val cache = new Recording
    runWith(xs, KernelProfile.v4_27.withDefEqSuccessCache, Some(cache))
    val back = runWith(xs, KernelProfile.v4_27, Some(cache))
    assert(back.forall(_.outcome.isInstanceOf[ReplayOutcome.Cached]), clue(back.map(_.outcome).toString))
  }

  test("a different release is still not reused") {
    // The guard the above must not weaken: `release` differs between releases,
    // so a v4_35 digest cannot be reused on v4_27.
    val xs    = items("nat-add-3.1.0.ndjson")
    val cache = new Recording
    runWith(xs, KernelProfile.v4_35, Some(cache))
    val other = runWith(xs, KernelProfile.v4_27, Some(cache))
    assertEquals(other.count(_.outcome.isInstanceOf[ReplayOutcome.Cached]), 0)
  }
