package kolla.cli

import cats.effect.IO
import kolla.kernel.*
import kolla.leanexport.*
import munit.CatsEffectSuite

class CheckSuite extends CatsEffectSuite:

  /** A hand-built export: an axiom, a definition that uses it, and a broken
    * definition whose stated type is a proposition and whose value is a type.
    *
    * Built rather than read from a file so the suite runs on the native build
    * too, where there is no classpath to load a resource from.
    */
  private val prop: Expr = Expr.Sort(Level.zero)
  private val type0: Expr = Expr.Sort(Level.Succ(Level.zero))

  private def axiom(name: String, tpe: Expr): ExportItem =
    ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse(name), Nil, tpe), isUnsafe = false)))

  private def defn(name: String, tpe: Expr, value: Expr): ExportItem =
    ExportItem.Info(
      ConstantInfo.DefnInfo(
        DefinitionVal(
          ConstantVal(Name.parse(name), Nil, tpe), value,
          ReducibilityHints.Abbrev, DefinitionSafety.Safe, List(Name.parse(name))
        )
      )
    )

  private val good: Vector[ExportItem] =
    Vector(axiom("P", prop), defn("Q", type0, prop))

  private val bad: Vector[ExportItem] =
    good :+ defn("Broken", prop, type0)

  private def silent(n: Name, o: ReplayOutcome, nanos: Long): IO[Unit] = IO.unit

  test("a well-formed export is accepted and reports a wall time") {
    Check.run(good, KernelProfile.v4_35, abortOnReject = false, silent).map { r =>
      assertEquals(r.tally.accepted, 2)
      assertEquals(r.tally.rejected, 0)
      assert(r.tally.ok)
      assert(r.wallNanos >= 0L)
    }
  }

  test("a broken declaration is rejected and named") {
    Check.run(bad, KernelProfile.v4_35, abortOnReject = false, silent).map { r =>
      assertEquals(r.tally.rejected, 1)
      assert(!r.tally.ok)
      assertEquals(r.tally.firstRejection.map(_._1.toString), Some("Broken"))
    }
  }

  test("emit sees every declaration, in order") {
    for
      seen <- IO.ref(Vector.empty[(String, String)])
      _ <- Check.run(
             bad, KernelProfile.v4_35, abortOnReject = false,
             (n, o, _) => seen.update(_ :+ (n.toString, Render.label(o)))
           )
      got <- seen.get
    yield assertEquals(got, Vector(("P", "accepted"), ("Q", "accepted"), ("Broken", "rejected")))
  }

  test("--abort stops after the first rejection and counts the rest unreached") {
    val items = bad :+ defn("After", type0, prop)
    for
      seen <- IO.ref(Vector.empty[String])
      r    <- Check.run(items, KernelProfile.v4_35, abortOnReject = true, (n, _, _) => seen.update(_ :+ n.toString))
      got  <- seen.get
    yield
      assertEquals(r.tally.rejected, 1)
      assertEquals(r.tally.notReached, 1)
      assertEquals(r.tally.total, 4)
      // `After` was never checked, so it was never emitted.
      assertEquals(got, Vector("P", "Q", "Broken"))
  }

  test("without --abort the run continues past a rejection") {
    val items = bad :+ defn("After", type0, prop)
    Check.run(items, KernelProfile.v4_35, abortOnReject = false, silent).map { r =>
      assertEquals(r.tally.notReached, 0)
      assertEquals(r.tally.accepted, 3)
      assertEquals(r.tally.rejected, 1)
    }
  }

  test("an unreadable file is a left, not an exception") {
    Check.file("x", "this is not an export", KernelProfile.v4_35, false, silent).map {
      case Left(m)  => assert(clue(m).startsWith("x: "))
      case Right(r) => fail(s"expected a read failure, got $r")
    }
  }

  test("a readable file goes through the same path as items") {
    val fmt  = ExportFormat.Ndjson("3.1.0")
    val text = ExportWriter.toString(ExportEnv(fmt, None, good), fmt)
    Check.file("x", text, KernelProfile.v4_35, false, silent).map {
      case Left(m)  => fail(m)
      case Right(r) => assertEquals(r.tally.accepted, 2)
    }
  }

  private val ndjson = ExportFormat.Ndjson("3.1.0")

  /** NDJSON announces itself with a `meta` header, which is how the reader
    * knows the format; a headerless file is not a file kolla ever sees.
    */
  private val meta =
    ExportMeta("lean4export", "3.1.0", "3.1.0", "4.35.0", "eb6cafb")

  /** The items as an export file, in `size`-byte chunks.
    *
    * Small chunks on purpose: the streaming path has to survive a declaration
    * split across two chunks, which a single-chunk stream would never show.
    */
  private def bytesOf(items: Vector[ExportItem], size: Int): fs2.Stream[IO, Byte] =
    fs2.Stream
      .emits(ExportWriter.toLines(ExportEnv(ndjson, Some(meta), items), ndjson))
      .intersperse("\n")
      .through(fs2.text.utf8.encode)
      .chunkLimit(size)
      .unchunks

  test("streaming an export gives the same tally as holding it") {
    for
      streamed <- Check.stream("x", bytesOf(good, 7), KernelProfile.v4_35, abortOnReject = false, silent)
      held     <- Check.run(good, KernelProfile.v4_35, abortOnReject = false, silent)
    yield
      val r = streamed.getOrElse(fail("the stream produced no result"))
      assertEquals(r.tally.accepted, held.tally.accepted)
      assertEquals(r.tally.rejected, held.tally.rejected)
      assertEquals(r.tally.total, held.tally.total)
      assertEquals(r.lateAmbient, Nil)
  }

  test("streaming a rejection is still a rejection") {
    Check.stream("x", bytesOf(bad, 13), KernelProfile.v4_35, abortOnReject = false, silent).map { out =>
      val r = out.getOrElse(fail("the stream produced no result"))
      assertEquals(r.tally.rejected, 1)
      assert(!r.tally.ok)
    }
  }

  test("streaming names each declaration exactly once") {
    val seen = IO.ref(Vector.empty[String])
    seen.flatMap { ref =>
      Check
        .stream("x", bytesOf(good, 5), KernelProfile.v4_35, abortOnReject = false,
                (n, _, _) => ref.update(_ :+ n.toString))
        .flatMap(_ => ref.get)
        .map(names => assertEquals(names, Vector("P", "Q")))
    }
  }

  test("an unparseable stream is a read failure, not an exhaustion") {
    val junk = fs2.Stream.emits("this is not an export".getBytes("UTF-8").toSeq)
    Check.stream("x", junk, KernelProfile.v4_35, abortOnReject = false, silent).map {
      case Left(f: Check.Failure.Unreadable) => assert(f.message.startsWith("x:"), clue(f.message))
      case other                             => fail(s"expected Unreadable, got $other")
    }
  }

  test("progress is reported as declarations go by") {
    // `progressEvery` is far above a two-declaration file, so the note must
    // not fire; this pins the threshold rather than the plumbing.
    val notes = IO.ref(Vector.empty[Check.Progress])
    notes.flatMap { ref =>
      Check
        .stream("x", bytesOf(good, 9), KernelProfile.v4_35, abortOnReject = false, silent,
                Some((p: Check.Progress) => ref.update(_ :+ p)))
        .flatMap(_ => ref.get)
        .map(ns => assertEquals(ns, Vector.empty[Check.Progress]))
    }
  }

  test("--check admits what it does not select, unchecked") {
    // `P` is selected and checked; `Q` is admitted so that anything depending
    // on it still resolves, and is never reported as accepted.
    Check
      .run(good, KernelProfile.v4_35, abortOnReject = false, silent, n => n.toString == "P")
      .map { r =>
        assertEquals(r.tally.accepted, 1)
        assertEquals(r.tally.carriedOver, 1)
        assertEquals(r.admittedUnchecked, 1)
        assert(r.tally.ok)
      }
  }

  test("--check can hide a rejection by not selecting it") {
    // The broken declaration is admitted rather than checked, so the run is
    // clean. That is the point of the flag and the reason the count is
    // reported: the verdict covers the selection, not the file.
    Check
      .run(bad, KernelProfile.v4_35, abortOnReject = false, silent, n => n.toString == "P")
      .map { r =>
        assertEquals(r.tally.rejected, 0)
        assertEquals(r.admittedUnchecked, 2)
        assert(r.tally.ok)
      }
  }

  test("selecting nothing checks everything") {
    Check.run(good, KernelProfile.v4_35, abortOnReject = false, silent).map { r =>
      assertEquals(r.admittedUnchecked, 0)
      assertEquals(r.tally.accepted, 2)
    }
  }

  test("a check prefix matches a name and its children, not a word prefix") {
    val sel = Options.selects(Options(checkOnly = List("Propulsion")))
    assert(sel(Name.parse("Propulsion")))
    assert(sel(Name.parse("Propulsion.Basic.thrust")))
    assert(!sel(Name.parse("PropulsionOther")))
    assert(!sel(Name.parse("Mathlib.Data.Nat")))
  }

  /** A cache in memory, standing in for the file one: the file is tested by
    * `CacheStoreSuite`, and this is about what `Check.stream` does with it.
    */
  private final class MemCache extends kolla.leanexport.ReplayCache:
    private val seen = scala.collection.mutable.HashSet.empty[kolla.leanexport.Digest]
    def contains(d: kolla.leanexport.Digest): Boolean = seen.contains(d)
    def accepted(d: kolla.leanexport.Digest): Unit = seen += d
    def size: Int = seen.size

  test("a second streamed run reuses the cache and checks nothing") {
    val cache = new MemCache
    for
      first  <- Check.stream("x", bytesOf(good, 11), KernelProfile.v4_35, abortOnReject = false,
                             silent, None, _ => true, Some(cache))
      second <- Check.stream("x", bytesOf(good, 11), KernelProfile.v4_35, abortOnReject = false,
                             silent, None, _ => true, Some(cache))
    yield
      val a = first.getOrElse(fail("no first result"))
      val b = second.getOrElse(fail("no second result"))
      assertEquals(a.tally.accepted, 2)
      assertEquals(a.reusedFromCache, 0)
      assertEquals(b.tally.accepted, 0)
      assertEquals(b.reusedFromCache, 2)
      assert(b.tally.ok, "a fully cached run is still ok")
  }

  test("a rejection is never cached") {
    val cache = new MemCache
    for
      _ <- Check.stream("x", bytesOf(bad, 17), KernelProfile.v4_35, abortOnReject = false,
                        silent, None, _ => true, Some(cache))
      r <- Check.stream("x", bytesOf(bad, 17), KernelProfile.v4_35, abortOnReject = false,
                        silent, None, _ => true, Some(cache))
    yield
      val x = r.getOrElse(fail("no result"))
      // The two good declarations come back cached; the broken one is checked
      // again and rejected again, because nothing records a rejection.
      assertEquals(x.reusedFromCache, 2)
      assertEquals(x.tally.rejected, 1)
      assert(!x.tally.ok)
  }

  test("the checkpoint runs even when the stream fails") {
    val flushed = IO.ref(0)
    flushed.flatMap { ref =>
      val junk = fs2.Stream.emits("this is not an export".getBytes("UTF-8").toSeq)
      Check
        .stream("x", junk, KernelProfile.v4_35, abortOnReject = false, silent, None,
                _ => true, None, Some(ref.update(_ + 1)))
        .flatMap(_ => ref.get)
        .map(n => assertEquals(n, 1, "an unreadable file must still checkpoint"))
    }
  }
