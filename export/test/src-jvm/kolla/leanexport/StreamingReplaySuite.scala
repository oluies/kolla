package kolla.leanexport

import kolla.kernel.*

/** The incremental `feed`/`finish` path, which the `Vector` constructor hides.
  *
  * Feeding a whole file and finishing before the first `next()` is what every
  * other suite does, so none of them reach the prefix cut or the block-boundary
  * lookahead. These drive one item at a time instead.
  */
class StreamingReplaySuite extends munit.FunSuite:

  private def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src   = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(lines).items

  private val fixtures =
    List("nat-add-3.1.0.ndjson", "nested-3.1.0.ndjson", "quot-sound-3.1.0.ndjson")

  /** Moves the group declaring `name` to the end, which is the P10 situation. */
  private def demote(xs: Vector[ExportItem], name: String): Vector[ExportItem] =
    val starts = Replay.groupStarts(xs)
    val ends   = starts.drop(1) :+ xs.length
    val g      = starts.indices.find(k => (starts(k) until ends(k)).exists(i => xs(i).names.exists(_.toString == name)))
    assert(g.isDefined, s"no group declares $name")
    val span = (starts(g.get) until ends(g.get)).toSet
    xs.zipWithIndex.filter((_, i) => !span.contains(i)).map(_._1) ++
      xs.zipWithIndex.filter((_, i) => span.contains(i)).map(_._1)

  private def allAtOnce(xs: Vector[ExportItem], p: KernelProfile, hoist: Boolean): Vector[ReplayStep] =
    val r   = new Replay(xs, p, hoist)
    val out = Vector.newBuilder[ReplayStep]
    while r.hasNext do out += r.next()
    out.result()

  /** Feeds one item at a time, stepping whenever a step is complete. */
  private def streamed(
      xs: Vector[ExportItem],
      p: KernelProfile,
      hoist: Boolean,
      window: Int = Int.MaxValue
  ): (Vector[ReplayStep], Int) =
    val r          = new Replay(p, hoist, window)
    val out        = Vector.newBuilder[ReplayStep]
    var beforeEnd  = 0
    xs.foreach { x =>
      r.feed(x)
      while r.hasNext do
        out += r.next()
        beforeEnd += 1
    }
    r.finish()
    while r.hasNext do out += r.next()
    (out.result(), beforeEnd)

  test("streaming produces the same steps as feeding the whole file") {
    for f <- fixtures; p <- KernelProfile.all do
      val xs = items(f)
      val (got, _) = streamed(xs, p, hoist = true)
      assertEquals(got, allAtOnce(xs, p, hoist = true), clue((f, p.label)))
  }

  test("streaming produces the same steps with hoisting off") {
    for f <- fixtures; p <- KernelProfile.all do
      val xs = items(f)
      val (got, _) = streamed(xs, p, hoist = false)
      assertEquals(got, allAtOnce(xs, p, hoist = false), clue((f, p.label)))
  }

  test("a bounded window releases the prefix before the stream closes") {
    // The point of the window: with it, steps come out while the file is still
    // being fed. If this is 0 the whole file was buffered and nothing streamed.
    // No fixture declares all nine ambient constants, so an unbounded window
    // can only cut at `finish()` — which is what the second assertion shows.
    val xs            = items("nested-3.1.0.ndjson")
    val (_, windowed) = streamed(xs, KernelProfile.v4_35, hoist = true, window = 2)
    assert(windowed > 0, "no step completed before finish(); the prefix was never released")
    assert(windowed < xs.length, clue(windowed))

    val (_, unbounded) = streamed(xs, KernelProfile.v4_35, hoist = true)
    assertEquals(unbounded, 0, "an unbounded window should hold the whole file")
  }

  test("a window wide enough for the ambient constants keeps the verdicts") {
    // `defaultHoistWindow` is far wider than any fixture, so the streamed
    // result has to match the whole-file one declaration for declaration.
    for f <- fixtures; p <- KernelProfile.all do
      val xs       = items(f)
      val (got, _) = streamed(xs, p, hoist = true, window = Replay.defaultHoistWindow)
      assertEquals(got, allAtOnce(xs, p, hoist = true), clue((f, p.label)))
  }

  test("an ambient constant past the window is reported, not hidden") {
    // `Nat` is the first group in this file, so a narrow window still hoists
    // it. Demoting it to the end puts it past the cut, which is the case the
    // report exists for.
    val xs = demote(items("nat-add-3.1.0.ndjson"), "Nat")
    val r  = new Replay(KernelProfile.v4_35, hoist = true, hoistWindow = 1)
    xs.foreach(r.feed)
    r.finish()
    while r.hasNext do r.next()
    val late = r.lateAmbientConstants.map(_.toString).sorted
    assertEquals(late, List("Nat", "Nat.succ", "Nat.zero"), clue(late))
  }

  test("a narrow window does not report a block it still hoisted") {
    // The same file undemoted: `Nat` is the first group, so even a window of 1
    // cuts only after that group has closed and nothing is late.
    val xs = items("nat-add-3.1.0.ndjson")
    val r  = new Replay(KernelProfile.v4_35, hoist = true, hoistWindow = 1)
    xs.foreach(r.feed)
    r.finish()
    while r.hasNext do r.next()
    assertEquals(r.lateAmbientConstants, Nil)
  }

  test("nothing is reported late when the window covers the file") {
    val xs = items("nat-add-3.1.0.ndjson")
    val r  = new Replay(KernelProfile.v4_35, hoist = true)
    xs.foreach(r.feed)
    r.finish()
    while r.hasNext do r.next()
    assertEquals(r.lateAmbientConstants, Nil)
  }

  test("size is unknown until the stream closes") {
    val xs = items("nat-add-3.1.0.ndjson")
    val r  = new Replay(KernelProfile.v4_35, hoist = true)
    xs.foreach(r.feed)
    assertEquals(r.size, -1)
    r.finish()
    assertEquals(r.size, xs.length)
  }

  test("a late ambient block still checks when streamed") {
    // Within the window the pass still reorders, so the verdict is unchanged.
    val bad      = demote(items("nat-add-3.1.0.ndjson"), "Nat")
    val (got, _) = streamed(bad, KernelProfile.v4_35, hoist = true, window = Replay.defaultHoistWindow)
    assertEquals(got.count(_.outcome != ReplayOutcome.Checked), 0, clue(got.map(_.outcome).toString))
  }

  test("a late ambient block past the window is rejected, as unhoisted") {
    // The counterpart: cut too early and the string/nat expansion has nothing
    // to expand to. This is what `lateAmbientConstants` warns about.
    val bad      = demote(items("nat-add-3.1.0.ndjson"), "Nat")
    val (got, _) = streamed(bad, KernelProfile.v4_35, hoist = true, window = 1)
    assert(got.exists(_.outcome.isRejection), clue(got.map(s => s.names.toString -> s.outcome).toString))
  }

  test("feeding after finish is refused") {
    val xs = items("quot-sound-3.1.0.ndjson")
    val r  = new Replay(KernelProfile.v4_35, hoist = true)
    xs.foreach(r.feed)
    r.finish()
    intercept[IllegalArgumentException](r.feed(xs.head))
  }
