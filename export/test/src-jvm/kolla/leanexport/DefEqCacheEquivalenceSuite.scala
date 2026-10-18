package kolla.leanexport

import kolla.kernel.*

/** `--defeq-cache` is sold as an optimisation, so the verdicts have to be the
  * same ones. A profile that keeps the positive `is_def_eq` cache must accept
  * and reject exactly what the release's profile does.
  */
class DefEqCacheEquivalenceSuite extends munit.FunSuite:

  private def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src   = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(lines).items

  /** Every committed fixture, by listing the resource directory rather than
    * naming them, so a fixture added later is covered without touching this
    * file. One known fixture anchors the directory; `getResource("/")` would
    * give the first classpath root, which is another module's classes.
    */
  private val anchor = "nat-add-3.1.0.ndjson"

  private val fixtures: List[String] =
    val url = getClass.getResource("/" + anchor)
    assert(url != null, s"missing anchor fixture $anchor")
    val dir = java.nio.file.Paths.get(url.toURI).getParent
    val stream = java.nio.file.Files.list(dir)
    val found =
      try
        scala.jdk.CollectionConverters
          .IteratorHasAsScala(stream.iterator())
          .asScala
          .map(_.getFileName.toString)
          .filter(n => n.endsWith(".ndjson") || n.endsWith(".export"))
          .toList
          .sorted
      finally stream.close()
    assert(found.contains(anchor), s"listing $dir did not find $anchor: $found")
    found

  private def outcomes(
      xs: Vector[ExportItem],
      p: KernelProfile,
      hoist: Boolean = true
  ): Vector[(List[String], String)] =
    val r   = new Replay(xs, p, hoist)
    val out = Vector.newBuilder[(List[String], String)]
    while r.hasNext do
      val s = r.next()
      out += ((s.names.map(_.toString), ReplayTally.label(s.outcome)))
    out.result()

  /** The profiles that do not already cache, which are the ones the flag is
    * for; derived so a new profile joins the test by existing. */
  private val uncached = KernelProfile.all.filterNot(_.cacheDefEqSuccess)

  /** The items with the group declaring `Nat` moved to the end, or `None` if
    * there is no such group.
    *
    * One copy, because two tests depend on replaying the same shape: the
    * equivalence and the guard that the shape still rejects. Two copies would
    * drift and the guard would vouch for something else.
    */
  private def demoteAmbientGroup(xs: Vector[ExportItem]): Option[Vector[ExportItem]] =
    val starts = Replay.groupStarts(xs)
    val ends   = starts.drop(1) :+ xs.length
    starts.indices
      .find(k => (starts(k) until ends(k)).exists(i => xs(i).names.exists(_.toString == "Nat")))
      .map { k =>
        val span = (starts(k) until ends(k)).toSet
        xs.zipWithIndex.filter((_, i) => !span.contains(i)).map(_._1) ++
          xs.zipWithIndex.filter((_, i) => span.contains(i)).map(_._1)
      }

  test("the fixtures and the uncached profiles are both non-empty") {
    // Without this the two tests below would pass by iterating nothing.
    assert(fixtures.nonEmpty, clue(fixtures))
    assert(uncached.nonEmpty, clue(KernelProfile.all.map(_.label)))
  }

  test("keeping the positive cache changes no verdict") {
    for f <- fixtures; p <- uncached do
      val xs = items(f)
      assertEquals(
        outcomes(xs, p.withDefEqSuccessCache),
        outcomes(xs, p),
        clue((f, p.label))
      )
  }

  test("it changes no verdict on an unhoisted file with a demoted ambient block") {
    // The P10 shape: `Nat` is moved to the end and hoisting is off, so the
    // literal expansion has no constructor in scope and the run rejects. With
    // hoisting on the pass would move the group straight back to the front and
    // this would be the previous test over again.
    for f <- fixtures; p <- uncached do
      demoteAmbientGroup(items(f)).foreach { bad =>
        assertEquals(
          outcomes(bad, p.withDefEqSuccessCache, hoist = false),
          outcomes(bad, p, hoist = false),
          clue((f, p.label))
        )
      }
  }

  test("at least one fixture has an ambient block to demote") {
    // Guards the test above: `Nat` missing from every fixture would make its
    // body a no-op and the equivalence it asserts vacuous.
    val withNat = fixtures.count(f => demoteAmbientGroup(items(f)).isDefined)
    assert(withNat > 0, clue(fixtures))
  }

  test("the demoted unhoisted shape really does reject") {
    // Without this the equivalence above could hold because both sides accept
    // everything, which would not exercise the cache on a failing run. Same
    // construction and same profile source as the equivalence test.
    val bad = fixtures.flatMap(f => demoteAmbientGroup(items(f))).headOption
    assert(bad.isDefined, clue(fixtures))
    val got = outcomes(bad.get, uncached.head, hoist = false)
    assert(got.exists(_._2 == "rejected"), clue(got.map(_._2).distinct))
  }
