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

  private def outcomes(xs: Vector[ExportItem], p: KernelProfile): Vector[(List[String], String)] =
    val r   = new Replay(xs, p, true)
    val out = Vector.newBuilder[(List[String], String)]
    while r.hasNext do
      val s = r.next()
      out += ((s.names.map(_.toString), ReplayTally.label(s.outcome)))
    out.result()

  /** The profiles that do not already cache, which are the ones the flag is
    * for; derived so a new profile joins the test by existing. */
  private val uncached = KernelProfile.all.filterNot(_.cacheDefEqSuccess)

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

  test("it changes no verdict on a file whose ambient block is demoted") {
    // The P10 shape, where the hoisting pass and the kernel's literal
    // extensions both come into play, so the cache is exercised on a run that
    // reduces literals rather than one that only checks types.
    for f <- fixtures; p <- uncached do
      val xs     = items(f)
      val starts = Replay.groupStarts(xs)
      val ends   = starts.drop(1) :+ xs.length
      val g      = starts.indices.find(k => (starts(k) until ends(k)).exists(i => xs(i).names.exists(_.toString == "Nat")))
      g.foreach { k =>
        val span = (starts(k) until ends(k)).toSet
        val bad =
          xs.zipWithIndex.filter((_, i) => !span.contains(i)).map(_._1) ++
            xs.zipWithIndex.filter((_, i) => span.contains(i)).map(_._1)
        assertEquals(outcomes(bad, p.withDefEqSuccessCache), outcomes(bad, p), clue((f, p.label)))
      }
  }
