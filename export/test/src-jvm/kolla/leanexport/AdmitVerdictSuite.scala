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

  private val anchor = "nat-add-3.1.0.ndjson"

  private def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src   = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(lines).items

  private val fixtures: List[String] =
    val url = getClass.getResource("/" + anchor)
    val dir = java.nio.file.Paths.get(url.toURI).getParent
    val st  = java.nio.file.Files.list(dir)
    try
      scala.jdk.CollectionConverters
        .IteratorHasAsScala(st.iterator())
        .asScala
        .map(_.getFileName.toString)
        .filter(n => n.endsWith(".ndjson") || n.endsWith(".export"))
        .toList
        .sorted
    finally st.close()

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
    for f <- fixtures do
      val p  = if f.contains("3.0.0") then KernelProfile.v4_27 else KernelProfile.v4_35
      val xs = items(f)
      val all = verdicts(xs, p, _ => true).toMap
      for (name, expected) <- all if expected == "accepted" do
        val one = verdicts(xs, p, _.toString == name).toMap
        assertEquals(one.get(name), Some(expected), clue((f, name)))
  }
