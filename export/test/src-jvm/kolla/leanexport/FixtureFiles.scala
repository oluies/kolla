package kolla.leanexport

/** The committed export fixture *files*, listed rather than named.
  *
  * Distinct from `Fixtures`, which holds inline literals and is cross-built;
  * listing a directory needs `java.nio`, so this is JVM-only.
  *
  * Shared so that two suites cannot drift, and guarded so that neither can
  * pass by iterating nothing: a listing that loses the anchor is an error, not
  * an empty loop.
  */
object FixtureFiles:

  /** A fixture that must always be present; it anchors the directory.
    *
    * `getResource("/")` would give the first classpath root, which is another
    * module's classes, so the directory is found through a known file.
    */
  val anchor = "nat-add-3.1.0.ndjson"

  lazy val names: List[String] =
    val url = getClass.getResource("/" + anchor)
    assert(url != null, s"missing anchor fixture $anchor")
    val dir    = java.nio.file.Paths.get(url.toURI).getParent
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

  /** The items of one fixture. */
  def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines =
      try src.getLines().toVector
      finally src.close()
    ExportReader.fromLines(lines).items

  /** The profile a fixture's format belongs to. */
  def profileOf(name: String): kolla.kernel.KernelProfile =
    if name.contains("3.0.0") then kolla.kernel.KernelProfile.v4_27
    else kolla.kernel.KernelProfile.v4_35
