package kolla.difftest

import java.nio.file.{Files, Path, Paths as JPaths}

/** Where the platform keeps its inputs and outputs.
  *
  * Paths are resolved against the repository root, found by walking up from the
  * working directory, so the driver behaves the same whether it is started from
  * the root or from a module directory.
  */
object Layout:

  private val marker = "build.mill"

  lazy val repoRoot: Path =
    var cur = JPaths.get("").toAbsolutePath.normalize
    while cur != null && !Files.exists(cur.resolve(marker)) do cur = cur.getParent
    if cur == null then
      throw new IllegalStateException(s"could not find $marker above ${JPaths.get("").toAbsolutePath}")
    cur

  def repoFile(rel: String): Path = repoRoot.resolve(rel)

  /** `difftest/toolchains.txt`. */
  def toolchainsFile: Path = repoFile("difftest/toolchains.txt")

  /** `difftest/mathlib-sample.txt`. */
  def mathlibSampleFile: Path = repoFile("difftest/mathlib-sample.txt")

  /** `difftest/lean/ListDecls.lean`, which prints a module's own declarations. */
  def listDeclsScript: Path = repoFile("difftest/lean/ListDecls.lean")

  /** `difftest/cases/`, the handwritten corpus. */
  def casesDir: Path = repoFile("difftest/cases")

  /** `difftest/test/resources/`, export files committed to the repository.
    *
    * These are real lean4export output, so they are a corpus that needs no
    * toolchain: enough to compare kolla's own builds against each other on
    * every push.
    */
  def fixturesDir: Path = repoFile("difftest/test/resources")

  /** `difftest/cases-negative/`, declarations the kernel has to reject. */
  def negativeCasesDir: Path = repoFile("difftest/cases-negative")

  /** `difftest/history/`, timing tracked over commits. */
  def historyDir: Path = repoFile("difftest/history")

  /** `.difftest/`, the cache: toolchains, tool builds and exports. */
  def cacheDir: Path = repoFile(".difftest")

  def toolchainCache(t: Toolchain): Path = cacheDir.resolve(t.slug)

  def exportFile(t: Toolchain, corpus: String): Path =
    toolchainCache(t).resolve(s"$corpus.export")

  def reportsDir: Path = cacheDir.resolve("reports")

  def readFile(p: Path): String = new String(Files.readAllBytes(p), "UTF-8")

  def writeFile(p: Path, contents: String): Unit =
    Files.createDirectories(p.getParent)
    Files.write(p, contents.getBytes("UTF-8"))
