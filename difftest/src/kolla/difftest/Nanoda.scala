package kolla.difftest

import cats.effect.IO
import kolla.kernel.Name
import kolla.kernel.KernelProfile
import kolla.leanexport.ExportFormat
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** Runs nanoda_lib as a second reference checker.
  *
  * Unlike `lean4checker`, nanoda reads an export file rather than oleans, so it
  * is not built against a Lean toolchain and one build serves every release.
  * What it is tied to is the export *format*: it accepts 3.1.0 up to but not
  * including 3.2.0 (`check_semver` in `src/parser.rs`), which in this matrix
  * means v4.28.0 and v4.35.0.
  *
  * That makes it the reference for v4.35.0, which `lean4checker` has no release
  * for. Like `lean4checker` it reports one verdict for the whole file: a bad
  * declaration panics out of `check_all_declars`.
  */
object Nanoda:

  val name = "nanoda"

  val repo = "https://github.com/ammkrn/nanoda_lib.git"

  /** The axioms a Lean export is expected to use. */
  val permittedAxioms = List("propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler")

  /** Whether nanoda can read a format at all. */
  def supports(format: ExportFormat): Boolean =
    format.ndjsonMajorMinor.exists((major, minor) => major == 3 && minor == 1)

  /** Whether nanoda's kernel semantics are those of a toolchain.
    *
    * nanoda tracks current Lean and has no notion of a release: it looks up
    * `String.ofList` unconditionally, which does not exist before v4.27, and it
    * implements the v4.35 behaviours unconditionally. Running it against an
    * older release produces disagreements that say nothing about kolla, so it
    * is a reference only for the newest profile. See docs/semantics.md P9.
    */
  def matchesKernel(t: Toolchain): Boolean = t.profile == KernelProfile.v4_35

  /** Whether nanoda is usable as a reference for a toolchain and format. */
  def applies(t: Toolchain, format: ExportFormat): Boolean = supports(format) && matchesKernel(t)

  private def dir: Path = Layout.cacheDir.resolve("nanoda")

  private def bin: Path = dir.resolve("target/release/nanoda_bin")

  /** Clones and builds nanoda, once. */
  def provision: IO[Option[Path]] =
    IO.blocking(Files.exists(bin)).flatMap { built =>
      if built then IO.pure(Some(bin))
      else
        val steps =
          for
            _ <- IO.blocking {
                   Files.createDirectories(dir.getParent)
                   Fs.removeRecursively(dir)
                 }
            _ <- Proc.run(Seq("git", "clone", "--quiet", "--depth", "1", repo, dir.toString))
                   .flatMap(_.orFail("git clone nanoda_lib"))
            _ <- Proc.run(Seq("cargo", "build", "--release"), cwd = Some(dir))
                   .flatMap(_.orFail("cargo build nanoda_lib"))
          yield Some(bin)
        Proc.which("cargo").flatMap {
          case None    => IO.println("  nanoda unavailable: cargo is not on PATH").as(None)
          case Some(_) => steps.handleErrorWith(e => IO.println(s"  nanoda unavailable: ${e.getMessage}").as(None))
        }
    }

  /** The declaration name a corpus-level verdict is recorded under. */
  def corpusDecl(corpus: String): Name = Name.Anonymous.str(s"<corpus:$corpus>")

  /** The configuration file nanoda takes in place of a command line. */
  def config(exportFile: Path): String =
    Json.obj(
      "export_file_path" -> Json.str(exportFile.toString),
      "use_stdin"        -> Json.bool(false),
      "permitted_axioms" -> Json.arr(permittedAxioms.map(Json.str)),
      // An export file declares axioms its declarations never use, such as
      // `sorryAx`; those are skipped rather than failing the run.
      "unpermitted_axiom_hard_error" -> Json.bool(false),
      "nat_extension"                -> Json.bool(true),
      "string_extension"             -> Json.bool(true),
      // The success message is a pretty-printer report, and with no
      // `pp_declars` it reports an error for the axioms it cannot print. The
      // exit code is the verdict.
      "print_success_message" -> Json.bool(false)
    )

  def run(
      binary: Option[Path],
      toolchain: Toolchain,
      corpus: Corpus,
      format: ExportFormat,
      exportFile: Path,
      timeout: FiniteDuration = 30.minutes
  ): IO[CheckerRun] =
    val base = CheckerRun(
      checker = name,
      toolchain = toolchain.spec,
      corpus = corpus.name,
      platform = "jvm",
      results = Vector.empty,
      wallNanos = 0L,
      peakHeapBytes = 0L,
      expectRejection = corpus.expectRejection,
      perDeclaration = false
    )
    (binary, applies(toolchain, format)) match
      case (None, _) => IO.pure(base.copy(failure = Some("nanoda was not built")))
      case (_, false) if !supports(format) =>
        IO.pure(base.copy(failure = Some(s"nanoda does not read the $format export format")))
      case (_, false) =>
        IO.pure(base.copy(failure = Some(s"nanoda does not implement the ${toolchain.profile.label} kernel")))
      case (Some(b), true) =>
        val cfg = Layout.toolchainCache(toolchain).resolve(s"nanoda-${corpus.name}.json")
        for
          _ <- IO.blocking(Layout.writeFile(cfg, config(exportFile)))
          r <- Proc.run(Seq(b.toString, cfg.toString), timeout = Some(timeout))
        yield
          val verdict =
            if r.timedOut then Verdict.Error(s"timed out after ${timeout.toSeconds}s")
            else if r.ok then Verdict.Accepted
            else Verdict.Rejected(reason(r))
          base.copy(
            results = Vector(DeclResult(corpusDecl(corpus.name), verdict, r.nanos)),
            wallNanos = r.nanos
          )

  /** The panic message, which names the assertion that failed. */
  private def reason(r: ProcResult): String =
    val text = if r.stderr.trim.nonEmpty then r.stderr else r.stdout
    val body = text.linesIterator.filter(!_.startsWith("note: run with")).mkString("\n").trim.takeRight(2000)
    if body.isEmpty then s"exit code ${r.exitCode}" else body
