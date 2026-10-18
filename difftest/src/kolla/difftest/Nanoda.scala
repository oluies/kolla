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
  *
  * Two separate gates apply. `supports` is about the reader: nanoda accepts
  * format 3.1.0 up to but not including 3.2.0 (`check_semver` in
  * `src/parser.rs`), and since lean4export backported 3.1.0 to every release
  * tag, every export in this matrix is readable. `matchesKernel` is what
  * narrows nanoda to v4.35.0, and it is the gate to look at when nanoda did not
  * run: nanoda implements the v4.35 behaviours unconditionally and looks up
  * `String.ofList`, which does not exist before v4.27.
  *
  * That makes it the reference for v4.35.0, which `lean4checker` has no release
  * for. Like `lean4checker` it reports one verdict for the whole file: a bad
  * declaration panics out of `check_all_declars`.
  */
object Nanoda:

  val name = "nanoda"

  val repo = "https://github.com/ammkrn/nanoda_lib.git"

  /** The nanoda revision the platform builds.
    *
    * Pinned for the same reason `Provision.resolveRevision` pins the Lean tools
    * (docs/semantics.md P1): nanoda tracks current Lean, so an unpinned clone
    * would make the v4.35.0 run report a disagreement the first time upstream
    * implements a kernel change, with nothing in kolla having moved, and two
    * machines provisioning on different days would not be running the same
    * reference. Bumping this is a deliberate act with a difftest run behind it.
    */
  val rev = "f67473ba5f9397266f89c7852082c9c914b5d219"

  /** The axioms a Lean export is expected to use. */
  val permittedAxioms = List("propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler")

  /** Whether nanoda can read a format at all. Not the gate that restricts it to
    * one toolchain; see `matchesKernel`.
    */
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

  /** The marker is named after the revision, so bumping `rev` rebuilds. */
  private def marker: Path = dir.resolve(s".built-${rev.take(12)}")

  /** Clones and builds the pinned nanoda revision, once. */
  def provision: IO[Option[Path]] =
    IO.blocking(Files.exists(marker) && Files.exists(bin)).flatMap { built =>
      if built then IO.pure(Some(bin))
      else
        val steps =
          for
            _ <- IO.blocking {
                   Files.createDirectories(dir.getParent)
                   Fs.removeRecursively(dir)
                 }
            // Not `--depth 1`: the pinned revision need not be the branch tip.
            _ <- Proc.run(Seq("git", "clone", "--quiet", repo, dir.toString))
                   .flatMap(_.orFail("git clone nanoda_lib"))
            _ <- Proc.run(Seq("git", "checkout", "--quiet", rev), cwd = Some(dir))
                   .flatMap(_.orFail(s"git checkout $rev in nanoda_lib"))
            _ <- Proc.run(Seq("cargo", "build", "--release"), cwd = Some(dir))
                   .flatMap(_.orFail("cargo build nanoda_lib"))
            _ <- IO.blocking(Files.write(marker, Array.emptyByteArray)).void
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
