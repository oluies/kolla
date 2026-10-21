package kolla.difftest

import cats.effect.IO
import kolla.kernel.Name
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** Runs `lean4checker` as the reference checker.
  *
  * `lean4checker` replays a module's declarations through Lean's own kernel and
  * reports a single accept/reject for the whole module: it aborts on the first
  * problem and names only the module, not the declaration. Its runs are
  * therefore `perDeclaration = false` and are comparable only through
  * `CheckerRun.overall`.
  */
object Lean4Checker:

  val name = "lean4checker"

  /** The synthetic declaration name a corpus-level verdict is recorded under. */
  def corpusDecl(corpus: String): Name = Name.Anonymous.str(s"<corpus:$corpus>")

  private def bin(dir: Path): Path = dir.resolve(".lake/build/bin/lean4checker")

  /** Workers for a corpus the size of a library.
    *
    * `lean4checker` defaults to 8, and its own source says that is already
    * chosen to avoid exhausting a 32 GB machine on a large project. Each worker
    * loads a near-complete environment, so a library corpus is run with fewer:
    * the wall time matters less than finishing.
    */
  val libraryWorkers: Int = 2

  /** How long to give the reference on a corpus the size of a library.
    *
    * The default 30 minutes is sized for a handwritten case. On the v4.28.0
    * mathlib sample it expired while kolla accepted all 17,240 declarations,
    * and the run was then reported as a disagreement rather than as a
    * reference that had not answered (P17). Replaying mathlib's modules
    * through Lean's own kernel is hours of work, so the budget says so.
    */
  val libraryTimeout: FiniteDuration = 6.hours

  def run(
      tools: Provision.Tools,
      corpus: Corpus,
      timeout: FiniteDuration = 30.minutes,
      numWorkers: Option[Int] = None
  ): IO[CheckerRun] =
    tools.lean4checker match
      case None =>
        IO.pure(
          empty(tools, corpus).copy(failure = Some(s"lean4checker is not available for ${tools.toolchain.spec}"))
        )
      case Some(dir) => runWith(tools, dir, corpus, timeout, numWorkers)

  private def empty(tools: Provision.Tools, corpus: Corpus): CheckerRun =
    CheckerRun(
      checker = name,
      toolchain = tools.toolchain.spec,
      corpus = corpus.name,
      platform = "jvm",
      results = Vector.empty,
      wallNanos = 0L,
      peakHeapBytes = 0L,
      expectRejection = corpus.expectRejection,
      perDeclaration = false
    )

  private def runWith(
      tools: Provision.Tools,
      dir: Path,
      corpus: Corpus,
      timeout: FiniteDuration,
      numWorkers: Option[Int]
  ): IO[CheckerRun] =
    // A single handwritten module is checked with `--fresh`, which replays its
    // imports too, so the declaration set matches the export file kolla reads.
    val fresh    = corpus.source.isDefined && corpus.modules.length == 1
    val flags    = (if fresh then Seq("--fresh") else Seq.empty) ++
      numWorkers.map(n => s"--num-workers=$n").toSeq
    val checker  = bin(dir).toString
    val baseCmd  = Seq("elan", "run", tools.toolchain.spec)
    val cmd =
      if corpus.project.isDefined then baseCmd ++ Seq("lake", "env", checker) ++ flags ++ corpus.modules
      else baseCmd ++ Seq(checker) ++ flags ++ corpus.modules

    for
      searchPath <- corpus.source.fold(IO.pure(Option.empty[Path]))(_ => casesPath(tools))
      env = searchPath.fold(Map.empty[String, String])(p => Map("LEAN_PATH" -> p.toString))
      r <- Proc.run(cmd, cwd = corpus.project, env = env, timeout = Some(timeout))
    yield
      val verdict =
        if r.timedOut then Verdict.Error(s"timed out after ${timeout.toSeconds}s")
        else if r.ok then Verdict.Accepted
        else if rejected(r) then Verdict.Rejected(reason(r))
        else Verdict.Error(reason(r))
      empty(tools, corpus).copy(
        results = Vector(DeclResult(corpusDecl(corpus.name), verdict, r.nanos)),
        wallNanos = r.nanos
      )

  /** The directory handwritten cases are compiled into, if it exists. */
  private def casesPath(tools: Provision.Tools): IO[Option[Path]] =
    val p = Layout.toolchainCache(tools.toolchain).resolve("cases")
    IO.blocking(if Files.isDirectory(p) then Some(p) else None)

  /** Output that means the reference never ran, rather than ran and refused.
    *
    * These are the ways `elan run` and `lake env` fail before `lean4checker`
    * sees the corpus: a release that will not download, a toolchain that is
    * not installed, a binary that is not there.
    */
  val notRunMarkers: List[String] = List(
    "could not download",
    "error during download",
    "is not installed",
    "unknown executable",
    "no such file or directory",
    "command not found"
  )

  /** Whether a non-zero exit was the reference rejecting something.
    *
    * The default is yes, which is what it was before P19, and the exceptions
    * are named rather than inferred. The first attempt at this inverted the
    * test — it asked for the string `lean4checker found a problem` and called
    * anything else a failure to run — and that was wrong twice over. That text
    * comes from the path that replays several modules; a handwritten case runs
    * with `--fresh` on one module, where the exception is simply rethrown and
    * the output reads `uncaught exception: (kernel) declaration type mismatch`.
    * So every negative corpus at v4.25.0, v4.27.0 and v4.28.0 stopped being
    * compared, which is a reference checker quietly switching itself off.
    *
    * Defaulting to a rejection fails loudly when this judgement is wrong. The
    * other way round fails silently, and a silent loss of comparison is worse
    * than a disagreement someone has to look at. See docs/semantics.md P19.
    */
  def rejected(r: ProcResult): Boolean =
    val out = r.stderr + r.stdout
    !notRunMarkers.exists(out.contains)

  /** The failure text, preferring stderr, which is where the problem is named. */
  private def reason(r: ProcResult): String =
    val text = if r.stderr.trim.nonEmpty then r.stderr else r.stdout
    val body = text.trim.takeRight(2000)
    if body.isEmpty then s"exit code ${r.exitCode}" else body
