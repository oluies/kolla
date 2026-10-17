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

  def run(
      tools: Provision.Tools,
      corpus: Corpus,
      timeout: FiniteDuration = 30.minutes
  ): IO[CheckerRun] =
    tools.lean4checker match
      case None =>
        IO.pure(
          empty(tools, corpus).copy(failure = Some(s"lean4checker is not available for ${tools.toolchain.spec}"))
        )
      case Some(dir) => runWith(tools, dir, corpus, timeout)

  private def empty(tools: Provision.Tools, corpus: Corpus): CheckerRun =
    CheckerRun(
      checker = name,
      toolchain = tools.toolchain.spec,
      corpus = corpus.name,
      platform = "jvm",
      results = Vector.empty,
      wallNanos = 0L,
      peakHeapBytes = 0L,
      perDeclaration = false
    )

  private def runWith(
      tools: Provision.Tools,
      dir: Path,
      corpus: Corpus,
      timeout: FiniteDuration
  ): IO[CheckerRun] =
    // A single handwritten module is checked with `--fresh`, which replays its
    // imports too, so the declaration set matches the export file kolla reads.
    val fresh    = corpus.source.isDefined && corpus.modules.length == 1
    val flags    = if fresh then Seq("--fresh") else Seq.empty
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
        else Verdict.Rejected(reason(r))
      empty(tools, corpus).copy(
        results = Vector(DeclResult(corpusDecl(corpus.name), verdict, r.nanos)),
        wallNanos = r.nanos
      )

  /** The directory handwritten cases are compiled into, if it exists. */
  private def casesPath(tools: Provision.Tools): IO[Option[Path]] =
    val p = Layout.toolchainCache(tools.toolchain).resolve("cases")
    IO.blocking(if Files.isDirectory(p) then Some(p) else None)

  /** The failure text, preferring stderr, which is where the problem is named. */
  private def reason(r: ProcResult): String =
    val text = if r.stderr.trim.nonEmpty then r.stderr else r.stdout
    val body = text.trim.takeRight(2000)
    if body.isEmpty then s"exit code ${r.exitCode}" else body
