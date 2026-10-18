package kolla.difftest

import cats.effect.IO
import kolla.kernel.{KernelProfile, Name}
import kolla.leanexport.Json
import kolla.leanexport.Json.{asArr, asBigInt, asObj, asStr, opt, req}
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** Runs kolla's other builds and reads their verdicts back.
  *
  * The native binary and the browser bundle emit the same JSON stream the
  * command line writes with `--json`, so a platform's run parses into the same
  * `CheckerRun` the JVM produces and the two are compared declaration by
  * declaration rather than by a count. A count would hide two platforms
  * disagreeing about which declarations they rejected.
  */
object Platforms:

  /** Where `mill cli.native.nativeLink` and `mill web.js.bundle` leave their
    * output. Taking them from the build's own layout avoids a second place
    * where the paths are written down, at the cost of needing the build to
    * have run.
    */
  def nativeBinary: Path = Layout.repoFile("out/cli/native/nativeLink.dest/out")
  def webBundle: Path    = Layout.repoFile("out/web/js/bundle.dest")

  def nativeAvailable: IO[Boolean] = IO.blocking(Files.isExecutable(nativeBinary))
  def nodeAvailable: IO[Boolean] =
    IO.blocking(Files.exists(webBundle.resolve("run.js"))).flatMap { bundled =>
      if !bundled then IO.pure(false) else Proc.which("node").map(_.isDefined)
    }

  /** The native binary, as a run. */
  def native(
      exportFile: Path,
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      timeout: FiniteDuration = 30.minutes
  ): IO[CheckerRun] =
    run(
      "native",
      Seq(nativeBinary.toString, "--json", "--profile", profile.label, exportFile.toString),
      toolchain, corpus, timeout, rejectionExitCode = Some(1)
    )

  /** The browser bundle under Node, as a run. */
  def node(
      exportFile: Path,
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      timeout: FiniteDuration = 30.minutes
  ): IO[CheckerRun] =
    run(
      "js",
      Seq("node", webBundle.resolve("run.js").toString, exportFile.toString, profile.label),
      toolchain, corpus, timeout, rejectionExitCode = None
    )

  /** The published page in a real browser, driven by Playwright.
    *
    * The script fills the box, picks the profile and presses the button, then
    * checks that what the page shows agrees with what the checker concluded
    * before printing the verdicts. A page that renders a different count from
    * the one it computed is a bug the JSON alone would not catch.
    */
  def browser(
      exportFile: Path,
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      timeout: FiniteDuration = 30.minutes
  ): IO[CheckerRun] =
    run(
      "browser",
      // `smoke.js` exits non-zero only when the page misbehaved; a rejected
      // declaration is in its output, not its exit code.
      Seq("node", webBundle.resolve("smoke.js").toString, webBundle.toString, exportFile.toString, profile.label),
      toolchain, corpus, timeout, rejectionExitCode = None
    )

  /** Playwright is a development dependency; a machine without it has not
    * found a bug, so the browser run is skipped rather than failed.
    */
  def browserAvailable: IO[Boolean] =
    IO.blocking(Files.exists(webBundle.resolve("smoke.js"))).flatMap { bundled =>
      if !bundled then IO.pure(false)
      else
        Proc.which("node").flatMap {
          case None => IO.pure(false)
          case Some(_) =>
            Proc
              .run(Seq("node", "-e", "require('playwright')"), timeout = Some(2.minutes))
              .map(_.ok)
        }
    }

  private def run(
      platform: String,
      cmd: Seq[String],
      toolchain: String,
      corpus: String,
      timeout: FiniteDuration,
      /** The code this command uses for "a declaration was rejected", which is
        * a verdict rather than a failure. `None` means every non-zero code is a
        * failure.
        */
      rejectionExitCode: Option[Int]
  ): IO[CheckerRun] =
    val empty = CheckerRun(KollaChecker.name, toolchain, corpus, platform, Vector.empty, 0L, 0L)
    Proc.run(cmd, timeout = Some(timeout)).map { r =>
      val expected = r.exitCode == 0 || rejectionExitCode.contains(r.exitCode)
      if r.timedOut then empty.copy(failure = Some(s"$platform timed out after ${timeout.toSeconds}s"))
      // 3 is `smoke.js` reporting that Playwright is not installed.
      else if r.exitCode == 3 then empty.copy(failure = Some(s"$platform unavailable: ${r.stderr.trim}"))
      else if !expected then
        empty.copy(failure = Some(s"$platform exited ${r.exitCode}: ${r.stderr.trim.takeRight(2000)}"))
      else parse(r.stdout, empty, r.nanos)
    }

  /** Reads the JSON stream back into verdicts.
    *
    * A missing or disagreeing summary is a failure rather than a short run:
    * silently comparing a truncated stream against a full one would report
    * agreement on the part that arrived.
    */
  def parse(stdout: String, template: CheckerRun, wallNanos: Long): CheckerRun =
    val results = Vector.newBuilder[DeclResult]
    var summary = Option.empty[Map[String, Json]]
    var failure = Option.empty[String]
    stdout.linesIterator.map(_.trim).filter(_.nonEmpty).foreach { line =>
      try
        val j = Json.parse(line).asObj("output line")
        if j.contains("summary") then summary = Some(j) else results += declResult(j)
      catch
        case _: Throwable => if failure.isEmpty then failure = Some(s"unreadable output line: ${line.take(200)}")
    }
    val got     = results.result()
    val counted = summary.flatMap(_.opt("counts")).map(_.asObj("counts")).flatMap(_.opt("total")).map(_.asBigInt("total"))
    val mismatch =
      counted.filter(_ != BigInt(got.length)).map(t => s"the summary says $t declarations but ${got.length} were read")
    template.copy(
      results = got,
      wallNanos = summary.flatMap(_.opt("wallNanos")).map(_.asBigInt("wallNanos").toLong).getOrElse(wallNanos),
      failure = failure.orElse(mismatch).orElse(if summary.isEmpty then Some("no summary line") else None)
    )

  private def declResult(j: Map[String, Json]): DeclResult =
    val name   = Name.parse(j.req("name", "declaration").asStr("name"))
    val detail = j.opt("detail").filter(_ != Json.Null).map(_.asStr("detail"))
    val verdict = j.req("verdict", "declaration").asStr("verdict") match
      case "accepted"     => Verdict.Accepted
      case "rejected"     => Verdict.Rejected(detail.getOrElse(""))
      case "carried-over" => Verdict.NotChecked(detail.getOrElse(""))
      case "error"        => Verdict.Error(detail.getOrElse(""))
      case other          => Verdict.Error(s"unknown verdict '$other'")
    val trace = j.opt("trace").toList.flatMap(_.asArr("trace").map(_.asStr("trace entry")))
    DeclResult(name, verdict, j.opt("nanos").map(_.asBigInt("nanos").toLong).getOrElse(0L), trace)
