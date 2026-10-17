package kolla.difftest

import cats.effect.IO
import java.nio.file.Path

/** Everything one invocation of the platform produced. */
final case class Report(
    commit: String,
    startedAt: String,
    runs: Vector[CheckerRun],
    comparisons: Vector[Comparison],
    overall: Vector[OverallAgreement],
    mutations: Vector[MutationOutcome] = Vector.empty
):
  /** Runs over a positive corpus that rejected or errored on something.
    *
    * Every corpus is an export of an environment Lean itself accepted, so a
    * rejection is a kolla bug whether or not a reference checker was available
    * to disagree with it.
    */
  def falseRejections: Vector[CheckerRun] =
    runs.filter(r => r.checker == KollaChecker.name && !r.expectRejection && r.unexpected.nonEmpty)

  /** Runs over a negative corpus that accepted everything.
    *
    * A negative corpus holds a declaration Lean put into the environment
    * without the kernel's consent, so a checker that judges it must reject
    * something. Accepting the lot is the failure this catches, and it is what
    * keeps the positive corpora from being the only thing the platform proves.
    */
  def missedRejections: Vector[CheckerRun] =
    runs.filter(r => r.expectRejection && r.rejected == 0)

  /** True when every comparison agreed and no run failed outright. */
  def agrees: Boolean =
    comparisons.forall(_.agrees) && overall.forall(_.agrees) &&
      mutations.forall(_.asExpected) && runs.forall(_.failure.isEmpty) &&
      falseRejections.isEmpty && missedRejections.isEmpty

  def json: String =
    Json.obj(
      "commit"      -> Json.str(commit),
      "startedAt"   -> Json.str(startedAt),
      "agrees"      -> Json.bool(agrees),
      "falseRejections"  -> Json.num(falseRejections.map(_.unexpected.length.toLong).sum),
      "missedRejections" -> Json.num(missedRejections.length.toLong),
      "runs"        -> Json.arr(runs.map(_.json)),
      "comparisons" -> Json.arr(comparisons.map(_.json)),
      "overall"     -> Json.arr(overall.map(_.json)),
      "mutations"   -> Json.arr(mutations.map(_.json))
    )

  def render: String =
    val sb = new StringBuilder
    sb ++= s"kolla difftest $commit ($startedAt)\n\n"
    runs.foreach { r =>
      sb ++= f"  ${r.checker}%-14s ${r.toolchain}%-26s ${r.corpus}%-18s ${r.platform}%-6s "
      sb ++= s"${r.accepted} accepted, ${r.rejected} rejected, ${r.notChecked} not-checked, ${r.errored} errored"
      r.failure.foreach(f => sb ++= s" [FAILED: ${f.linesIterator.next()}]")
      sb ++= "\n"
    }
    if falseRejections.nonEmpty then
      sb ++= "\nfalse rejections on a positive corpus\n"
      falseRejections.foreach { r =>
        sb ++= s"  ${r.toolchain} / ${r.corpus} / ${r.platform}\n"
        r.unexpected.take(5).foreach { d =>
          sb ++= s"    ${d.name}: ${d.verdict.detail.getOrElse("").linesIterator.next()}\n"
        }
        if r.unexpected.length > 5 then sb ++= s"    ... and ${r.unexpected.length - 5} more\n"
      }
    if missedRejections.nonEmpty then
      sb ++= "\nmissed rejections on a negative corpus\n"
      missedRejections.foreach(r => sb ++= s"  ${r.checker} accepted all of ${r.toolchain} / ${r.corpus}\n")
    if comparisons.nonEmpty then
      sb ++= "\nper-declaration comparisons\n"
      comparisons.foreach(c => sb ++= c.render)
    if overall.nonEmpty then
      sb ++= "\ncorpus-level comparisons\n"
      overall.foreach(o => sb ++= o.render)
    if mutations.nonEmpty then
      sb ++= s"\nmutants (${mutations.count(_.asExpected)}/${mutations.length} as expected)\n"
      mutations.filter(!_.asExpected).foreach(m => sb ++= m.render)
    sb ++= (if agrees then "\nAGREE\n" else "\nDISAGREE\n")
    sb.result()

object Report:

  /** Writes the report under `.difftest/reports/` and returns the JSON path. */
  def write(report: Report): IO[Path] =
    val stem = s"${report.startedAt.replace(':', '-')}-${report.commit.take(12)}"
    val json = Layout.reportsDir.resolve(s"$stem.json")
    val txt  = Layout.reportsDir.resolve(s"$stem.txt")
    IO.blocking {
      Layout.writeFile(json, report.json)
      Layout.writeFile(txt, report.render)
      json
    }

  def now: IO[String] =
    IO.realTimeInstant.map(i => i.toString.take(19) + "Z")

  def commit: IO[String] =
    Proc
      .run(Seq("git", "rev-parse", "HEAD"), cwd = Some(Layout.repoRoot))
      .map(r => if r.ok then r.stdout.trim else "unknown")
