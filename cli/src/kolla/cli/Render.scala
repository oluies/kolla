package kolla.cli

import kolla.kernel.Name
import kolla.leanexport.{ReplayOutcome, ReplayTally}

/** The command line's output formats.
  *
  * The counts come from `ReplayTally` in the export module, which the browser
  * uses too; only the rendering is here.
  */
object Render:

  def label(outcome: ReplayOutcome): String = ReplayTally.label(outcome)

  /** One JSON object per declaration, which is what `difftest` reads back. */
  def json(name: Name, outcome: ReplayOutcome, nanos: Long): String =
    Json.obj(
      "name"    -> Json.str(name.toString),
      "verdict" -> Json.str(label(outcome)),
      "detail"  -> ReplayTally.detail(outcome).fold("null")(Json.str),
      "nanos"   -> Json.num(nanos),
      "trace"   -> Json.arr(ReplayTally.trace(outcome).map(Json.str))
    )

  def summaryJson(file: String, profile: String, platform: String, t: ReplayTally, wallNanos: Long): String =
    Json.obj(
      "summary"   -> Json.str(file),
      "profile"   -> Json.str(profile),
      "platform"  -> Json.str(platform),
      "ok"        -> Json.bool(t.ok),
      "wallNanos" -> Json.num(wallNanos),
      "counts" -> Json.obj(
        "accepted"    -> Json.num(t.accepted.toLong),
        "rejected"    -> Json.num(t.rejected.toLong),
        "carriedOver" -> Json.num(t.carriedOver.toLong),
        "errored"     -> Json.num(t.failed.toLong),
        "notReached"  -> Json.num(t.notReached.toLong),
        "total"       -> Json.num(t.total.toLong)
      )
    )

  /** The human summary: counts, then the first rejection if there was one. */
  def summary(file: String, profile: String, t: ReplayTally, wallNanos: Long): String =
    val sb = new StringBuilder
    sb ++= s"$file: ${t.counts} as $profile in ${wallNanos / 1000000L}ms\n"
    t.firstRejection.foreach { (n, reason, trace) =>
      sb ++= s"\nfirst rejection: $n\n"
      reason.linesIterator.foreach(l => sb ++= s"  $l\n")
      if trace.nonEmpty then
        sb ++= "  defeq trace:\n"
        trace.foreach(l => sb ++= s"    $l\n")
    }
    sb.result()
