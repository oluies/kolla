package kolla.cli

import kolla.kernel.Name
import kolla.leanexport.{ReplayJson, ReplayOutcome, ReplayTally}

/** The command line's output formats.
  *
  * The counts come from `ReplayTally` in the export module, which the browser
  * uses too; only the rendering is here.
  */
object Render:

  def label(outcome: ReplayOutcome): String = ReplayTally.label(outcome)

  /** One JSON object per declaration, which is what `difftest` reads back. */
  def json(name: Name, outcome: ReplayOutcome, nanos: Long): String =
    ReplayJson.declaration(name, outcome, nanos)

  def summaryJson(file: String, profile: String, platform: String, t: ReplayTally, wallNanos: Long): String =
    ReplayJson.summary(file, profile, platform, t, wallNanos)

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
