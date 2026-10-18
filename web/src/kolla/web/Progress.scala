package kolla.web

import kolla.leanexport.ReplayTally

/** What the page shows while a check runs.
  *
  * Separated from the DOM so it can be tested without a browser: the page is
  * then only the part that writes these strings into elements.
  */
final case class Progress(
    tally: ReplayTally,
    position: Int,
    size: Int,
    elapsedMillis: Long,
    done: Boolean
):
  def percent: Int = if size == 0 then 100 else (position.toDouble / size * 100).toInt

  def status: String =
    if !done then s"checking $position of $size"
    else if size == 0 then "nothing to check"
    else if tally.ok then s"accepted ${tally.accepted} declarations"
    else s"rejected ${tally.rejected} of ${tally.total}"

  /** The class the result banner gets, which is what the smoke test asserts. */
  def verdictClass: String =
    if !done then "running"
    else if size == 0 then "empty"
    else if tally.ok then "accepted"
    else "rejected"

  def counts: String = tally.counts

  def timing: String =
    if size == 0 then ""
    else s"${elapsedMillis}ms"

  def firstRejection: Option[String] =
    tally.firstRejection.map((n, reason, _) => s"$n: ${reason.linesIterator.mkString(" ")}")
