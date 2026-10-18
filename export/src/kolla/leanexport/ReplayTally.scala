package kolla.leanexport

import kolla.kernel.Name

/** The running tally of a replay.
  *
  * Pure and cross-platform, so the command line, the browser and the
  * differential platform all count the same way and none of them needs a second
  * implementation of what "accepted" means.
  */
final case class ReplayTally(
    accepted: Int = 0,
    rejected: Int = 0,
    carriedOver: Int = 0,
    /** Accepted by an earlier run and skipped on a digest match. */
    cached: Int = 0,
    failed: Int = 0,
    notReached: Int = 0,
    /** The first rejection: the name, the reason and the defeq trace. */
    firstRejection: Option[(Name, String, List[String])] = None
):
  def total: Int = accepted + rejected + carriedOver + cached + failed + notReached

  def add(step: ReplayStep): ReplayTally =
    val n = step.names.length
    step.outcome match
      case ReplayOutcome.Checked        => copy(accepted = accepted + n)
      case _: ReplayOutcome.Cached      => copy(cached = cached + n)
      case _: ReplayOutcome.CarriedOver => copy(carriedOver = carriedOver + n)
      case ReplayOutcome.Rejected(r, t) =>
        copy(
          rejected = rejected + n,
          firstRejection = firstRejection.orElse(step.names.headOption.map(d => (d, r, t)))
        )
      case ReplayOutcome.Failed(r) =>
        copy(
          failed = failed + n,
          firstRejection = firstRejection.orElse(step.names.headOption.map(d => (d, r, Nil)))
        )

  /** Declarations a frontend abandoned rather than judged. */
  def addNotReached(count: Int): ReplayTally = copy(notReached = notReached + count)

  /** Accepted only if something was judged and nothing was rejected.
    *
    * An empty file is not a pass: nothing was checked. See docs/semantics.md K8
    * for why a carried-over declaration is not agreement either.
    *
    * A cache hit counts as judged, because it is this kolla's own verdict on
    * the same content against the same dependencies — which makes the cache
    * file part of what the verdict rests on. See docs/semantics.md P15.
    */
  def ok: Boolean = rejected == 0 && failed == 0 && (accepted + cached) > 0

  def counts: String =
    s"$accepted accepted, $rejected rejected, $carriedOver carried over, $failed errored" +
      (if cached > 0 then s", $cached cached" else "") +
      (if notReached > 0 then s", $notReached not reached" else "")

object ReplayTally:

  /** The one-word name of an outcome, shared by every frontend's output. */
  def label(outcome: ReplayOutcome): String = outcome match
    case ReplayOutcome.Checked        => "accepted"
    case _: ReplayOutcome.CarriedOver => "carried-over"
    case _: ReplayOutcome.Cached      => "cached"
    case _: ReplayOutcome.Rejected    => "rejected"
    case _: ReplayOutcome.Failed      => "error"

  def detail(outcome: ReplayOutcome): Option[String] = outcome match
    case ReplayOutcome.Checked        => None
    case ReplayOutcome.CarriedOver(r) => Some(r)
    case ReplayOutcome.Cached(d)      => Some(s"accepted by an earlier run, digest $d")
    case ReplayOutcome.Rejected(r, _) => Some(r)
    case ReplayOutcome.Failed(r)      => Some(r)

  def trace(outcome: ReplayOutcome): List[String] = outcome match
    case ReplayOutcome.Rejected(_, t) => t
    case _                            => Nil
