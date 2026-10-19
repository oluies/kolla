package kolla.difftest

import kolla.kernel.Name

/** One declaration where two checkers disagreed. */
final case class Disagreement(
    name: Name,
    reference: Verdict,
    subject: Verdict,
    trace: List[String]
):
  def json: String =
    Json.obj(
      "name"      -> Json.str(name.toString),
      "reference" -> Json.str(reference.label),
      "referenceDetail" -> reference.detail.fold("null")(Json.str),
      "subject"   -> Json.str(subject.label),
      "subjectDetail"   -> subject.detail.fold("null")(Json.str),
      "trace"     -> Json.arr(trace.map(Json.str))
    )

  def render: String =
    val sb = new StringBuilder
    sb ++= s"  $name\n"
    sb ++= s"    reference: ${reference.label}${reference.detail.fold("")(d => s" ($d)")}\n"
    sb ++= s"    kolla:     ${subject.label}${subject.detail.fold("")(d => s" ($d)")}\n"
    if trace.nonEmpty then
      sb ++= "    defeq trace:\n"
      trace.foreach(t => sb ++= s"      $t\n")
    sb.result()

/** The result of diffing a subject run against a reference run. */
final case class Comparison(
    reference: CheckerRun,
    subject: CheckerRun,
    disagreements: Vector[Disagreement],
    /** Declarations only one of the two produced a judgement for. */
    onlyInReference: Vector[Name],
    onlyInSubject: Vector[Name],
    comparable: Int
):
  def agrees: Boolean = disagreements.isEmpty && onlyInReference.isEmpty && onlyInSubject.isEmpty

  /** Subject wall time over reference wall time. */
  def timeRatio: Double =
    if reference.wallNanos == 0L then Double.NaN
    else subject.wallNanos.toDouble / reference.wallNanos.toDouble

  def json: String =
    Json.obj(
      "toolchain"     -> Json.str(subject.toolchain),
      "corpus"        -> Json.str(subject.corpus),
      "platform"      -> Json.str(subject.platform),
      "reference"     -> Json.str(reference.checker),
      "subject"       -> Json.str(subject.checker),
      "agrees"        -> Json.bool(agrees),
      "comparable"    -> Json.num(comparable.toLong),
      "timeRatio"     -> Json.num(timeRatio),
      "referenceWallNanos" -> Json.num(reference.wallNanos),
      "subjectWallNanos"   -> Json.num(subject.wallNanos),
      "referencePeakHeapBytes" -> Json.num(reference.peakHeapBytes),
      "subjectPeakHeapBytes"   -> Json.num(subject.peakHeapBytes),
      "disagreements"   -> Json.arr(disagreements.map(_.json)),
      "onlyInReference" -> Json.arr(onlyInReference.map(n => Json.str(n.toString))),
      "onlyInSubject"   -> Json.arr(onlyInSubject.map(n => Json.str(n.toString)))
    )

  def render: String =
    val sb = new StringBuilder
    sb ++= s"${subject.toolchain} / ${subject.corpus} / ${subject.platform}: "
    sb ++= (if agrees then "agrees" else s"${disagreements.length} disagreement(s)")
    sb ++= f" (${comparable} comparable, ratio ${timeRatio}%.2fx vs ${reference.checker})\n"
    disagreements.foreach(d => sb ++= d.render)
    if onlyInReference.nonEmpty then
      sb ++= s"  only ${reference.checker} judged: ${onlyInReference.take(10).mkString(", ")}\n"
    if onlyInSubject.nonEmpty then
      sb ++= s"  only ${subject.checker} judged: ${onlyInSubject.take(10).mkString(", ")}\n"
    sb.result()

object Compare:

  /** Diffs a subject run against a reference run.
    *
    * Only declarations both checkers produced a *judgement* for are compared: a
    * `NotChecked` on either side is not agreement, so it is reported separately
    * rather than silently counted as a match. See docs/semantics.md K8.
    */
  def apply(reference: CheckerRun, subject: CheckerRun): Comparison =
    val ref = reference.byName
    val sub = subject.byName
    val disagreements = Vector.newBuilder[Disagreement]
    val onlyRef       = Vector.newBuilder[Name]
    val onlySub       = Vector.newBuilder[Name]
    var comparable    = 0

    (ref.keySet ++ sub.keySet).toVector.sortBy(_.toString).foreach { n =>
      val r = ref.get(n).map(_.verdict)
      val s = sub.get(n).map(_.verdict)
      (r, s) match
        case (Some(rv), Some(sv)) if rv.isJudgement && sv.isJudgement =>
          comparable += 1
          if rv.label != sv.label then
            disagreements += Disagreement(n, rv, sv, sub.get(n).map(_.trace).getOrElse(Nil))
        case (Some(rv), Some(sv)) =>
          if rv.isJudgement then onlyRef += n
          if sv.isJudgement then onlySub += n
        case (Some(rv), None) => if rv.isJudgement then onlyRef += n
        case (None, Some(sv)) => if sv.isJudgement then onlySub += n
        case (None, None)     => ()
    }
    Comparison(reference, subject, disagreements.result(), onlyRef.result(), onlySub.result(), comparable)

  /** Compares two subject runs that must agree exactly, used across platforms. */
  def platforms(a: CheckerRun, b: CheckerRun): Comparison = apply(a, b)

  /** Compares only the corpus-level decision, which is all a checker that
    * reports per module can be held to.
    */
  def overall(reference: CheckerRun, subject: CheckerRun): OverallAgreement =
    OverallAgreement(reference, subject)

/** Agreement on the corpus-level accept/reject decision. */
final case class OverallAgreement(reference: CheckerRun, subject: CheckerRun):
  def referenceVerdict: Verdict = reference.overall
  def subjectVerdict: Verdict   = subject.overall

  /** Both sides must have reached a judgement, and it must be the same one. */
  def agrees: Boolean =
    comparable && referenceVerdict.label == subjectVerdict.label

  /** Whether there was anything to compare: both sides reached a judgement. */
  def comparable: Boolean =
    referenceVerdict.isJudgement && subjectVerdict.isJudgement

  /** The reference reached no verdict while the subject did.
    *
    * This is not a disagreement. A reference that timed out, was not built, or
    * does not cover the toolchain has said nothing about the corpus, and
    * holding kolla's verdict against silence would report a difference of
    * opinion where there is only a missing opinion. A subject that reaches no
    * verdict is a different matter and stays a failure.
    * See docs/semantics.md P17.
    */
  def referenceUnavailable: Boolean =
    !referenceVerdict.isJudgement && subjectVerdict.isJudgement

  def json: String =
    Json.obj(
      "toolchain" -> Json.str(subject.toolchain),
      "corpus"    -> Json.str(subject.corpus),
      "platform"  -> Json.str(subject.platform),
      "reference" -> Json.str(reference.checker),
      "subject"   -> Json.str(subject.checker),
      "agrees"     -> Json.bool(agrees),
      "comparable" -> Json.bool(comparable),
      "referenceVerdict" -> Json.str(referenceVerdict.label),
      "referenceDetail"  -> referenceVerdict.detail.fold("null")(Json.str),
      "subjectVerdict"   -> Json.str(subjectVerdict.label),
      "subjectDetail"    -> subjectVerdict.detail.fold("null")(Json.str),
      "referenceWallNanos" -> Json.num(reference.wallNanos),
      "subjectWallNanos"   -> Json.num(subject.wallNanos)
    )

  def render: String =
    val sb = new StringBuilder
    sb ++= s"${subject.toolchain} / ${subject.corpus} / ${subject.platform}: "
    sb ++= (
      if agrees then "agrees"
      else if referenceUnavailable then s"NO REFERENCE VERDICT from ${reference.checker}"
      else "DISAGREES"
    )
    sb ++= s" (${reference.checker} ${referenceVerdict.label} vs ${subject.checker} ${subjectVerdict.label})\n"
    if !agrees then
      referenceVerdict.detail.foreach(d => sb ++= s"  ${reference.checker}: $d\n")
      subjectVerdict.detail.foreach(d => sb ++= s"  ${subject.checker}: $d\n")
    sb.result()
