package kolla.difftest

import kolla.kernel.Name

/** What a checker decided about one declaration. */
enum Verdict:
  case Accepted
  case Rejected(reason: String)
  /** The checker did not produce a judgement: a declaration it carries over from
    * the file rather than re-deriving, or one it does not support.
    */
  case NotChecked(reason: String)
  /** The checker crashed or timed out. */
  case Error(reason: String)

  def label: String = this match
    case Accepted      => "accepted"
    case _: Rejected   => "rejected"
    case _: NotChecked => "not-checked"
    case _: Error      => "error"

  def detail: Option[String] = this match
    case Accepted         => None
    case Rejected(r)      => Some(r)
    case NotChecked(r)    => Some(r)
    case Error(r)         => Some(r)

  /** Only `Accepted` and `Rejected` are comparable between checkers. */
  def isJudgement: Boolean = this match
    case Accepted | _: Rejected => true
    case _                      => false

/** One declaration's result from one checker. */
final case class DeclResult(
    name: Name,
    verdict: Verdict,
    nanos: Long,
    trace: List[String] = Nil
):
  def json: String =
    Json.obj(
      "name"    -> Json.str(name.toString),
      "verdict" -> Json.str(verdict.label),
      "detail"  -> verdict.detail.fold("null")(Json.str),
      "nanos"   -> Json.num(nanos),
      "trace"   -> Json.arr(trace.map(Json.str))
    )

/** Everything one checker produced for one corpus under one toolchain. */
final case class CheckerRun(
    checker: String,
    toolchain: String,
    corpus: String,
    platform: String,
    results: Vector[DeclResult],
    wallNanos: Long,
    peakHeapBytes: Long,
    failure: Option[String] = None,
    /** Whether `results` carries a verdict per declaration. `lean4checker`
      * reports one accept/reject for a whole module, so its run is comparable
      * only through `overall`.
      */
    perDeclaration: Boolean = true
):
  def accepted: Int   = results.count(_.verdict == Verdict.Accepted)
  def rejected: Int   = results.count(_.verdict.isInstanceOf[Verdict.Rejected])
  def notChecked: Int = results.count(_.verdict.isInstanceOf[Verdict.NotChecked])
  def errored: Int    = results.count(_.verdict.isInstanceOf[Verdict.Error])

  def byName: Map[Name, DeclResult] = results.map(r => r.name -> r).toMap

  /** Declarations rejected or errored, which a positive corpus must not have. */
  def unexpected: Vector[DeclResult] =
    results.filter(r => r.verdict.isInstanceOf[Verdict.Rejected] || r.verdict.isInstanceOf[Verdict.Error])

  /** The corpus-level decision: rejected if anything was rejected, accepted
    * only if at least one declaration was judged and none were rejected. This
    * is the granularity `lean4checker` reports at.
    */
  def overall: Verdict =
    failure match
      case Some(f) => Verdict.Error(f)
      case None =>
        results.collectFirst { case DeclResult(n, Verdict.Rejected(r), _, _) => Verdict.Rejected(s"$n: $r") } match
          case Some(v) => v
          case None =>
            results.collectFirst { case DeclResult(n, Verdict.Error(r), _, _) => Verdict.Error(s"$n: $r") } match
              case Some(v)                 => v
              case None if accepted > 0    => Verdict.Accepted
              case None                    => Verdict.NotChecked("no declaration was judged")

  def json: String =
    Json.obj(
      "checker"       -> Json.str(checker),
      "toolchain"     -> Json.str(toolchain),
      "corpus"        -> Json.str(corpus),
      "platform"      -> Json.str(platform),
      "wallNanos"     -> Json.num(wallNanos),
      "peakHeapBytes" -> Json.num(peakHeapBytes),
      "failure"       -> failure.fold("null")(Json.str),
      "perDeclaration" -> Json.bool(perDeclaration),
      "overall"        -> Json.str(overall.label),
      "overallDetail"  -> overall.detail.fold("null")(Json.str),
      "counts" -> Json.obj(
        "accepted"   -> Json.num(accepted.toLong),
        "rejected"   -> Json.num(rejected.toLong),
        "notChecked" -> Json.num(notChecked.toLong),
        "errored"    -> Json.num(errored.toLong),
        "total"      -> Json.num(results.length.toLong)
      ),
      "declarations" -> Json.arr(results.map(_.json))
    )
