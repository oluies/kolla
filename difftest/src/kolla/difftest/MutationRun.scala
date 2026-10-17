package kolla.difftest

import cats.effect.IO
import kolla.kernel.{KernelProfile, Name}
import kolla.leanexport.ExportItem

/** One mutant's outcome: whether kolla rejected it, and whether it should have.
  *
  * `baselineRejected` names the declarations the unmutated corpus already
  * rejected. A mutant is only credited with a rejection the baseline did not
  * have: otherwise a corpus with a pre-existing failure would make every mutant
  * look like a success, including the one kind that must stay accepted.
  */
final case class MutationOutcome(
    mutation: Mutation,
    toolchain: String,
    corpus: String,
    run: CheckerRun,
    baselineRejected: Set[Name] = Set.empty
):
  /** `ChangeDefinitionalHeight` only steers unfolding order, so a mutant of that
    * kind must still be accepted; every other kind must be rejected.
    */
  def expectedRejection: Boolean = mutation.kind != MutationKind.ChangeDefinitionalHeight

  /** Rejections this mutation caused, as opposed to ones already there. */
  def newRejections: Vector[DeclResult] =
    run.results.filter(r => r.verdict.isInstanceOf[Verdict.Rejected] && !baselineRejected.contains(r.name))

  def rejected: Boolean = newRejections.nonEmpty

  def asExpected: Boolean = rejected == expectedRejection && run.failure.isEmpty

  /** The declaration this mutation made kolla reject, when it did. */
  def rejectedName: Option[String] = newRejections.headOption.map(_.name.toString)

  def json: String =
    Json.obj(
      "kind"        -> Json.str(mutation.kind.slug),
      "seed"        -> Json.num(mutation.seed),
      "target"      -> Json.str(mutation.target.toString),
      "description" -> Json.str(mutation.description),
      "toolchain"   -> Json.str(toolchain),
      "corpus"      -> Json.str(corpus),
      "expectedRejection" -> Json.bool(expectedRejection),
      "baselineRejected"  -> Json.num(baselineRejected.size.toLong),
      "rejected"          -> Json.bool(rejected),
      "asExpected"        -> Json.bool(asExpected),
      "rejectedName"      -> rejectedName.fold("null")(Json.str),
      "failure"           -> run.failure.fold("null")(Json.str)
    )

  def render: String =
    val mark = if asExpected then "ok  " else "BAD "
    val what = if rejected then s"rejected ${rejectedName.getOrElse("?")}" else "accepted"
    s"  $mark ${mutation.id} on ${mutation.target}: $what (expected ${if expectedRejection then "rejection" else "acceptance"})\n"

object MutationRun:

  /** Mutates `base` once per kind and checks each mutant.
    *
    * The mutant is checked to the end rather than stopped at the first
    * rejection, so a mutation that corrupts one declaration is not credited
    * with rejections it did not cause. For the same reason the unmutated corpus
    * is checked first, and only rejections it did not already have count.
    */
  def run(
      base: Vector[ExportItem],
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      seeds: List[Long]
  ): IO[Vector[MutationOutcome]] =
    val mutations = seeds.flatMap(s => Mutate.generate(s, base))
    if mutations.isEmpty then IO.pure(Vector.empty)
    else
      KollaChecker.check(base, profile, toolchain, s"$corpus/baseline", "jvm").flatMap { baseline =>
        val already = baseline.results.collect { case DeclResult(n, _: Verdict.Rejected, _, _) => n }.toSet
        mutations.foldLeft(IO.pure(Vector.empty[MutationOutcome])) { (acc, m) =>
          acc.flatMap { done =>
            KollaChecker
              .check(m.items, profile, toolchain, s"$corpus/${m.id}", "jvm")
              .map(r => done :+ MutationOutcome(m, toolchain, corpus, r, already))
          }
        }
      }
