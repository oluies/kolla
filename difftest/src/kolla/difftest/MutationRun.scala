package kolla.difftest

import cats.effect.IO
import kolla.kernel.KernelProfile
import kolla.leanexport.ExportItem

/** One mutant's outcome: whether kolla rejected it, and whether it should have. */
final case class MutationOutcome(
    mutation: Mutation,
    toolchain: String,
    corpus: String,
    run: CheckerRun
):
  /** `ChangeDefinitionalHeight` only steers unfolding order, so a mutant of that
    * kind must still be accepted; every other kind must be rejected.
    */
  def expectedRejection: Boolean = mutation.kind != MutationKind.ChangeDefinitionalHeight

  def rejected: Boolean = run.rejected > 0

  def asExpected: Boolean = rejected == expectedRejection && run.failure.isEmpty

  /** The declaration kolla rejected, when it did. */
  def rejectedName: Option[String] =
    run.results.collectFirst { case DeclResult(n, _: Verdict.Rejected, _, _) => n.toString }

  def json: String =
    Json.obj(
      "kind"        -> Json.str(mutation.kind.slug),
      "seed"        -> Json.num(mutation.seed),
      "target"      -> Json.str(mutation.target.toString),
      "description" -> Json.str(mutation.description),
      "toolchain"   -> Json.str(toolchain),
      "corpus"      -> Json.str(corpus),
      "expectedRejection" -> Json.bool(expectedRejection),
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
    * with rejections it did not cause.
    */
  def run(
      base: Vector[ExportItem],
      profile: KernelProfile,
      toolchain: String,
      corpus: String,
      seeds: List[Long]
  ): IO[Vector[MutationOutcome]] =
    val mutations = seeds.flatMap(s => Mutate.generate(s, base))
    mutations.foldLeft(IO.pure(Vector.empty[MutationOutcome])) { (acc, m) =>
      acc.flatMap { done =>
        KollaChecker
          .check(m.items, profile, toolchain, s"$corpus/${m.id}", "jvm")
          .map(r => done :+ MutationOutcome(m, toolchain, corpus, r))
      }
    }
