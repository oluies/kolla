package kolla.difftest

import kolla.kernel.KernelProfile

/** One Lean release the platform runs against.
  *
  * `hasReference` records whether `lean4checker` has a release for this
  * toolchain. It is declared rather than discovered: a tool revision must pin
  * exactly the target toolchain to compile against it, so a missing release is
  * a fact about the release, not a transient failure to retry every run.
  */
final case class Toolchain(spec: String, hasReference: Boolean = true):
  /** The version part, for example `v4.35.0`. */
  def version: String = spec.substring(spec.lastIndexOf(':') + 1)

  /** A filesystem-safe directory name. */
  def slug: String = spec.replace('/', '-').replace(':', '-')

  def profile: KernelProfile = KernelProfile.forToolchain(spec)

object Toolchains:

  /** The flag that marks a toolchain `lean4checker` has no release for. */
  val noReferenceFlag = "no-reference"

  /** Reads `difftest/toolchains.txt`. Blank lines and `#` comments are ignored.
    *
    * A line is a toolchain spec, optionally followed by `no-reference`.
    */
  def parse(contents: String): List[Toolchain] =
    contents.linesIterator
      .map(_.trim)
      .filter(l => l.nonEmpty && !l.startsWith("#"))
      .map { l =>
        val fields = l.split("\\s+").toList
        Toolchain(fields.head, hasReference = !fields.tail.contains(noReferenceFlag))
      }
      .toList

  /** The toolchains `names` selects, or the names that match nothing.
    *
    * A name matching nothing is an error rather than an empty selection:
    * every command would otherwise do nothing and report success, which reads
    * as a run that found no disagreement.
    */
  def select(all: List[Toolchain], names: List[String]): Either[List[String], List[Toolchain]] =
    if names.isEmpty then Right(all)
    else
      def matches(t: Toolchain, s: String) = t.spec == s || t.version == s
      val unmatched = names.filterNot(s => all.exists(t => matches(t, s)))
      if unmatched.nonEmpty then Left(unmatched)
      else Right(all.filter(t => names.exists(s => matches(t, s))))

  def render(ts: List[Toolchain]): String =
    ts.map(t => if t.hasReference then t.spec else s"${t.spec} $noReferenceFlag").mkString("\n")
