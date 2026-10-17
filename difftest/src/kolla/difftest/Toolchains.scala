package kolla.difftest

import kolla.kernel.KernelProfile

/** One Lean release the platform runs against. */
final case class Toolchain(spec: String):
  /** The version part, for example `v4.35.0`. */
  def version: String = spec.substring(spec.lastIndexOf(':') + 1)

  /** A filesystem-safe directory name. */
  def slug: String = spec.replace('/', '-').replace(':', '-')

  def profile: KernelProfile = KernelProfile.forToolchain(spec)

object Toolchains:

  /** Reads `difftest/toolchains.txt`. Blank lines and `#` comments are ignored. */
  def parse(contents: String): List[Toolchain] =
    contents.linesIterator
      .map(_.trim)
      .filter(l => l.nonEmpty && !l.startsWith("#"))
      .map(Toolchain(_))
      .toList

  def render(ts: List[Toolchain]): String = ts.map(_.spec).mkString("\n")
