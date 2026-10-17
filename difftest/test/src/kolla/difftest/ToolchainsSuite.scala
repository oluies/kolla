package kolla.difftest

import kolla.kernel.KernelProfile

class ToolchainsSuite extends munit.FunSuite:

  test("comments and blank lines are ignored") {
    val src =
      """# a comment
        |
        |leanprover/lean4:v4.25.0
        |   leanprover/lean4:v4.27.0
        |# another
        |leanprover/lean4:v4.35.0
        |""".stripMargin
    val ts = Toolchains.parse(src)
    assertEquals(ts.map(_.spec), List(
      "leanprover/lean4:v4.25.0", "leanprover/lean4:v4.27.0", "leanprover/lean4:v4.35.0"
    ))
  }

  test("the no-reference flag is parsed and rendered") {
    val ts = Toolchains.parse(
      """leanprover/lean4:v4.28.0
        |leanprover/lean4:v4.35.0 no-reference
        |""".stripMargin
    )
    assertEquals(ts.map(_.hasReference), List(true, false))
    assertEquals(
      Toolchains.render(ts),
      "leanprover/lean4:v4.28.0\nleanprover/lean4:v4.35.0 no-reference"
    )
  }

  test("the committed file declares v4.35.0 as having no reference checker") {
    val ts = Toolchains.parse(Layout.readFile(Layout.toolchainsFile))
    // lean4checker's newest tag is v4.29.0-rc8 and a tool revision must pin
    // exactly the target toolchain to compile against it.
    assertEquals(ts.filter(!_.hasReference).map(_.version), List("v4.35.0"))
    assert(ts.exists(t => t.hasReference && t.version == "v4.28.0"))
  }

  test("version, slug and profile") {
    val t = Toolchain("leanprover/lean4:v4.35.0")
    assertEquals(t.version, "v4.35.0")
    assertEquals(t.slug, "leanprover-lean4-v4.35.0")
    assertEquals(t.profile, KernelProfile.v4_35)
    assertEquals(Toolchain("leanprover/lean4:v4.25.0").profile, KernelProfile.v4_25)
    assertEquals(Toolchain("leanprover/lean4:v4.27.0").profile, KernelProfile.v4_27)
  }

  test("every toolchain in the committed file resolves to the newest profile at or below it") {
    val ts = Toolchains.parse(Layout.readFile(Layout.toolchainsFile))
    assert(ts.nonEmpty)
    // This is the consistency check the kernel module cannot run, since it
    // cross-compiles and cannot read the file. See the note in K1. A toolchain
    // need not have a profile of its own: v4.28.0 shares v4.27.0's, because
    // nothing in the K1 matrix changed between them.
    def parts(v: String): List[Int] =
      v.stripPrefix("v").split('.').toList.flatMap(_.takeWhile(_.isDigit).toIntOption)
    def atOrBelow(a: String, b: String): Boolean =
      parts(a).zipAll(parts(b), 0, 0).collectFirst { case (x, y) if x != y => x < y }.getOrElse(true)
    ts.foreach { t =>
      val resolved = KernelProfile.forToolchain(t.spec)
      assert(atOrBelow(resolved.label, t.version), clue(s"${t.spec} resolved to ${resolved.label}"))
      val newer = KernelProfile.all.filter(p => atOrBelow(p.label, t.version))
      assertEquals(
        resolved.label,
        newer.map(_.label).reduce((a, b) => if atOrBelow(a, b) then b else a),
        clue(s"${t.spec} did not resolve to the newest applicable profile")
      )
    }
    // Every pinned profile is exercised by at least one toolchain.
    val labels = ts.map(t => KernelProfile.forToolchain(t.spec).label).distinct
    assertEquals(labels.sorted, KernelProfile.all.map(_.label).sorted)
  }

  test("a slug is safe as a directory name") {
    Toolchains.parse("leanprover/lean4:v4.35.0\nleanprover/lean4:nightly-2026-01-01")
      .foreach(t => assert(!t.slug.exists(c => c == '/' || c == ':'), clue(t.slug)))
  }

  test("the layout resolves against the repository root") {
    assert(java.nio.file.Files.exists(Layout.repoRoot.resolve("build.mill")))
    assert(java.nio.file.Files.exists(Layout.toolchainsFile), clue(Layout.toolchainsFile.toString))
    assert(java.nio.file.Files.isDirectory(Layout.casesDir), clue(Layout.casesDir.toString))
    assertEquals(
      Layout.exportFile(Toolchain("leanprover/lean4:v4.35.0"), "Init").getFileName.toString,
      "Init.export"
    )
    assert(Layout.toolchainCache(Toolchain("leanprover/lean4:v4.35.0")).toString
      .endsWith(".difftest/leanprover-lean4-v4.35.0"))
  }
