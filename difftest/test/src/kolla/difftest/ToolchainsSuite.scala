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

  test("version, slug and profile") {
    val t = Toolchain("leanprover/lean4:v4.35.0")
    assertEquals(t.version, "v4.35.0")
    assertEquals(t.slug, "leanprover-lean4-v4.35.0")
    assertEquals(t.profile, KernelProfile.v4_35)
    assertEquals(Toolchain("leanprover/lean4:v4.25.0").profile, KernelProfile.v4_25)
    assertEquals(Toolchain("leanprover/lean4:v4.27.0").profile, KernelProfile.v4_27)
  }

  test("every toolchain in the committed file resolves to a pinned profile") {
    val ts = Toolchains.parse(Layout.readFile(Layout.toolchainsFile))
    assert(ts.nonEmpty)
    // This is the consistency check the kernel module cannot run, since it
    // cross-compiles and cannot read the file. See the note in K1.
    ts.foreach { t =>
      assertEquals(
        KernelProfile.forToolchain(t.spec).label,
        t.version,
        clue(s"${t.spec} has no pinned profile of its own")
      )
    }
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
