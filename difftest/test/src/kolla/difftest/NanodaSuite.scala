package kolla.difftest

import kolla.leanexport.ExportFormat
import java.nio.file.Paths

class NanodaSuite extends munit.FunSuite:

  test("nanoda reads only NDJSON 3.1.x") {
    // `check_semver` in nanoda's src/parser.rs: 3.1.0 <= v < 3.2.0.
    assert(Nanoda.supports(ExportFormat.Ndjson("3.1.0")))
    assert(Nanoda.supports(ExportFormat.Ndjson("3.1.4")))
    assert(!Nanoda.supports(ExportFormat.Ndjson("3.0.0")))
    assert(!Nanoda.supports(ExportFormat.Ndjson("3.2.0")))
    assert(!Nanoda.supports(ExportFormat.TextV1))
    assert(!Nanoda.supports(ExportFormat.TextV2))
  }

  test("nanoda is a reference only for the newest profile") {
    import kolla.kernel.KernelProfile
    val fmt = ExportFormat.Ndjson("3.1.0")
    // It looks up String.ofList unconditionally, which does not exist before
    // v4.27, and it implements the v4.35 behaviours unconditionally.
    assert(Nanoda.applies(Toolchain("leanprover/lean4:v4.35.0"), fmt))
    assert(!Nanoda.applies(Toolchain("leanprover/lean4:v4.28.0"), fmt))
    assert(!Nanoda.applies(Toolchain("leanprover/lean4:v4.25.0"), fmt))
    assert(!Nanoda.applies(Toolchain("leanprover/lean4:v4.35.0"), ExportFormat.TextV2))
    assertEquals(Toolchain("leanprover/lean4:v4.35.0").profile, KernelProfile.v4_35)
  }

  test("nanoda is the reference for the toolchain lean4checker has none for") {
    val ts = Toolchains.parse(Layout.readFile(Layout.toolchainsFile))
    val fmt = ExportFormat.Ndjson("3.1.0")
    // Every toolchain has at least one reference: lean4checker, or nanoda.
    ts.foreach(t => assert(t.hasReference || Nanoda.applies(t, fmt), clue(t.spec)))
  }

  test("the config names the file, the axioms and both kernel extensions") {
    val cfg = Nanoda.config(Paths.get("/tmp/x.export"))
    assert(clue(cfg).contains("\"export_file_path\":\"/tmp/x.export\""))
    assert(cfg.contains("\"use_stdin\":false"))
    assert(cfg.contains("\"nat_extension\":true"))
    assert(cfg.contains("\"string_extension\":true"))
    // A file declares axioms nothing uses, such as sorryAx; those are skipped.
    assert(cfg.contains("\"unpermitted_axiom_hard_error\":false"))
    Nanoda.permittedAxioms.foreach(a => assert(cfg.contains(s"\"$a\""), clue(a)))
    // The verdict is the exit code, so the pretty-printer report is off.
    assert(cfg.contains("\"print_success_message\":false"))
  }

  test("a run with no binary or an unreadable format fails rather than agreeing") {
    import cats.effect.unsafe.implicits.global
    val t = Toolchain("leanprover/lean4:v4.35.0")
    val c = Corpus.library("init", "Init")
    val noBin =
      Nanoda.run(None, t, c, ExportFormat.Ndjson("3.1.0"), Paths.get("/tmp/x.export")).unsafeRunSync()
    assertEquals(noBin.failure, Some("nanoda was not built"))
    assertEquals(noBin.overall.label, "error")

    val oldFormat =
      Nanoda.run(Some(Paths.get("/bin/true")), t, c, ExportFormat.TextV2, Paths.get("/tmp/x.export"))
        .unsafeRunSync()
    assert(oldFormat.failure.exists(_.contains("does not read")), clue(oldFormat.failure))
    assertEquals(oldFormat.overall.label, "error")

    val oldKernel = Nanoda
      .run(Some(Paths.get("/bin/true")), Toolchain("leanprover/lean4:v4.25.0"), c,
        ExportFormat.Ndjson("3.1.0"), Paths.get("/tmp/x.export"))
      .unsafeRunSync()
    assert(oldKernel.failure.exists(_.contains("does not implement")), clue(oldKernel.failure))
  }

  test("a nanoda run is corpus-level, not per declaration") {
    import cats.effect.unsafe.implicits.global
    val r = Nanoda
      .run(None, Toolchain("leanprover/lean4:v4.35.0"), Corpus.init,
        ExportFormat.Ndjson("3.1.0"), Paths.get("/tmp/x.export"))
      .unsafeRunSync()
    assert(!r.perDeclaration)
    assertEquals(r.checker, "nanoda")
  }
