package kolla.kernel

class KernelProfileSuite extends munit.FunSuite:

  test("the pinned profiles record the differences between releases") {
    assertEquals(KernelProfile.v4_25.stringLiteralCtor, Name.parse("String.mk"))
    assertEquals(KernelProfile.v4_27.stringLiteralCtor, Name.parse("String.ofList"))
    assertEquals(KernelProfile.v4_35.stringLiteralCtor, Name.parse("String.ofList"))

    assert(!KernelProfile.v4_25.propByNormalization)
    assert(!KernelProfile.v4_27.propByNormalization)
    assert(KernelProfile.v4_35.propByNormalization)

    assertEquals(KernelProfile.v4_25.natMaxSizeBytes, None)
    assertEquals(KernelProfile.v4_27.natMaxSizeBytes, None)
    assertEquals(KernelProfile.v4_35.natMaxSizeBytes, Some(128L * 1024 * 1024))

    List(KernelProfile.v4_25, KernelProfile.v4_27).foreach { p =>
      assert(!p.checkUniformIndOccs, clue(p.label))
      assert(!p.checkRecursors, clue(p.label))
      assert(!p.etaStructRequiresNonRec, clue(p.label))
      assert(!p.boundedProjIdx, clue(p.label))
      assert(!p.cacheDefEqSuccess, clue(p.label))
    }
    assert(KernelProfile.v4_35.checkUniformIndOccs)
    assert(KernelProfile.v4_35.checkRecursors)
    assert(KernelProfile.v4_35.etaStructRequiresNonRec)
    assert(KernelProfile.v4_35.boundedProjIdx)
    assert(KernelProfile.v4_35.cacheDefEqSuccess)
  }

  test("unbounded nat size is representable") {
    assertEquals(KernelProfile.v4_25.natMaxSize, Long.MaxValue)
    assertEquals(KernelProfile.v4_35.natMaxSize, 128L * 1024 * 1024)
  }

  test("toolchain specs resolve to the nearest profile at or below") {
    def p(s: String) = KernelProfile.forToolchain(s).label
    assertEquals(p("leanprover/lean4:v4.35.0"), "v4.35.0")
    assertEquals(p("leanprover/lean4:v4.36.0"), "v4.35.0")
    assertEquals(p("leanprover/lean4:v4.40.0-rc1"), "v4.35.0")
    assertEquals(p("leanprover/lean4:v4.27.0"), "v4.27.0")
    assertEquals(p("leanprover/lean4:v4.28.0"), "v4.27.0")
    assertEquals(p("leanprover/lean4:v4.34.0"), "v4.27.0")
    assertEquals(p("leanprover/lean4:v4.25.0"), "v4.25.0")
    assertEquals(p("leanprover/lean4:v4.12.0"), "v4.25.0")
    assertEquals(p("v4.35.0"), "v4.35.0")
    assertEquals(p("4.35.0"), "v4.35.0")
    assertEquals(p("nightly-2026-01-01"), KernelProfile.default.label)
  }

  test("every pinned profile is reachable from its own label") {
    // Falsifiable: adding a profile to `all` without extending `forToolchain`
    // makes it resolve to a neighbour instead of itself.
    KernelProfile.all.foreach { p =>
      assertEquals(KernelProfile.forToolchain(s"leanprover/lean4:${p.label}"), p, clue(p.label))
    }
    assertEquals(KernelProfile.all.map(_.label).distinct.length, KernelProfile.all.length)
  }
