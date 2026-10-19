package kolla.cli

import kolla.kernel.KernelProfile

class OptionsSuite extends munit.FunSuite:

  def ok(args: String*): Options = Options.parse(args.toList).fold(m => fail(m), identity)
  def err(args: String*): String = Options.parse(args.toList).swap.fold(o => fail(s"expected an error, got $o"), identity)

  test("a file is required unless help or version was asked for") {
    assert(err().contains("no export file given"))
    assert(ok("--help").help)
    assert(ok("--version").version)
    assertEquals(ok("a.export").files, List("a.export"))
  }

  test("several files accumulate in order") {
    assertEquals(ok("a", "b", "c").files, List("a", "b", "c"))
  }

  test("a dash is a file, not an option") {
    assertEquals(ok("-").files, List("-"))
  }

  test("the default profile is the newest") {
    assertEquals(ok("a").profile, KernelProfile.v4_35)
    assertEquals(KernelProfile.all.last, KernelProfile.v4_35)
  }

  test("a profile is accepted with or without the v") {
    assertEquals(ok("--profile", "v4.25.0", "a").profile, KernelProfile.v4_25)
    assertEquals(ok("--profile", "4.27.0", "a").profile, KernelProfile.v4_27)
    assert(err("--profile", "v9.9.9", "a").contains("unknown profile"))
    // The error lists what is on offer, so the user does not have to guess.
    KernelProfile.all.foreach(p => assert(err("--profile", "nope", "a").contains(p.label), clue(p.label)))
  }

  test("the output flags are off by default and settable") {
    val d = ok("a")
    assert(!d.json && !d.verbose && !d.quiet && !d.abortOnReject)
    val o = ok("--json", "--abort", "a")
    assert(o.json && o.abortOnReject)
    assert(ok("-v", "a").verbose)
    assert(ok("-q", "a").quiet)
  }

  test("quiet and verbose contradict each other") {
    assert(err("-q", "-v", "a").contains("mutually exclusive"))
  }

  test("--only accumulates") {
    assertEquals(ok("--only", "Nat", "--only", "Nat.succ", "a").only, List("Nat", "Nat.succ"))
  }

  test("an unknown option is an error that shows the usage") {
    val m = err("--wat", "a")
    assert(m.contains("--wat"))
    assert(m.contains("kolla [options]"))
  }

  test("--profiles is a listing, not a run and not an error") {
    val o = ok("--profiles")
    assert(o.listProfiles)
    assert(o.files.isEmpty, clue(o.files))
    KernelProfile.all.foreach(p => assert(Options.profiles.contains(p.label), clue(p.label)))
  }

  test("a listing takes precedence over a missing file") {
    // `--profiles`, `--help` and `--version` all answer without a file.
    List("--profiles", "--help", "--version").foreach(f => Options.parse(List(f)).fold(m => fail(s"$f: $m"), identity))
  }

  test("the usage names every exit code the tool returns") {
    List("0", "1", "2").foreach(c => assert(Options.usage.contains(c), clue(c)))
  }

  test("the defeq-cache advice fires only where it is needed") {
    val small = Options.libraryScaleBytes - 1
    val large = Options.libraryScaleBytes

    // An uncached profile at library scale: advise.
    val warned = Options.defeqCacheAdvice(Options(profile = KernelProfile.v4_27), large)
    assert(warned.isDefined)
    assert(warned.get.contains("--defeq-cache"), clue(warned))
    assert(warned.get.contains(KernelProfile.v4_27.label), clue(warned))

    // Below library scale, nothing to say.
    assertEquals(Options.defeqCacheAdvice(Options(profile = KernelProfile.v4_27), small), None)

    // Already asked for it.
    assertEquals(
      Options.defeqCacheAdvice(Options(profile = KernelProfile.v4_27, defeqCache = true), large),
      None
    )

    // A profile that keeps the cache anyway.
    assertEquals(Options.defeqCacheAdvice(Options(profile = KernelProfile.v4_35), large), None)
  }

  test("every profile without the cache is covered by the advice") {
    // Derived from the profiles rather than naming v4_25 and v4_27, so a
    // profile added later is covered the day it is added.
    for p <- KernelProfile.all do
      val advice = Options.defeqCacheAdvice(Options(profile = p), Options.libraryScaleBytes)
      assertEquals(advice.isDefined, !p.cacheDefEqSuccess, clue(p.label))
  }

  test("the threshold sits between the largest fixture and the smallest library") {
    // 17 MB is the largest committed fixture and `init` is 292 MB; the point of
    // the threshold is to separate them, so assert that rather than the number.
    assert(Options.libraryScaleBytes > 17L * 1024 * 1024, clue(Options.libraryScaleBytes))
    assert(Options.libraryScaleBytes < 292L * 1024 * 1024, clue(Options.libraryScaleBytes))
  }

  test("--defeq-cache parses and reaches the profile") {
    assert(!ok("a").defeqCache)
    assert(ok("--defeq-cache", "a").defeqCache)
    assertEquals(Options.profileOf(ok("a")).label, KernelProfile.default.label)
    assertEquals(
      Options.profileOf(ok("--profile", "4.27.0", "--defeq-cache", "a")).label,
      "v4.27.0+defeq-cache"
    )
    assert(Options.profileOf(ok("--profile", "4.27.0", "--defeq-cache", "a")).cacheDefEqSuccess)
    assert(!Options.profileOf(ok("--profile", "4.27.0", "a")).cacheDefEqSuccess)
  }

  test("the amended profile keeps the release it is of") {
    // What a `--cache` digest is keyed on, so the flag must not change it.
    val plain   = Options.profileOf(ok("--profile", "4.27.0", "a"))
    val amended = Options.profileOf(ok("--profile", "4.27.0", "--defeq-cache", "a"))
    assertNotEquals(amended.label, plain.label)
    assertEquals(amended.release, plain.release)
  }

  test("--eval takes a term and exactly one file") {
    assertEquals(ok("--eval", "Nat.add 2 3", "a").evalTerm, Some("Nat.add 2 3"))
    assertEquals(ok("a").evalTerm, None)
    // With no file at all the earlier, more specific check fires first.
    assert(err("--eval", "t").contains("no export file given"))
    assert(err("--eval", "t", "a", "b").contains("exactly one export file"))
  }

  test("--eval rejects the flags it would otherwise ignore") {
    // Silently ignoring them is what this guards against: --eval checks
    // nothing, so neither a cache nor a selector has anything to do.
    assert(err("--eval", "t", "--cache", "c.txt", "a").contains("mutually exclusive"))
    assert(err("--eval", "t", "--check", "Nat", "a").contains("mutually exclusive"))
    // but it composes with the ones that do apply
    assert(ok("--eval", "t", "--progress", "a").progress)
    assert(ok("--eval", "t", "--json", "a").json)
    assertEquals(
      Options.profileOf(ok("--eval", "t", "--profile", "4.27.0", "--defeq-cache", "a")).label,
      "v4.27.0+defeq-cache"
    )
  }

  test("--trace parses and composes") {
    assert(!ok("a").trace)
    assert(ok("--trace", "a").trace)
    assert(ok("--trace", "--progress", "a").trace)
  }
