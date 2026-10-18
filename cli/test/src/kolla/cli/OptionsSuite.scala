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
