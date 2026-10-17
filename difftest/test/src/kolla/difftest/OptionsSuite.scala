package kolla.difftest

class OptionsSuite extends munit.FunSuite:

  def ok(args: String*): Options = Options.parse(args.toList).fold(m => fail(m), identity)

  test("the default is a full run of every toolchain and corpus") {
    val o = ok()
    assertEquals(o.command, "run")
    assertEquals(o.toolchains, Nil)
    assertEquals(o.corpora, Nil)
    assertEquals(o.seeds, List(1L))
    assert(o.withChecker)
    assert(o.withMutants)
    assert(!o.writeHistory)
  }

  test("repeated restrictions accumulate") {
    val o = ok("export", "--toolchain", "v4.27.0", "--toolchain", "v4.35.0", "--corpus", "case-eta")
    assertEquals(o.command, "export")
    assertEquals(o.toolchains, List("v4.27.0", "v4.35.0"))
    assertEquals(o.corpora, List("case-eta"))
  }

  test("an explicit seed replaces the default rather than adding to it") {
    assertEquals(ok("--seed", "7").seeds, List(7L))
    assertEquals(ok("--seed", "7", "--seed", "8").seeds, List(7L, 8L))
  }

  test("a non-numeric seed is an error") {
    assert(Options.parse(List("--seed", "x")).isLeft)
  }

  test("flags turn the optional stages off") {
    val o = ok("--no-checker", "--no-mutants", "--history")
    assert(!o.withChecker)
    assert(!o.withMutants)
    assert(o.writeHistory)
  }

  test("an unknown option is an error and help is not a command") {
    assert(Options.parse(List("--wat")).isLeft)
    assertEquals(Options.parse(List("--help")), Left(Options.usage))
  }

  test("a mathlib checkout is a path") {
    assertEquals(ok("--mathlib", "/tmp/mathlib4").mathlib.map(_.toString), Some("/tmp/mathlib4"))
  }
