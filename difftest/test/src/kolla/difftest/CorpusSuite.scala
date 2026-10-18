package kolla.difftest

import java.nio.file.Paths

class CorpusSuite extends munit.FunSuite:

  test("a handwritten case takes its module name from the file name") {
    val c = Corpus.handwritten(Paths.get("difftest/cases/eta.lean"))
    assertEquals(c.name, "case-eta")
    assertEquals(c.modules, List("eta"))
    assertEquals(c.source.map(_.getFileName.toString), Some("eta.lean"))
    assert(c.decls.isEmpty)
    assert(c.project.isEmpty)
  }

  test("a library corpus has no source to compile") {
    assertEquals(Corpus.init.name, "init")
    assertEquals(Corpus.init.modules, List("Init"))
    assert(Corpus.init.source.isEmpty)
  }

  test("every committed case is picked up and compiles to a distinct corpus") {
    val cs = Corpus.cases.unsafeRunHere()
    assert(cs.length >= 10, clue(cs.map(_.name)))
    assertEquals(cs.map(_.name).distinct.length, cs.length)
    assert(cs.forall(_.source.isDefined))
    // The order is stable so a report's rows do not shuffle between runs.
    assertEquals(cs.map(_.name), cs.map(_.name).sorted)
  }

  test("a negative case is named apart and marked") {
    val c = Corpus.handwritten(Paths.get("difftest/cases-negative/addfalse.lean"), expectRejection = true)
    assertEquals(c.name, "bad-addfalse")
    assert(c.expectRejection)
    assert(!Corpus.handwritten(Paths.get("difftest/cases/eta.lean")).expectRejection)
  }

  test("every committed negative case is picked up") {
    val cs = Corpus.negativeCases.unsafeRunHere()
    assert(cs.length >= 3, clue(cs.map(_.name)))
    assert(cs.forall(_.expectRejection))
    assert(cs.forall(_.name.startsWith("bad-")))
    // Nothing is both a positive and a negative corpus.
    val names = Corpus.cases.unsafeRunHere().map(_.name).toSet
    assert(cs.forall(c => !names.contains(c.name)))
  }

  test("a toolchains directive restricts a case, and an absent one does not") {
    val all = Corpus.handwritten(Paths.get("x/a.lean"))
    assert(all.appliesTo(Toolchain("leanprover/lean4:v4.35.0")))

    val some = Corpus.handwritten(
      Paths.get("x/a.lean"),
      expectRejection = true,
      contents = "/- doc -/\n-- toolchains: v4.27.0  v4.28.0\nimport Lean\n"
    )
    assertEquals(some.toolchains, List("v4.27.0", "v4.28.0"))
    assert(some.appliesTo(Toolchain("leanprover/lean4:v4.28.0")))
    assert(!some.appliesTo(Toolchain("leanprover/lean4:v4.35.0")))
  }

  test("every toolchain a committed case names is in the matrix") {
    // A typo here would silently drop the case from every run.
    val known = Toolchains.parse(Layout.readFile(Layout.toolchainsFile)).map(_.version).toSet
    val cs    = Corpus.cases.unsafeRunHere() ++ Corpus.negativeCases.unsafeRunHere()
    cs.foreach(c => c.toolchains.foreach(v => assert(known.contains(v), clue(s"${c.name} names $v"))))
  }

  test("every committed toolchain has at least one negative case or something to mutate") {
    val ts = Toolchains.parse(Layout.readFile(Layout.toolchainsFile))
    val cs = Corpus.cases.unsafeRunHere() ++ Corpus.negativeCases.unsafeRunHere()
    ts.foreach { t =>
      val applicable = cs.filter(_.appliesTo(t))
      assert(
        applicable.exists(_.expectRejection) || applicable.exists(!_.expectRejection),
        clue(s"${t.spec} has no corpus at all")
      )
    }
    // v4.35.0 has no negative case, by P7; its negative coverage is the mutants.
    val v435 = Toolchain("leanprover/lean4:v4.35.0")
    assert(cs.filter(_.appliesTo(v435)).forall(!_.expectRejection))
    assert(cs.exists(c => c.expectRejection && c.appliesTo(Toolchain("leanprover/lean4:v4.28.0"))))
  }

  test("a committed export is a corpus that needs no toolchain") {
    val cs = Corpus.fixtures.unsafeRunHere()
    assert(cs.length >= 4, clue(cs.map(_.name)))
    assert(cs.forall(_.prebuilt.isDefined))
    assert(cs.forall(_.modules.isEmpty))
    assert(cs.forall(!_.expectRejection))
    assert(cs.forall(_.name.startsWith("fixture-")), clue(cs.map(_.name)))
    // The suffix is dropped, not the version in the name.
    assert(cs.exists(_.name == "fixture-nat-add-3.1.0"), clue(cs.map(_.name)))
    // Both NDJSON format versions are present, so the platform comparison
    // covers the 3.0.0 reader as well as the current one.
    assert(cs.exists(_.name.endsWith("3.0.0")), clue(cs.map(_.name)))
    assert(cs.exists(_.name.endsWith("3.1.0")))
  }

  test("a fixture corpus is distinct from a handwritten one") {
    val handwritten = Corpus.cases.unsafeRunHere().map(_.name).toSet
    val fixtures    = Corpus.fixtures.unsafeRunHere().map(_.name).toSet
    assertEquals(handwritten.intersect(fixtures), Set.empty[String])
    assert(Corpus.cases.unsafeRunHere().forall(_.prebuilt.isEmpty))
  }

  test("the mathlib sample names declarations and nothing else") {
    val c = Corpus.mathlibSample(Paths.get("/tmp/mathlib4")).unsafeRunHere()
    assertEquals(c.name, "mathlib-sample")
    assertEquals(c.modules, List("Mathlib"))
    assert(c.decls.nonEmpty)
    assert(c.decls.forall(d => !d.startsWith("#") && d.trim == d), clue(c.decls))
    assertEquals(c.project.map(_.toString), Some("/tmp/mathlib4"))
  }

  extension [A](io: cats.effect.IO[A])
    def unsafeRunHere(): A =
      import cats.effect.unsafe.implicits.global
      io.unsafeRunSync()
