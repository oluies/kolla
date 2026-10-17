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
