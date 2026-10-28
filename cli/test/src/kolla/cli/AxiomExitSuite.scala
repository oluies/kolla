package kolla.cli

import cats.effect.ExitCode
import kolla.kernel.{Axioms, Name}

class AxiomExitSuite extends munit.FunSuite:

  def closure(axioms: String*): Axioms.Closure =
    Axioms.Closure(Name.parse("Thm"), axioms.toVector.map(Name.parse), axioms.length + 1)

  val trustBase = closure("Classical.choice", "Quot.sound", "propext")

  test("nothing unusual is exit 0") {
    assertEquals(Main.axiomExit(List(closure(), trustBase), unknown = false), ExitCode.Success)
  }

  test("a sorry is exit 1") {
    assertEquals(Main.axiomExit(List(trustBase, closure("sorryAx")), unknown = false), ExitCode(1))
  }

  test("an axiom outside the trust base is exit 1") {
    assertEquals(Main.axiomExit(List(closure("cheat")), unknown = false), ExitCode(1))
  }

  test("an unknown name alone is exit 2") {
    assertEquals(Main.axiomExit(List(trustBase), unknown = true), ExitCode(2))
    assertEquals(Main.axiomExit(Nil, unknown = true), ExitCode(2))
  }

  test("a named set replaces the default judgement, and an empty one permits nothing") {
    def ps(xs: String*): Option[Set[Name]] = Some(xs.map(Name.parse).toSet)
    // The trust base is only unremarkable by default; a caller may say otherwise.
    assertEquals(Main.axiomExit(List(trustBase), unknown = false,
                                ps("propext", "Classical.choice", "Quot.sound")), ExitCode.Success)
    assertEquals(Main.axiomExit(List(trustBase), unknown = false, ps("propext")), ExitCode(1))
    assertEquals(Main.axiomExit(List(closure()), unknown = false, Some(Set.empty[Name])), ExitCode.Success)
    assertEquals(Main.axiomExit(List(trustBase), unknown = false, Some(Set.empty[Name])), ExitCode(1))
    // sorryAx is outside any set that does not name it.
    assertEquals(Main.axiomExit(List(closure("sorryAx")), unknown = false,
                                ps("propext")), ExitCode(1))
    // And a set that does name it is the caller's business.
    assertEquals(Main.axiomExit(List(closure("sorryAx")), unknown = false,
                                ps("sorryAx")), ExitCode.Success)
  }

  test("a verdict outranks an unknown name") {
    assertEquals(Main.axiomExit(List(closure("sorryAx")), unknown = true), ExitCode(1))
    assertEquals(Main.axiomExit(List(closure("cheat")), unknown = true), ExitCode(1))
  }
