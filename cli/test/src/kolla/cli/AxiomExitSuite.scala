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

  test("a verdict outranks an unknown name") {
    assertEquals(Main.axiomExit(List(closure("sorryAx")), unknown = true), ExitCode(1))
    assertEquals(Main.axiomExit(List(closure("cheat")), unknown = true), ExitCode(1))
  }
