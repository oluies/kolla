package kolla.kernel

import kolla.kernel.Generators.given
import org.scalacheck.Prop.forAll

class NameSuite extends munit.ScalaCheckSuite:

  test("construction and rendering") {
    assertEquals(Name.parse("Nat.add").toString, "Nat.add")
    assertEquals(Name.anonymous.toString, "[anonymous]")
    assertEquals(Name.mkSimple("Nat").num(3).toString, "Nat.3")
    assertEquals(Name.mkSimple("has space").toString, "«has space»")
    assertEquals(Name("List", "map").toString, "List.map")
  }

  test("structure") {
    val n = Name.parse("A.B.C")
    assertEquals(n.length, 3)
    assertEquals(n.prefix, Name.parse("A.B"))
    assert(!n.isAtomic)
    assert(Name.mkSimple("A").isAtomic)
    assert(Name.anonymous.isAnonymous)
    assertEquals(n.components.map(_.toString), List("A", "B", "C"))
  }

  test("append") {
    assertEquals(Name.parse("A.B").append(Name.parse("C.D")), Name.parse("A.B.C.D"))
    assertEquals(Name.anonymous.append(Name.parse("C")), Name.parse("C"))
  }

  test("numeral and string components are distinct") {
    assertNotEquals(Name.anonymous.str("1"), Name.anonymous.num(1))
    assert(Name.compare(Name.anonymous.num(1), Name.anonymous.str("1")) < 0)
  }

  test("deep names do not overflow the stack") {
    val deep = (0 until 200000).foldLeft(Name.anonymous)((n, i) => n.str("c"))
    assertEquals(deep.length, 200000)
    val deep2 = (0 until 200000).foldLeft(Name.anonymous)((n, i) => n.str("c"))
    assertEquals(deep, deep2)
  }

  property("parse and render round-trip for identifier components") {
    forAll(org.scalacheck.Gen.listOfN(3, org.scalacheck.Gen.oneOf("a", "bc", "Nat", "map"))) { cs =>
      Name.parse(cs.mkString(".")).toString == cs.mkString(".")
    }
  }

  property("equal names have equal hashes") {
    forAll { (a: Name, b: Name) => !(a == b) || a.hashCode == b.hashCode }
  }

  property("compare is a total order") {
    forAll { (a: Name, b: Name) =>
      val c = Name.compare(a, b)
      val d = Name.compare(b, a)
      if a == b then c == 0 && d == 0 else c != 0 && c == -d.sign * math.abs(c)
    }
  }

  property("compare is transitive") {
    forAll { (a: Name, b: Name, c: Name) =>
      val ab = Name.compare(a, b)
      val bc = Name.compare(b, c)
      if ab < 0 && bc < 0 then Name.compare(a, c) < 0
      else if ab > 0 && bc > 0 then Name.compare(a, c) > 0
      else true
    }
  }

  property("components rebuild the name") {
    forAll { (a: Name) => Name.anonymous.append(a) == a }
  }

  test("appendAfter extends the last string component") {
    assertEquals(Name.appendAfter(Name.parse("A.n"), "_ih").toString, "A.n_ih")
    assertEquals(Name.appendAfter(Name.mkSimple("n"), "_ih").toString, "n_ih")
    // A numeral component cannot be extended, so a component is added.
    assertEquals(Name.appendAfter(Name.anonymous.num(3), "_ih").toString, "3._ih")
    assertEquals(Name.appendAfter(Name.anonymous, "u").toString, "u")
  }

  test("appendIndexAfter separates the index with an underscore") {
    assertEquals(Name.appendIndexAfter(Name.mkSimple("u"), 1).toString, "u_1")
    assertEquals(Name.appendIndexAfter(Name.mkSimple("motive"), 2).toString, "motive_2")
    assertEquals(Name.appendIndexAfter(Name.parse("A.b"), 7).toString, "A.b_7")
  }

  test("replacePrefix strips an inductive's namespace") {
    assertEquals(Name.replacePrefix(Name.parse("Nat.succ"), Name.parse("Nat"), Name.anonymous).toString, "succ")
    assertEquals(Name.replacePrefix(Name.parse("A.B.c"), Name.parse("A.B"), Name.anonymous).toString, "c")
    // No match leaves the name alone.
    assertEquals(Name.replacePrefix(Name.parse("Nat.succ"), Name.parse("Int"), Name.anonymous).toString, "Nat.succ")
    assertEquals(Name.replacePrefix(Name.parse("Nat"), Name.parse("Nat"), Name.mkSimple("X")).toString, "X")
  }
