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

  test("macro scopes are recognised") {
    // <name>._@.<imported>.<ctx>._hyg.<scopes>
    val hyg = Name.parse("a._@._internal._hyg").num(0)
    assert(Name.hasMacroScopes(hyg))
    assert(!Name.hasMacroScopes(Name.parse("a.b")))
    assert(!Name.hasMacroScopes(Name.parse("a._hyg.b")))
    assert(Name.hasMacroScopes(Name.parse("a._@.M._hyg").num(3).num(4)))
    assertEquals(Name.eraseMacroScopes(hyg), Name.mkSimple("a"))
    assertEquals(Name.eraseMacroScopes(Name.parse("x.y._@.M._hyg").num(1)), Name.parse("x.y"))
    assertEquals(Name.eraseMacroScopes(Name.parse("a.b")), Name.parse("a.b"))
  }

  test("appendAfter lands on the unhygienic base") {
    // Lean's modifyBase applies the suffix to the base and re-attaches the
    // scopes, so the suffix must not end up after `._hyg.<scopes>`.
    val hyg = Name.parse("n._@._internal._hyg").num(0)
    assertEquals(Name.appendAfter(hyg, "_ih"), Name.parse("n_ih._@._internal._hyg").num(0))
    assertEquals(
      Name.appendIndexAfter(Name.parse("motive._@.M._hyg").num(2), 1),
      Name.parse("motive_1._@.M._hyg").num(2)
    )
    // A plain name is unaffected.
    assertEquals(Name.appendAfter(Name.mkSimple("n"), "_ih").toString, "n_ih")
  }

  test("parse inverts toString") {
    // The wire format between kolla's platforms is `Name.toString`, so a name
    // that does not survive the round trip is a name two platforms disagree
    // about. See docs/semantics.md N4.
    val names = List(
      Name.parse("Nat"),
      Name.parse("Nat.rec"),
      Name.anonymous.str("_private").str("Init").str("Core").num(0).str("Lean").str("injEq_helper"),
      Name.anonymous.str("n").str("_@").str("Init").str("Prelude").num(4011339995L).str("_hyg").num(8),
      Name.anonymous.str("a b"),
      Name.anonymous.str("0"),
      Name.anonymous.str("").str("x"),
      Name.anonymous.num(0),
      Name.anonymous.num(BigInt("123456789012345678901234567890")),
      Name.anonymous.str("has.dot"),
      Name.anonymous.str("«odd»")
    )
    names.foreach(n => assertEquals(Name.parse(n.toString), n, clue(n.toString)))
  }

  test("a numeric component is a Num, not a string of digits") {
    assertEquals(Name.parse("a.0"), Name.anonymous.str("a").num(0))
    assertNotEquals(Name.parse("a.0"), Name.anonymous.str("a").str("0"))
    // A string of digits still renders escaped, which is what tells them apart.
    assertEquals(Name.anonymous.str("a").str("0").toString, "a.«0»")
    assertEquals(Name.anonymous.str("a").num(0).toString, "a.0")
  }

  test("a component that only starts with a digit is a string") {
    assertEquals(Name.parse("a.0b"), Name.anonymous.str("a").str("0b"))
  }

  test("a dot inside guillemets does not split a component") {
    val n = Name.anonymous.str("a.b").str("c")
    assertEquals(n.toString, "«a.b».c")
    assertEquals(Name.parse(n.toString), n)
    assertEquals(Name.parse(n.toString).components.length, 2)
  }
