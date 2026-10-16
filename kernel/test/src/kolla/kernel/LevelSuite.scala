package kolla.kernel

import kolla.kernel.Generators.given
import org.scalacheck.Prop.forAll

class LevelSuite extends munit.ScalaCheckSuite:

  val u = Level.param("u")
  val v = Level.param("v")

  test("explicit levels") {
    assert(Level.zero.isExplicit)
    assert(Level.ofNat(5).isExplicit)
    assertEquals(Level.ofNat(5).depth, 5)
    assertEquals(Level.toExplicit(Level.ofNat(5)), 5)
    assert(!u.isExplicit)
    assert(!Level.Max(Level.zero, Level.zero).isExplicit)
  }

  test("toOffset") {
    assertEquals(Level.toOffset(Level.succN(u, 3)), (u, 3))
    assertEquals(Level.toOffset(Level.zero), (Level.zero, 0))
  }

  test("max smart constructor") {
    assertEquals(Level.max(u, u), u)
    assertEquals(Level.max(u, Level.zero), u)
    assertEquals(Level.max(Level.zero, u), u)
    assertEquals(Level.max(Level.ofNat(2), Level.ofNat(5)), Level.ofNat(5))
    assertEquals(Level.max(Level.succN(u, 2), Level.succN(u, 1)), Level.succN(u, 2))
    assertEquals(Level.max(u, Level.Max(u, v)), Level.Max(u, v))
  }

  test("imax smart constructor") {
    assertEquals(Level.imax(u, Level.zero), Level.zero)
    assertEquals(Level.imax(Level.zero, u), u)
    assertEquals(Level.imax(Level.one, u), u)
    assertEquals(Level.imax(u, u), u)
    assertEquals(Level.imax(u, Level.succ(v)), Level.max(u, Level.succ(v)))
    assertEquals(Level.imax(u, v), Level.IMax(u, v): Level)
  }

  test("normalize flattens and dedups max") {
    assertEquals(Level.normalize(Level.Max(u, u)), u)
    assertEquals(
      Level.normalize(Level.Max(Level.Max(u, v), u)),
      Level.normalize(Level.Max(u, v))
    )
    assertEquals(Level.normalize(Level.Max(Level.ofNat(1), Level.succ(u))), Level.succ(u))
    assertEquals(Level.normalize(Level.Max(Level.ofNat(3), Level.succ(u))), Level.Max(Level.ofNat(3), Level.succ(u)))
  }

  test("isEquiv on reassociated max") {
    val a = Level.Max(Level.Max(u, v), Level.param("w"))
    val b = Level.Max(u, Level.Max(v, Level.param("w")))
    assert(Level.isEquiv(a, b))
  }

  test("normalize is not idempotent across imax: src/kernel/level.cpp normalize") {
    val l = Level.IMax(Level.succ(u), Level.one)
    assertEquals(Level.normalize(l), Level.Max(Level.succ(u), Level.one): Level)
    assertEquals(Level.normalize(Level.normalize(l)), Level.succ(u))
  }

  test("geq is a conservative approximation across imax") {
    assert(!Level.geq(Level.succ(Level.IMax(u, v)), Level.IMax(u, v)))
  }

  test("geq basics") {
    assert(Level.geq(u, Level.zero))
    assert(Level.geq(Level.succ(u), u))
    assert(!Level.geq(u, Level.succ(u)))
    assert(Level.geq(Level.Max(u, v), u))
    assert(Level.geq(Level.Max(u, v), v))
    assert(!Level.geq(u, Level.Max(u, v)))
  }

  test("instantiate") {
    assertEquals(Level.instantiate(u, List(Name.mkSimple("u")), List(Level.ofNat(3))), Level.ofNat(3))
    assertEquals(Level.instantiate(Level.succ(u), List(Name.mkSimple("u")), List(Level.zero)), Level.one)
    assertEquals(Level.instantiate(v, List(Name.mkSimple("u")), List(Level.zero)), v)
    assertEquals(
      Level.instantiate(Level.IMax(u, v), List(Name.mkSimple("v")), List(Level.zero)),
      Level.zero
    )
  }

  test("undefinedParam") {
    assertEquals(Level.undefinedParam(Level.Max(u, v), List(Name.mkSimple("u"))), Some(Name.mkSimple("v")))
    assertEquals(Level.undefinedParam(Level.Max(u, v), List(Name.mkSimple("u"), Name.mkSimple("v"))), None)
  }

  test("flags") {
    assert(u.hasParam)
    assert(!u.hasMVar)
    assert(Level.mvar(Name.mkSimple("m")).hasMVar)
    assert(Level.Max(u, Level.mvar(Name.mkSimple("m"))).hasParam)
    assert(Level.Max(u, Level.mvar(Name.mkSimple("m"))).hasMVar)
  }

  test("deep levels do not overflow the stack") {
    val deep = (0 until 200000).foldLeft(u: Level)((l, _) => Level.Succ(l))
    assertEquals(Level.toOffset(deep)._2, 200000)
    assertEquals(Level.normalize(deep), deep)
    assert(Level.geq(Level.Succ(deep), deep))
    val nested = (0 until 100000).foldLeft(u: Level)((l, _) => Level.Max(l, v))
    assert(Level.isEquiv(nested, Level.Max(u, v)))
  }

  property("normalize is idempotent on imax-free levels") {
    forAll { (n: Generators.NoIMax) =>
      Level.normalize(Level.normalize(n.level)) == Level.normalize(n.level)
    }
  }

  property("isEquiv is reflexive") {
    forAll { (l: Level) => Level.isEquiv(l, l) }
  }

  property("isEquiv agrees with normalize on imax-free levels") {
    forAll { (n: Generators.NoIMax) => Level.isEquiv(n.level, Level.normalize(n.level)) }
  }

  property("isEquiv is symmetric") {
    forAll { (a: Level, b: Level) => Level.isEquiv(a, b) == Level.isEquiv(b, a) }
  }

  property("geq is reflexive and zero is least") {
    forAll { (l: Level) => Level.geq(l, l) && Level.geq(l, Level.zero) }
  }

  property("max is commutative and idempotent up to equivalence") {
    forAll { (a: Level, b: Level) =>
      Level.isEquiv(Level.max(a, b), Level.max(b, a)) && Level.max(a, a) == a
    }
  }

  property("max is associative up to equivalence") {
    forAll { (a: Level, b: Level, c: Level) =>
      Level.isEquiv(Level.max(Level.max(a, b), c), Level.max(a, Level.max(b, c)))
    }
  }

  property("max dominates its arguments on imax-free levels") {
    forAll { (a: Generators.NoIMax, b: Generators.NoIMax) =>
      Level.geq(Level.max(a.level, b.level), a.level) &&
        Level.geq(Level.max(a.level, b.level), b.level)
    }
  }

  property("imax with a successor right argument is max") {
    forAll { (a: Level, b: Level) =>
      Level.imax(a, Level.succ(b)) == Level.max(a, Level.succ(b))
    }
  }

  property("imax with zero right argument is zero") {
    forAll { (a: Level) => Level.imax(a, Level.zero) == Level.zero }
  }

  property("succ dominates on imax-free levels") {
    forAll { (n: Generators.NoIMax) => Level.geq(Level.succ(n.level), n.level) }
  }

  property("identity substitution preserves equivalence on imax-free levels") {
    forAll { (n: Generators.NoIMax) =>
      val ps = Generators.paramNames.toList
      Level.isEquiv(Level.instantiate(n.level, ps, Level.paramsToLevels(ps)), n.level)
    }
  }

  property("instantiating every parameter removes hasParam") {
    forAll { (l: Level) =>
      val ps = Generators.paramNames.toList
      !Level.instantiate(l, ps, ps.map(_ => Level.zero)).hasParam
    }
  }

  property("equal levels have equal hashes") {
    forAll { (a: Level, b: Level) => !(a == b) || a.hashCode == b.hashCode }
  }

  property("normalize preserves equivalence classes on imax-free levels") {
    forAll { (a: Generators.NoIMax, b: Generators.NoIMax) =>
      Level.isEquiv(a.level, b.level) ==
        Level.isEquiv(Level.normalize(a.level), Level.normalize(b.level))
    }
  }

  property("depth of succ") {
    forAll { (l: Level) => Level.Succ(l).depth == l.depth + 1 }
  }

  property("isNormLt is a strict total order on distinct levels") {
    forAll { (a: Level, b: Level) =>
      if a == b then !Level.isNormLt(a, b) && !Level.isNormLt(b, a)
      else Level.isNormLt(a, b) != Level.isNormLt(b, a)
    }
  }
