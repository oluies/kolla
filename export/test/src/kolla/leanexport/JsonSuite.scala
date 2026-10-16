package kolla.leanexport

import Json.*

class JsonSuite extends munit.FunSuite:

  test("scalars") {
    assertEquals(Json.parse("null"), Json.Null)
    assertEquals(Json.parse("true"), Json.Bool(true))
    assertEquals(Json.parse("false"), Json.Bool(false))
    assertEquals(Json.parse("0"), Json.Num(BigInt(0)))
    assertEquals(Json.parse("-17"), Json.Num(BigInt(-17)))
    assertEquals(Json.parse("1.5"), Json.Real(1.5))
    assertEquals(Json.parse("2e3"), Json.Real(2000.0))
    assertEquals(Json.parse("\"hi\""), Json.Str("hi"))
  }

  test("big integers are exact") {
    val big = "123456789012345678901234567890"
    assertEquals(Json.parse(big), Json.Num(BigInt(big)))
  }

  test("string escapes") {
    assertEquals(Json.parse(""""a\"b"""").asStr("s"), "a\"b")
    assertEquals(Json.parse(""""a\\b"""").asStr("s"), "a\\b")
    assertEquals(Json.parse(""""\n\r\t\b\f\/"""").asStr("s"), "\n\r\t\b\f/")
    assertEquals(Json.parse(""""é"""").asStr("s"), "é")
    assertEquals(Json.parse("\"αβγ\"").asStr("s"), "αβγ")
  }

  test("objects and arrays") {
    assertEquals(Json.parse("{}"), Json.Obj(Map.empty))
    assertEquals(Json.parse("[]"), Json.Arr(Vector.empty))
    val j = Json.parse("""{"a":1,"b":[2,3],"c":{"d":null}}""")
    val f = j.asObj("root")
    assertEquals(f.req("a", "root").asInt("a"), 1)
    assertEquals(f.req("b", "root").asArr("b").map(_.asInt("b")), Vector(2, 3))
    assertEquals(f.req("c", "root").asObj("c").req("d", "c"), Json.Null)
  }

  test("whitespace is skipped") {
    assertEquals(Json.parse("  { \"a\" : [ 1 , 2 ] } ").asObj("r").req("a", "r").asArr("a").length, 2)
  }

  test("accessors report the actual kind") {
    val e = intercept[ExportException](Json.parse("1").asStr("thing"))
    assert(clue(e.getMessage).contains("thing: expected string, got integer"))
    intercept[ExportException](Json.parse("\"x\"").asInt("n"))
    intercept[ExportException](Json.parse("1e400").asBigInt("n"))
    intercept[ExportException](Json.parse("99999999999").asInt("n"))
  }

  test("malformed input is rejected") {
    List("", "{", "[1,", "{\"a\"}", "{\"a\":}", "nul", "\"abc", "1 2", "{\"a\":1,}", "[1,]")
      .foreach(s => intercept[ExportException](Json.parse(s)))
  }

  test("nesting is bounded") {
    val deep = "[" * (Json.maxDepth + 5) + "]" * (Json.maxDepth + 5)
    val e = intercept[ExportException](Json.parse(deep))
    assert(clue(e.getMessage).contains("nesting too deep"))
  }

  test("missing fields are reported") {
    val e = intercept[ExportException](Json.parse("{}").asObj("x").req("k", "x"))
    assert(clue(e.getMessage).contains("x: missing field 'k'"))
  }
