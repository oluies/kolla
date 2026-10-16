package kolla.leanexport

import scala.annotation.tailrec
import scala.collection.mutable

enum Json:
  case Null
  case Bool(value: Boolean)
  case Num(value: BigInt)
  case Real(value: Double)
  case Str(value: String)
  case Arr(values: Vector[Json])
  case Obj(fields: Map[String, Json])

  def kindName: String = this match
    case Null    => "null"
    case _: Bool => "boolean"
    case _: Num  => "integer"
    case _: Real => "number"
    case _: Str  => "string"
    case _: Arr  => "array"
    case _: Obj  => "object"

object Json:

  val maxDepth: Int = 64

  def parse(input: String): Json =
    val p = new Parser(input)
    val v = p.value(0)
    p.skipWs()
    if !p.atEnd then p.fail("trailing input")
    v

  final class Parser(private val s: String):
    private var i = 0

    def atEnd: Boolean = i >= s.length

    def fail(msg: String): Nothing =
      throw ExportException(s"json: $msg at offset $i")

    def skipWs(): Unit =
      while i < s.length && (s.charAt(i) match
            case ' ' | '\t' | '\n' | '\r' => true
            case _                        => false
          )
      do i += 1

    private def expect(c: Char): Unit =
      if i >= s.length || s.charAt(i) != c then fail(s"expected '$c'")
      i += 1

    private def literal(word: String, v: Json): Json =
      if !s.startsWith(word, i) then fail(s"expected '$word'")
      i += word.length
      v

    def value(depth: Int): Json =
      if depth > maxDepth then fail("nesting too deep")
      skipWs()
      if atEnd then fail("unexpected end of input")
      s.charAt(i) match
        case '{'                   => obj(depth)
        case '['                   => arr(depth)
        case '"'                   => Str(string())
        case 't'                   => literal("true", Bool(true))
        case 'f'                   => literal("false", Bool(false))
        case 'n'                   => literal("null", Null)
        case c if c == '-' || (c >= '0' && c <= '9') => number()
        case c                     => fail(s"unexpected character '$c'")

    private def obj(depth: Int): Json =
      expect('{')
      val b = mutable.LinkedHashMap.empty[String, Json]
      skipWs()
      if i < s.length && s.charAt(i) == '}' then { i += 1; return Obj(Map.empty) }
      var done = false
      while !done do
        skipWs()
        val k = string()
        skipWs()
        expect(':')
        b(k) = value(depth + 1)
        skipWs()
        if i >= s.length then fail("unterminated object")
        s.charAt(i) match
          case ',' => i += 1
          case '}' => i += 1; done = true
          case c   => fail(s"unexpected character '$c' in object")
      Obj(b.toMap)

    private def arr(depth: Int): Json =
      expect('[')
      val b = Vector.newBuilder[Json]
      skipWs()
      if i < s.length && s.charAt(i) == ']' then { i += 1; return Arr(Vector.empty) }
      var done = false
      while !done do
        b += value(depth + 1)
        skipWs()
        if i >= s.length then fail("unterminated array")
        s.charAt(i) match
          case ',' => i += 1
          case ']' => i += 1; done = true
          case c   => fail(s"unexpected character '$c' in array")
      Arr(b.result())

    private def string(): String =
      expect('"')
      val start = i
      var plain = true
      while i < s.length && s.charAt(i) != '"' do
        if s.charAt(i) == '\\' then { plain = false; i += 2 } else i += 1
      if i >= s.length then fail("unterminated string")
      val end = i
      i += 1
      if plain then s.substring(start, end) else unescape(s.substring(start, end))

    private def unescape(raw: String): String =
      val sb = new StringBuilder(raw.length)
      var j = 0
      while j < raw.length do
        val c = raw.charAt(j)
        if c != '\\' then { sb += c; j += 1 }
        else
          if j + 1 >= raw.length then fail("dangling escape")
          raw.charAt(j + 1) match
            case '"'  => sb += '"'; j += 2
            case '\\' => sb += '\\'; j += 2
            case '/'  => sb += '/'; j += 2
            case 'b'  => sb += '\b'; j += 2
            case 'f'  => sb += '\f'; j += 2
            case 'n'  => sb += '\n'; j += 2
            case 'r'  => sb += '\r'; j += 2
            case 't'  => sb += '\t'; j += 2
            case 'u' =>
              if j + 6 > raw.length then fail("truncated \\u escape")
              val h = raw.substring(j + 2, j + 6)
              val cp =
                try Integer.parseInt(h, 16)
                catch case _: NumberFormatException => fail(s"bad \\u escape '$h'")
              sb += cp.toChar
              j += 6
            case other => fail(s"bad escape '\\$other'")
      sb.result()

    private def number(): Json =
      val start = i
      if i < s.length && s.charAt(i) == '-' then i += 1
      while i < s.length && s.charAt(i).isDigit do i += 1
      var integral = true
      if i < s.length && s.charAt(i) == '.' then
        integral = false
        i += 1
        while i < s.length && s.charAt(i).isDigit do i += 1
      if i < s.length && (s.charAt(i) == 'e' || s.charAt(i) == 'E') then
        integral = false
        i += 1
        if i < s.length && (s.charAt(i) == '+' || s.charAt(i) == '-') then i += 1
        while i < s.length && s.charAt(i).isDigit do i += 1
      val text = s.substring(start, i)
      if text.isEmpty || text == "-" then fail("bad number")
      if integral then Num(BigInt(text)) else Real(text.toDouble)

  extension (j: Json)

    def asObj(what: String): Map[String, Json] = j match
      case Obj(f) => f
      case _      => throw ExportException(s"$what: expected object, got ${j.kindName}")

    def asArr(what: String): Vector[Json] = j match
      case Arr(v) => v
      case _      => throw ExportException(s"$what: expected array, got ${j.kindName}")

    def asStr(what: String): String = j match
      case Str(v) => v
      case _      => throw ExportException(s"$what: expected string, got ${j.kindName}")

    def asBigInt(what: String): BigInt = j match
      case Num(v) => v
      case _      => throw ExportException(s"$what: expected integer, got ${j.kindName}")

    def asInt(what: String): Int =
      val v = j.asBigInt(what)
      if !v.isValidInt then throw ExportException(s"$what: integer out of range: $v")
      v.toInt

    def asBool(what: String): Boolean = j match
      case Bool(v) => v
      case _       => throw ExportException(s"$what: expected boolean, got ${j.kindName}")

  extension (fields: Map[String, Json])

    def req(key: String, what: String): Json =
      fields.getOrElse(key, throw ExportException(s"$what: missing field '$key'"))

    def opt(key: String): Option[Json] = fields.get(key)
