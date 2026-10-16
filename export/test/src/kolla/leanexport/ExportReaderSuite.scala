package kolla.leanexport

import kolla.kernel.*
import Fixtures.*

class ExportReaderSuite extends munit.FunSuite:

  import ExportFormat.*

  private def read(s: String, f: Option[ExportFormat] = None): ExportEnv =
    ExportReader.fromString(s, f)

  // ----------------------------------------------------------- format detection

  test("format detection") {
    assertEquals(read(textV1Literal).format, TextV1)
    assertEquals(read(textV2Literal).format, TextV2)
    assertEquals(read(ndjson310Literal).format, Ndjson("3.1.0"))
    assertEquals(read(ndjson300Literal).format, Ndjson("3.0.0"))
  }

  test("meta header") {
    val m = read(ndjson310Literal).meta.get
    assertEquals(m.exporterName, "lean4export")
    assertEquals(m.exporterVersion, "3.1.0")
    assertEquals(m.leanVersion, "4.35.0")
    assertEquals(m.leanGithash, "abc")
    assertEquals(read(textV2Literal).meta, None)
  }

  test("the ndjson version comes from meta.format.version, not the exporter version") {
    val src =
      """{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.0.0"},"lean":{"githash":"g","version":"4.27.0"}}}
        |{"in":1,"str":{"pre":0,"str":"A"}}
        |{"ie":0,"sort":0}
        |{"axiom":[{"name":1,"levelParams":[],"type":0,"isUnsafe":false}]}""".stripMargin
    val env = read(src)
    assertEquals(env.format, Ndjson("3.0.0"))
    assertEquals(env.meta.map(_.exporterVersion), Some("3.1.0"))
    assertEquals(env.meta.map(_.formatVersion), Some("3.0.0"))
    // 3.0.0 wraps declarations in arrays; reading it as 3.1.0 would have failed.
    assertEquals(env.infos.map(_.name.toString), Vector("A"))
  }

  test("the exporter version is the fallback when meta.format is absent") {
    val src =
      """{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"}}}
        |{"in":1,"str":{"pre":0,"str":"A"}}
        |{"ie":0,"sort":0}
        |{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}""".stripMargin
    assertEquals(read(src).format, Ndjson("3.1.0"))
  }

  test("a #DEF with a hint token forces v2, without one forces v1") {
    assertEquals(read("1 #NS 0 A\n0 #EC 1\n#DEF 1 0 0 R 3").format, TextV2)
    assertEquals(read("1 #NS 0 A\n0 #EC 1\n#DEF 1 0 0").format, TextV1)
    assertEquals(read("1 #NS 0 A\n2 #NS 0 u\n0 #EC 1\n#DEF 1 0 0 2").format, TextV1)
  }

  test("a bare #QUOT forces v1, an annotated one forces v2") {
    assertEquals(read("1 #NS 0 A\n0 #EC 1\n#QUOT").format, TextV1)
    assertEquals(read("1 #NS 0 Quot\n0 #EC 1\n#QUOT 1 0").format, TextV2)
  }

  test("#RR forces v2") {
    assertEquals(read("1 #NS 0 A\n0 #EC 1\n0 #RR 1 0 0").format, TextV2)
  }

  test("declarations seen before the version is known are replayed in order") {
    val src =
      """1 #NS 0 A
        |2 #NS 0 B
        |0 #EC 1
        |#AX 1 0
        |#AX 2 0
        |#DEF 1 0 0 A""".stripMargin
    val env = read(src)
    assertEquals(env.format, TextV2)
    assertEquals(env.items.flatMap(_.names).map(_.toString), Vector("A", "B", "A"))
  }

  test("an export with only version-ambiguous declarations resolves") {
    val src = "1 #NS 0 A\n0 #ES 0\n#AX 1 0"
    assertEquals(read(src).items.length, 1)
    val onlyInd = "1 #NS 0 A\n0 #ES 0\n#IND 0 1 0 0"
    val env = read(onlyInd)
    assertEquals(env.items.length, 1)
  }

  test("mixed text versions are rejected") {
    val e = intercept[ExportException](read("1 #NS 0 A\n0 #EC 1\n#DEF 1 0 0 A\n#QUOT"))
    assert(clue(e.getMessage).contains("mixed text export formats"))
  }

  // ------------------------------------------------------------------ text v1

  test("text v1 literal") {
    val env = read(textV1Literal)
    assertEquals(env.format, TextV1)
    assertEquals(env.items.length, 4)
    env.items(0) match
      case ExportItem.Info(ConstantInfo.AxiomInfo(a)) =>
        assertEquals(a.toConstantVal.name, Name.parse("Nat"))
        assertEquals(a.toConstantVal.tpe, Expr.Const(Name.parse("Nat"), Nil))
        assertEquals(a.toConstantVal.levelParams, Nil)
      case other => fail(s"expected an axiom, got $other")
    env.items(1) match
      case ExportItem.DefnWithoutHints(n, lp, t, v) =>
        assertEquals(n, Name.parse("Nat.add"))
        assertEquals(lp, Nil)
        assertEquals(
          t,
          Expr.ForallE(Name.mkSimple("x"), Expr.Const(Name.parse("Nat"), Nil), Expr.BVar(0), BinderInfo.Default)
        )
        assertEquals(v, Expr.BVar(0))
      case other => fail(s"expected a hint-less definition, got $other")
    assertEquals(env.items(2), ExportItem.Decl(Declaration.QuotDecl))
    env.items(3) match
      case ExportItem.Decl(Declaration.InductDecl(lp, np, types, unsafe)) =>
        assertEquals(lp, Nil)
        assertEquals(np, 0)
        assertEquals(types.length, 1)
        assertEquals(types.head.name, Name.parse("Nat"))
        assertEquals(types.head.tpe, Expr.Sort(Level.one))
        assertEquals(types.head.ctors.map(_.name.toString), List("Nat.zero"))
        assertEquals(types.head.ctors.map(_.tpe), List(Expr.Const(Name.parse("Nat"), Nil)))
        assert(!unsafe)
      case other => fail(s"expected an inductive declaration, got $other")
  }

  test("text v1 #EC tolerates the exporter's trailing space") {
    val env = read("1 #NS 0 Nat\n0 #EC 1 \n#AX 1 0")
    assertEquals(env.infos.head.tpe, Expr.Const(Name.parse("Nat"), Nil))
  }

  // ------------------------------------------------------------------ text v2

  test("text v2 literal") {
    val env = read(textV2Literal)
    assertEquals(env.format, TextV2)
    val byName = env.infos.map(i => i.name.toString -> i).toMap
    assertEquals(env.infos.length, 9)

    byName("Nat") match
      case ConstantInfo.InductInfo(iv) =>
        assertEquals(iv.numParams, 0)
        assertEquals(iv.numIndices, 0)
        assertEquals(iv.numNested, 0)
        assert(iv.isRec)
        assert(!iv.isReflexive)
        assertEquals(iv.all.map(_.toString), List("Nat"))
        assertEquals(iv.ctors.map(_.toString), List("Nat.zero", "Nat.succ"))
        assertEquals(iv.toConstantVal.levelParams, Nil)
      case other => fail(s"expected an inductive, got $other")

    byName("Nat.succ") match
      case ConstantInfo.CtorInfo(cv) =>
        assertEquals(cv.induct, Name.parse("Nat"))
        assertEquals(cv.cidx, 1)
        assertEquals(cv.numFields, 1)
        assertEquals(
          cv.toConstantVal.tpe,
          Expr.ForallE(Name.mkSimple("n"), Expr.Const(Name.parse("Nat"), Nil), Expr.Const(Name.parse("Nat"), Nil), BinderInfo.Default)
        )
      case other => fail(s"expected a constructor, got $other")

    assertEquals(byName("Nat.add").hints, ReducibilityHints.Regular(3))
    assert(byName("thm1").isTheorem)
    assert(byName("opq").isOpaque)
    assert(byName("ax").isAxiom)

    byName("Nat.rec") match
      case ConstantInfo.RecInfo(rv) =>
        assertEquals(rv.all.map(_.toString), List("Nat"))
        assertEquals(rv.numMotives, 1)
        assertEquals(rv.numMinors, 2)
        assert(!rv.k)
        assertEquals(rv.rules.length, 2)
        assertEquals(rv.rules.map(_.ctor.toString), List("Nat.zero", "Nat.succ"))
        assertEquals(rv.rules.map(_.nfields), List(0, 1))
        assertEquals(rv.rules.map(_.rhs), List(Expr.BVar(0), Expr.BVar(0)))
        assertEquals(rv.toConstantVal.levelParams.map(_.toString), List("u"))
      case other => fail(s"expected a recursor, got $other")

    assert(byName.contains("Quot"))
    byName("Quot") match
      case ConstantInfo.QuotInfo(q) => assertEquals(q.kind, QuotKind.Type)
      case other                    => fail(s"expected a quotient, got $other")
  }

  test("text v2 reducibility hints") {
    def hintOf(h: String): ReducibilityHints =
      read(s"1 #NS 0 A\n0 #ES 0\n#DEF 1 0 0 $h").infos.head.hints
    assertEquals(hintOf("O"), ReducibilityHints.Opaque)
    assertEquals(hintOf("A"), ReducibilityHints.Abbrev)
    assertEquals(hintOf("R 12"), ReducibilityHints.Regular(12))
    intercept[ExportException](hintOf("X"))
  }

  test("text v2 quotient kinds come from the name") {
    def kindOf(n: String): QuotKind =
      read(s"1 #NS 0 Quot\n2 #NS 1 ${n}\n0 #ES 0\n#QUOT ${if n.isEmpty then 1 else 2} 0")
        .infos.head.asInstanceOf[ConstantInfo.QuotInfo].value.kind
    assertEquals(kindOf(""), QuotKind.Type)
    assertEquals(kindOf("mk"), QuotKind.Ctor)
    assertEquals(kindOf("lift"), QuotKind.Lift)
    assertEquals(kindOf("ind"), QuotKind.Ind)
    intercept[ExportException](kindOf("nope"))
  }

  // ------------------------------------------------------------------- ndjson

  test("ndjson 3.1.0 literal") {
    val env = read(ndjson310Literal)
    assertEquals(env.items.length, 5)
    val natName = Name.parse("Nat")
    val d = env.infos(1).asInstanceOf[ConstantInfo.DefnInfo].value
    assertEquals(d.toConstantVal.name, natName.num(7))
    assertEquals(d.hints, ReducibilityHints.Regular(4))
    assertEquals(d.safety, DefinitionSafety.Safe)
    val o = env.infos(3).asInstanceOf[ConstantInfo.OpaqueInfo].value
    assert(o.isUnsafe)
    val q = env.infos(4).asInstanceOf[ConstantInfo.QuotInfo].value
    assertEquals(q.kind, QuotKind.Lift)
  }

  test("ndjson expression constructors") {
    val env = read(ndjson310Literal)
    val d = env.infos(1).asInstanceOf[ConstantInfo.DefnInfo].value
    assertEquals(
      d.value,
      Expr.App(Expr.Const(Name.parse("Nat"), Nil), Expr.natLit(BigInt("123456789012345678901234567890")))
    )
    val a = env.infos(0).asInstanceOf[ConstantInfo.AxiomInfo].value
    assertEquals(a.toConstantVal.tpe, Expr.Sort(Level.Max(Level.Param(u), Level.Succ(Level.Param(u)))))
  }

  test("ndjson 3.0.0 array wrappers and legacy inductive keys") {
    val env = read(ndjson300Literal)
    assertEquals(env.format, Ndjson("3.0.0"))
    assertEquals(env.items.length, 6)
    assertEquals(env.infos.map(_.name.toString), Vector("Nat", "Nat.zero", "Nat.succ", "Nat.rec", "u", "u"))
    env.infos(3) match
      case ConstantInfo.RecInfo(r) => assertEquals(r.rules.length, 2)
      case other                   => fail(s"expected a recursor, got $other")
    assertEquals(env.infos(4).hints, ReducibilityHints.Abbrev)
  }

  test("ndjson natVal accepts an integer as well as a string") {
    val src =
      """{"meta":{"exporter":{"name":"x","version":"3.1.0"},"format":{"version":"3.1.0"}}}
        |{"in":1,"str":{"pre":0,"str":"A"}}
        |{"ie":0,"natVal":5}
        |{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}""".stripMargin
    assertEquals(read(src).infos.head.tpe, Expr.natLit(5))
  }

  test("ndjson mdata keeps the inner expression and drops the payload") {
    val src =
      """{"meta":{"exporter":{"name":"x","version":"3.1.0"},"format":{"version":"3.1.0"}}}
        |{"in":1,"str":{"pre":0,"str":"A"}}
        |{"ie":0,"const":{"name":1,"us":[]}}
        |{"ie":1,"mdata":{"expr":0,"data":{"pp":true}}}
        |{"axiom":{"name":1,"levelParams":[],"type":1,"isUnsafe":false}}""".stripMargin
    val t = read(src).infos.head.tpe
    assertEquals(t, Expr.MData(KVMap.empty, Expr.Const(Name.parse("A"), Nil)): Expr)
    assertEquals(Expr.consumeMData(t), Expr.Const(Name.parse("A"), Nil))
  }

  // ------------------------------------------------------------------- errors

  test("errors carry the line number") {
    val e = intercept[ExportException](read("1 #NS 0 A\n0 #EC 1\n7 #NOPE 1"))
    assertEquals(e.lineNumber, 3)
    assert(clue(e.getMessage).contains("unknown indexed command '#NOPE'"))
  }

  test("dangling indices are reported") {
    val e = intercept[ExportException](read("1 #NS 0 A\n0 #EA 5 6"))
    assert(clue(e.getMessage).contains("expr not found: 5"))
    val e2 = intercept[ExportException](read("1 #NS 9 A"))
    assert(clue(e2.getMessage).contains("name not found: 9"))
  }

  test("truncated lines are reported") {
    intercept[ExportException](read("1 #NS 0 A\n0 #EA 0"))
    intercept[ExportException](read("1 #NS 0 A\n0 #EL #BD 1 0"))
    intercept[ExportException](read("1 #NS 0 A\n0 #EL #XX 1 0 0"))
  }

  test("a #NS with no name component is an error, an empty one is not") {
    val e = intercept[ExportException](read("1 #NS 0"))
    assert(clue(e.getMessage).contains("missing name component"))
    intercept[ExportException](read("1 #NI 0"))
    val env = read("1 #NS 0 \n0 #EC 1\n#AX 1 0")
    assertEquals(env.infos.head.name, Name.anonymous.str(""))
  }

  test("an index beyond the number of lines read is rejected") {
    val e = intercept[ExportException](read("1 #NS 0 A\n268435455 #EV 0"))
    assert(clue(e.getMessage).contains("expr index out of range: 268435455"))
    val e2 = intercept[ExportException](read("1000 #NS 0 A"))
    assert(clue(e2.getMessage).contains("name index out of range: 1000"))
    // Dense, sequential indices are unaffected.
    val dense = (1 to 400).map(i => s"$i #NS 0 n$i").mkString("\n")
    assertEquals(read(dense + "\n0 #EC 400\n#AX 400 0").infos.head.name.toString, "n400")
  }

  test("unknown ndjson items are reported") {
    val e = intercept[ExportException](read("{\"meta\":{}}\n{\"wat\":1}"))
    assert(clue(e.getMessage).contains("unknown export object"))
  }

  // -------------------------------------------------------------- streaming

  test("the fs2 pipe yields the same items") {
    val got = fs2.Stream
      .emits(ndjson310Literal.linesIterator.toVector)
      .through(ExportReader.pipe[fs2.Pure]())
      .compile
      .toVector
    assertEquals(got, read(ndjson310Literal).items)
  }

  test("the fs2 pipe yields the same items for the text formats") {
    List(textV1Literal, textV2Literal).foreach { src =>
      val got = fs2.Stream
        .emits(src.linesIterator.toVector)
        .through(ExportReader.pipe[fs2.Pure]())
        .compile
        .toVector
      assertEquals(got, read(src).items)
    }
  }

  test("blank lines and trailing carriage returns are ignored") {
    val env = read("1 #NS 0 Nat\r\n\r\n0 #EC 1\r\n#AX 1 0\r\n")
    assertEquals(env.infos.length, 1)
  }
