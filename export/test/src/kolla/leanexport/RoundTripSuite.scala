package kolla.leanexport

import kolla.kernel.*
import Fixtures.*

class RoundTripSuite extends munit.FunSuite:

  import ExportFormat.*

  private def roundTrip(env: ExportEnv, fmt: ExportFormat): ExportEnv =
    val text1 = ExportWriter.toString(env, fmt)
    val env2  = ExportReader.fromString(text1)
    assertEquals(env2.format, fmt, clues(text1))
    assertEquals(env2.items, env.items, clues(text1))
    val text2 = ExportWriter.toString(env2, fmt)
    assertEquals(text2, text1)
    env2

  test("text v2 round-trips every item kind") {
    roundTrip(richEnv, TextV2)
  }

  test("ndjson 3.1.0 round-trips every item kind") {
    roundTrip(richEnv, Ndjson("3.1.0"))
  }

  test("ndjson 3.0.0 round-trips every item kind") {
    roundTrip(richEnv, Ndjson("3.0.0"))
  }

  test("text v1 round-trips the item kinds it can carry") {
    roundTrip(v1Env, TextV1)
  }

  test("the hand-written files round-trip") {
    List(
      textV1Literal   -> TextV1,
      textV2Literal   -> TextV2,
      ndjson310Literal -> Ndjson("3.1.0"),
      ndjson300Literal -> Ndjson("3.0.0")
    ).foreach { (src, fmt) =>
      val env = ExportReader.fromString(src)
      assertEquals(env.format, fmt)
      roundTrip(env, fmt)
    }
  }

  test("ndjson preserves the meta header") {
    val env  = ExportReader.fromString(ndjson310Literal)
    val back = ExportReader.fromString(ExportWriter.toString(env, Ndjson("3.1.0")))
    assertEquals(back.meta, env.meta)
  }

  test("string literals survive the hex encoding") {
    val strings = List("", "a", "héllo wörld", "αβγ", "emoji 😀", "tab\there", "quote\"x", "back\\slash")
    strings.foreach { s =>
      val n = Name.parse("S")
      val env = ExportEnv(TextV2, None, Vector(ExportItem.Info(ConstantInfo.AxiomInfo(
        AxiomVal(ConstantVal(n, Nil, Expr.strLit(s)), false)
      ))))
      assertEquals(roundTrip(env, TextV2).infos.head.tpe, Expr.strLit(s), clue(s))
      assertEquals(roundTrip(env, Ndjson("3.1.0")).infos.head.tpe, Expr.strLit(s), clue(s))
    }
  }

  test("large nat literals survive") {
    val big = BigInt("9" * 80)
    val n = Name.parse("N")
    val env = ExportEnv(TextV2, None, Vector(ExportItem.Info(ConstantInfo.AxiomInfo(
      AxiomVal(ConstantVal(n, Nil, Expr.natLit(big)), false)
    ))))
    assertEquals(roundTrip(env, TextV2).infos.head.tpe, Expr.natLit(big))
    assertEquals(roundTrip(env, Ndjson("3.1.0")).infos.head.tpe, Expr.natLit(big))
  }

  test("numeral name components survive") {
    val n = Name.parse("A").num(BigInt("12345678901234567890")).str("b")
    val env = ExportEnv(TextV2, None, Vector(ExportItem.Info(ConstantInfo.AxiomInfo(
      AxiomVal(ConstantVal(n, Nil, Expr.Sort(Level.zero)), false)
    ))))
    assertEquals(roundTrip(env, TextV2).infos.head.name, n)
    assertEquals(roundTrip(env, Ndjson("3.1.0")).infos.head.name, n)
  }

  test("binder annotations survive") {
    List(BinderInfo.Default, BinderInfo.Implicit, BinderInfo.StrictImplicit, BinderInfo.InstImplicit).foreach { bi =>
      val n = Name.parse("B")
      val e = Expr.Lam(Name.mkSimple("x"), Expr.Sort(Level.zero), Expr.BVar(0), bi)
      val env = ExportEnv(TextV2, None, Vector(ExportItem.Info(ConstantInfo.AxiomInfo(
        AxiomVal(ConstantVal(n, Nil, e), false)
      ))))
      List[ExportFormat](TextV2, TextV1, Ndjson("3.1.0")).foreach { fmt =>
        val back = ExportReader.fromString(ExportWriter.toString(env, fmt))
        assert(Expr.isBiEqual(back.infos.head.tpe, e), clue((fmt, bi)))
      }
    }
  }

  test("deep terms do not overflow the writer or the reader") {
    val depth = 50000
    val body  = (0 until depth).foldLeft(Expr.const("Nat"))((e, _) => Expr.App(e, Expr.BVar(0)))
    val n     = Name.parse("Deep")
    val env = ExportEnv(TextV2, None, Vector(ExportItem.Info(ConstantInfo.AxiomInfo(
      AxiomVal(ConstantVal(n, Nil, body), false)
    ))))
    val back = ExportReader.fromString(ExportWriter.toString(env, TextV2))
    assertEquals(Expr.getAppNumArgs(back.infos.head.tpe), depth)
  }

  test("the writer rejects what a format cannot represent") {
    def envOf(item: ExportItem) = ExportEnv(TextV1, None, Vector(item))
    intercept[ExportException](ExportWriter.toString(envOf(quotItems.head), TextV1))
    intercept[ExportException](ExportWriter.toString(envOf(inductItem), TextV1))
    intercept[ExportException](ExportWriter.toString(envOf(v1Items(1)), TextV2))
    intercept[ExportException](
      ExportWriter.toString(envOf(ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(
        ConstantVal(Name.parse("M"), Nil, Expr.MData(KVMap.empty, Expr.const("Nat"))), false
      )))), TextV2)
    )
    intercept[ExportException](
      ExportWriter.toString(envOf(ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(
        ConstantVal(Name.parse("F"), Nil, Expr.FVar(Name.parse("x"))), false
      )))), TextV2)
    )
    intercept[ExportException](
      ExportWriter.toString(envOf(ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(
        ConstantVal(Name.parse("L"), Nil, Expr.Sort(Level.mvar(Name.parse("m")))), false
      )))), TextV2)
    )
  }

  test("infoEnvironment preserves declaration order") {
    val env = ExportReader.fromString(textV2Literal)
    assertEquals(
      env.infoEnvironment.names.map(_.toString),
      Vector("Nat", "Nat.zero", "Nat.succ", "Nat.rec", "ax", "Nat.add", "thm1", "opq", "Quot")
    )
  }
