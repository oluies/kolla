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

  test("a single binder's annotation survives") {
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

  // The exporter's own expression table is keyed on `BEq Expr`, which is
  // `Expr.eqv` (`expr_eq_fn<false>`) and ignores binder names and annotations,
  // so lean4export assigns one index to binder nodes that differ only there and
  // the file records the first occurrence's annotation. The writer matches that.
  test("binder-blind deduplication matches lean4export") {
    val nat      = Expr.const("Nat")
    val explicitB = Expr.ForallE(Name.mkSimple("a"), nat, nat, BinderInfo.Default)
    val implicitB = Expr.ForallE(Name.mkSimple("b"), nat, nat, BinderInfo.Implicit)
    assertEquals(explicitB, implicitB)
    assert(!Expr.isBiEqual(explicitB, implicitB))

    val env = ExportEnv(TextV2, None, Vector(
      ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("E"), Nil, explicitB), false))),
      ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("I"), Nil, implicitB), false)))
    ))
    val lines = ExportWriter.toLines(env, TextV2)
    assertEquals(lines.count(_.contains("#EP")), 1)
    val back = ExportReader.fromString(lines.mkString("\n"))
    assert(Expr.isBiEqual(back.infos(0).tpe, explicitB))
    assert(Expr.isBiEqual(back.infos(1).tpe, explicitB))
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

  test("the text formats reject what they cannot represent without loss") {
    def envOf(item: ExportItem) = ExportEnv(TextV2, None, Vector(item))
    val n  = Name.parse("U")
    val cv = ConstantVal(n, Nil, Expr.const("Nat"))

    val unsafeAxiom = ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(cv, true)))
    val unsafeDefn = ExportItem.Info(ConstantInfo.DefnInfo(DefinitionVal(
      cv, Expr.const("Nat"), ReducibilityHints.Abbrev, DefinitionSafety.Unsafe, List(n)
    )))
    val partialDefn = ExportItem.Info(ConstantInfo.DefnInfo(DefinitionVal(
      cv, Expr.const("Nat"), ReducibilityHints.Abbrev, DefinitionSafety.Partial, List(n)
    )))
    val unsafeOpaque = ExportItem.Info(ConstantInfo.OpaqueInfo(OpaqueVal(cv, Expr.const("Nat"), true, List(n))))
    val unsafeInduct = ExportItem.Info(ConstantInfo.InductInfo(InductiveVal(
      cv, 0, 0, List(n), Nil, 0, false, true, false
    )))
    val unsafeCtor = ExportItem.Info(ConstantInfo.CtorInfo(ConstructorVal(cv, n, 0, 0, 0, true)))
    val unsafeRec = ExportItem.Info(ConstantInfo.RecInfo(RecursorVal(cv, List(n), 0, 0, 1, 0, Nil, false, true)))
    val nondepLet = ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(
      ConstantVal(n, Nil, Expr.LetE(n, Expr.const("Nat"), Expr.const("Nat"), Expr.BVar(0), true)), false
    )))

    val lossy = List(unsafeAxiom, unsafeDefn, partialDefn, unsafeOpaque, unsafeInduct, unsafeCtor, unsafeRec, nondepLet)
    lossy.foreach { it =>
      List[ExportFormat](TextV1, TextV2).foreach { fmt =>
        intercept[ExportException](ExportWriter.toString(envOf(it), fmt))
      }
    }

    // NDJSON carries all of them, so they must survive a round trip there.
    List(unsafeAxiom, unsafeDefn, partialDefn, unsafeOpaque, nondepLet).foreach { it =>
      assertEquals(roundTrip(envOf(it), Ndjson("3.1.0")).items, Vector(it))
    }
    List(unsafeInduct, unsafeCtor, unsafeRec).foreach { it =>
      assertEquals(roundTrip(envOf(it), Ndjson("3.1.0")).items, Vector(it))
    }
  }

  test("text v1 rejects a mutual or unsafe inductive block") {
    val a = InductiveType(Name.parse("A"), Expr.Sort(Level.one), Nil)
    val b = InductiveType(Name.parse("B"), Expr.Sort(Level.one), Nil)
    def envOf(d: Declaration) = ExportEnv(TextV1, None, Vector(ExportItem.Decl(d)))

    val mutual = intercept[ExportException](
      ExportWriter.toString(envOf(Declaration.InductDecl(Nil, 0, List(a, b), false)), TextV1)
    )
    assert(clue(mutual.getMessage).contains("mutual inductive block of 2 types"))

    intercept[ExportException](
      ExportWriter.toString(envOf(Declaration.InductDecl(Nil, 0, List(a), true)), TextV1)
    )

    // A single safe type is still fine.
    assertEquals(
      ExportReader.fromString(
        ExportWriter.toString(envOf(Declaration.InductDecl(Nil, 0, List(a), false)), TextV1)
      ).items.length,
      1
    )
  }

  test("infoEnvironment preserves declaration order") {
    val env = ExportReader.fromString(textV2Literal)
    assertEquals(
      env.infoEnvironment.names.map(_.toString),
      Vector("Nat", "Nat.zero", "Nat.succ", "Nat.rec", "ax", "Nat.add", "thm1", "opq", "Quot")
    )
  }
