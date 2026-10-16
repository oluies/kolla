package kolla.leanexport

import kolla.kernel.*

/** Parses export files produced by lean4export itself. */
class RealExportSuite extends munit.FunSuite:

  import ExportFormat.*

  private def resource(name: String): Vector[String] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src = scala.io.Source.fromInputStream(in, "UTF-8")
    try src.getLines().toVector
    finally src.close()

  private def read(name: String): ExportEnv = ExportReader.fromLines(resource(name))

  test("Nat.add exported by lean4export 3.1.0 from Lean 4.35.0") {
    val env = read("nat-add-3.1.0.ndjson")
    assertEquals(env.format, Ndjson("3.1.0"))
    assertEquals(env.meta.map(_.leanVersion), Some("4.35.0"))
    assertEquals(env.meta.map(_.exporterName), Some("lean4export"))
    assert(env.items.forall(_.isInstanceOf[ExportItem.Info]))

    val names = env.infos.map(_.name.toString)
    assert(names.contains("Nat"))
    assert(names.contains("Nat.rec"))
    assert(names.contains("Nat.add"))
    assertEquals(names.distinct.length, names.length)

    env.infos.find(_.name == Name.parse("Nat")).get match
      case ConstantInfo.InductInfo(iv) =>
        assertEquals(iv.numParams, 0)
        assertEquals(iv.numIndices, 0)
        assertEquals(iv.ctors.map(_.toString), List("Nat.zero", "Nat.succ"))
        assert(iv.isRec)
        assertEquals(iv.toConstantVal.tpe, Expr.Sort(Level.one))
      case other => fail(s"expected an inductive, got $other")

    env.infos.find(_.name == Name.parse("Nat.rec")).get match
      case ConstantInfo.RecInfo(rv) =>
        assertEquals(rv.numMotives, 1)
        assertEquals(rv.numMinors, 2)
        assertEquals(rv.rules.map(_.ctor.toString), List("Nat.zero", "Nat.succ"))
        assertEquals(rv.rules.map(_.nfields), List(0, 1))
        assertEquals(rv.toConstantVal.levelParams.length, 1)
      case other => fail(s"expected a recursor, got $other")

    env.infos.find(_.name == Name.parse("Nat.add")).get match
      case ConstantInfo.DefnInfo(dv) =>
        assertEquals(dv.safety, DefinitionSafety.Safe)
        assert(dv.hints.isRegular)
      case other => fail(s"expected a definition, got $other")
  }

  test("Quot.sound exported by lean4export 3.1.0") {
    val env = read("quot-sound-3.1.0.ndjson")
    assertEquals(env.format, Ndjson("3.1.0"))
    val quots = env.infos.collect { case ConstantInfo.QuotInfo(q) => q }
    assertEquals(quots.map(_.toConstantVal.name.toString).sorted.toList, List("Quot", "Quot.ind", "Quot.lift", "Quot.mk"))
    assertEquals(
      quots.map(q => q.toConstantVal.name.toString -> q.kind).toMap,
      Map(
        "Quot"      -> QuotKind.Type,
        "Quot.mk"   -> QuotKind.Ctor,
        "Quot.lift" -> QuotKind.Lift,
        "Quot.ind"  -> QuotKind.Ind
      )
    )
    assertEquals(env.infos.count(_.isAxiom), 1)
    assertEquals(env.infos.find(_.isAxiom).map(_.name.toString), Some("Quot.sound"))
  }

  test("Nat.add_succ exported by lean4export 3.0.0 from Lean 4.27.0-rc1") {
    val env = read("nat-add-succ-3.0.0.ndjson")
    assertEquals(env.format, Ndjson("3.0.0"))
    assertEquals(env.meta.map(_.leanVersion), Some("4.27.0-rc1"))
    val names = env.infos.map(_.name.toString)
    assert(names.contains("Nat.add_succ"))
    assert(names.contains("Eq.refl"))
    assertEquals(env.infos.count(_.isTheorem), 1)
    assert(env.infos.count(_.isInductive) >= 5)
    assert(env.infos.count(_.isRecursor) >= 5)
  }

  test("every real export builds an Environment in file order") {
    List("nat-add-3.1.0.ndjson", "quot-sound-3.1.0.ndjson", "nat-add-succ-3.0.0.ndjson").foreach { f =>
      val env = read(f)
      val e   = env.infoEnvironment
      assertEquals(e.size, env.infos.length, clue(f))
      assertEquals(e.names, env.infos.map(_.name), clue(f))
    }
  }

  test("every real export round-trips through the writer") {
    List(
      "nat-add-3.1.0.ndjson"      -> Ndjson("3.1.0"),
      "quot-sound-3.1.0.ndjson"   -> Ndjson("3.1.0"),
      "nat-add-succ-3.0.0.ndjson" -> Ndjson("3.0.0")
    ).foreach { (f, fmt) =>
      val env   = read(f)
      val text1 = ExportWriter.toLines(env, fmt)
      val env2  = ExportReader.fromLines(text1)
      assertEquals(env2.items, env.items, clue(f))
      assertEquals(ExportWriter.toLines(env2, fmt), text1, clue(f))
    }
  }

  test("real ndjson exports re-serialize to text v2 and back") {
    List("nat-add-3.1.0.ndjson", "quot-sound-3.1.0.ndjson", "nat-add-succ-3.0.0.ndjson").foreach { f =>
      val env   = read(f)
      val text1 = ExportWriter.toLines(env, TextV2)
      val env2  = ExportReader.fromLines(text1)
      assertEquals(env2.format, TextV2, clue(f))
      assertEquals(env2.items, env.items, clue(f))
      assertEquals(ExportWriter.toLines(env2, TextV2), text1, clue(f))
    }
  }

  test("the fs2 pipe reads a real export incrementally") {
    val lines = resource("nat-add-3.1.0.ndjson")
    val got = fs2.Stream
      .emits(lines)
      .chunkLimit(7)
      .flatMap(fs2.Stream.chunk)
      .through(ExportReader.pipe[fs2.Pure]())
      .compile
      .toVector
    assertEquals(got, ExportReader.fromLines(lines).items)
  }
