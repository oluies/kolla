package kolla.leanexport

import kolla.kernel.*

/** Replays real lean4export output through the kernel. */
class CheckRealExportSuite extends munit.FunSuite:

  private def resource(name: String): Vector[String] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src = scala.io.Source.fromInputStream(in, "UTF-8")
    try src.getLines().toVector
    finally src.close()

  private def replay(file: String): (Environment, Map[Name, CheckOutcome]) =
    val env0 = ExportReader.fromLines(resource(file))
    val dc   = new DeclarationChecker(KernelProfile.v4_35)
    var env  = Environment.empty
    val outcomes = Map.newBuilder[Name, CheckOutcome]
    env0.infos.foreach { info =>
      val (next, outcome) = dc.addInfo(env, info)
      env = next
      outcomes += (info.name -> outcome)
    }
    (env, outcomes.result())

  // Fully checked counts are the number of def/thm/opaque/axiom entries in each
  // file; inductives, constructors, recursors and the quotient package have
  // their types checked but are not yet validated as a block.
  test("every declaration of the Nat.add export is accepted") {
    val (env, outcomes) = replay("nat-add-3.1.0.ndjson")
    assertEquals(env.size, outcomes.size)
    assertEquals(env.size, 17)
    assertEquals(outcomes.count(_._2 == CheckOutcome.Checked), 7)
    assertEquals(outcomes(Name.parse("Nat.add")), CheckOutcome.Checked)
    assertEquals(outcomes(Name.parse("Nat.rec")), CheckOutcome.TypeOnly)
  }

  test("every declaration of the Quot.sound export is accepted") {
    val (env, outcomes) = replay("quot-sound-3.1.0.ndjson")
    assertEquals(env.size, 8)
    assert(env.contains(Name.parse("Quot")))
    assert(env.quotInitialized)
    assertEquals(outcomes.count(_._2 == CheckOutcome.Checked), 1)
    assertEquals(outcomes(Name.parse("Quot.sound")), CheckOutcome.Checked)
  }

  test("every declaration of the 3.0.0 Nat.add_succ export is accepted") {
    val (env, outcomes) = replay("nat-add-succ-3.0.0.ndjson")
    assertEquals(env.size, 32)
    assertEquals(outcomes.count(_._2 == CheckOutcome.Checked), 13)
    assertEquals(outcomes(Name.parse("Nat.add_succ")), CheckOutcome.Checked)
  }

  test("iota reduction through Nat.rec computes") {
    val (env, _) = replay("nat-add-3.1.0.ndjson")
    val tc = new TypeChecker(env, KernelProfile.v4_35)
    def lit(n: Int): Expr = Expr.natLit(n)
    val add = Expr.const(Name.parse("Nat.add"))
    // `Nat.add` is defined by recursion, so this exercises whnf's iota rule and
    // the Nat literal extension.
    assertEquals(tc.whnf(Expr.mkAppN(add, Seq(lit(2), lit(3)))), lit(5))
    assert(tc.isDefEq(Expr.mkAppN(add, Seq(lit(2), lit(3))), lit(5)))
    assert(!tc.isDefEq(Expr.mkAppN(add, Seq(lit(2), lit(3))), lit(6)))
  }

  test("inferType agrees with the declared types") {
    val (env, outcomes) = replay("nat-add-3.1.0.ndjson")
    val tc = new TypeChecker(env, KernelProfile.v4_35)
    env.declarations.foreach { info =>
      info.value() match
        case Some(v) =>
          val t = tc.infer(v)
          assert(tc.isDefEq(t, info.tpe), clue(info.name.toString))
        case None => ()
    }
  }

  test("a corrupted value is rejected") {
    val env0 = ExportReader.fromLines(resource("nat-add-3.1.0.ndjson"))
    val dc   = new DeclarationChecker(KernelProfile.v4_35)
    var env  = Environment.empty
    var checkedOne = false
    env0.infos.foreach { info =>
      info match
        case ConstantInfo.DefnInfo(v) if !checkedOne && v.toConstantVal.levelParams.isEmpty =>
          checkedOne = true
          // Replace the value with a nat literal, which cannot have the
          // declared function type.
          val broken = v.copy(value = Expr.natLit(0))
          val e = intercept[KernelException](dc.addDefinition(env, broken))
          assert(
            e.kind == ExceptionKind.DefinitionTypeMismatch || e.kind == ExceptionKind.AppTypeMismatch,
            clue(e.getMessage)
          )
          assert(e.trace.nonEmpty, clue(e.getMessage))
          env = dc.addInfo(env, info)._1
        case _ => env = dc.addInfo(env, info)._1
    }
    assert(checkedOne)
  }
