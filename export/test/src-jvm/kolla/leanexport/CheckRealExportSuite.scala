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
    // 1 axiom plus the four validated quotient constants.
    assertEquals(outcomes.count(_._2 == CheckOutcome.Checked), 5)
    assertEquals(outcomes(Name.parse("Quot.sound")), CheckOutcome.Checked)
  }

  test("every declaration of the 3.0.0 Nat.add_succ export is accepted") {
    val (env, outcomes) = replay("nat-add-succ-3.0.0.ndjson")
    assertEquals(env.size, 32)
    assertEquals(outcomes.count(_._2 == CheckOutcome.Checked), 13)
    assertEquals(outcomes(Name.parse("Nat.add_succ")), CheckOutcome.Checked)
  }

  test("the kernel's quotient package matches the one Lean exports") {
    val env0 = ExportReader.fromLines(resource("quot-sound-3.1.0.ndjson"))
    val exported = env0.infos.collect { case ConstantInfo.QuotInfo(q) => q }
    assertEquals(exported.length, 4)
    // Lean built these four constants itself; `Quot.declarations` rebuilds them
    // from `add_quot`, so this compares against ground truth.
    Quot.validate(Environment.empty, exported.toList)

    val built = Quot.declarations.map(d => d.toConstantVal.name -> d).toMap
    exported.foreach { got =>
      val want = built(got.toConstantVal.name)
      assertEquals(got.kind, want.kind, clue(got.toConstantVal.name.toString))
      assertEquals(
        got.toConstantVal.levelParams.length,
        want.toConstantVal.levelParams.length,
        clue(got.toConstantVal.name.toString)
      )
      val renamed = ExprOps.instantiateLevelParams(
        want.toConstantVal.tpe,
        want.toConstantVal.levelParams,
        got.toConstantVal.levelParams.map(Level.Param(_))
      )
      assertEquals(renamed, got.toConstantVal.tpe, clue(got.toConstantVal.name.toString))
    }
  }

  test("checkEqType accepts Lean's Eq and the quotient package installs") {
    val (env, outcomes) = replay("quot-sound-3.1.0.ndjson")
    assert(env.contains(Name.parse("Eq")))
    Quot.checkEqType(env)
    assert(env.quotInitialized)
    // The export ships the four constants; the kernel builds them and the driver
    // validates each one, so all four count as fully checked.
    List("Quot", "Quot.mk", "Quot.lift", "Quot.ind").foreach { n =>
      assertEquals(outcomes(Name.parse(n)), CheckOutcome.Checked, clue(n))
    }
    // add_quot is idempotent.
    assertEquals(Quot.add(env).size, env.size)
  }

  test("a quotient constant with the wrong type is rejected") {
    val (env, _) = replay("quot-sound-3.1.0.ndjson")
    val bad = QuotVal(
      ConstantVal(Name.parse("Quot"), List(Name.mkSimple("u")), Expr.Sort(Level.zero)),
      QuotKind.Type
    )
    val e = intercept[KernelException](Quot.validate(env, List(bad)))
    assert(clue(e.getMessage).contains("but the kernel builds"))
    val wrongKind = Quot.declarations.find(_.toConstantVal.name == Name.parse("Quot")).get
      .copy(kind = QuotKind.Lift)
    assert(clue(intercept[KernelException](Quot.validate(env, List(wrongKind))).getMessage)
      .contains("quotient kind mismatch"))
  }

  /** Walks an export file, running the inductive checker on each block instead
    * of carrying the file's entries over unchecked.
    */
  private def checkInductiveBlocks(file: String): (Int, Int) =
    val infos = ExportReader.fromLines(resource(file)).infos
    val dc    = new DeclarationChecker(KernelProfile.v4_35)
    var env   = Environment.empty
    var blocks = 0
    var recsSeen = 0
    var i = 0
    while i < infos.length do
      infos(i) match
        case ConstantInfo.InductInfo(first) =>
          val blockNames = first.all.toSet
          val inds  = List.newBuilder[InductiveVal]
          val ctors = List.newBuilder[ConstructorVal]
          val recs  = List.newBuilder[RecursorVal]
          var j = i
          var consumed = 0
          // The entries of one block are contiguous: types, then constructors,
          // then recursors.
          var scanning = true
          while scanning && j < infos.length do
            infos(j) match
              case ConstantInfo.InductInfo(v) if blockNames.contains(v.toConstantVal.name) =>
                inds += v; consumed += 1; j += 1
              case ConstantInfo.CtorInfo(v) if blockNames.contains(v.induct) =>
                ctors += v; consumed += 1; j += 1
              case ConstantInfo.RecInfo(v) if v.all.toSet == blockNames =>
                recs += v; consumed += 1; j += 1
              case _ => scanning = false
          val exportedInds  = inds.result()
          val exportedCtors = ctors.result()
          val exportedRecs  = recs.result()
          val declaration   = InductiveChecker.declarationOf(exportedInds, exportedCtors)
          val result        = new InductiveChecker(env, declaration, KernelProfile.v4_35, exportedInds.head.numNested).run()
          InductiveChecker.validate(
            exportedInds, exportedCtors, result.inductives, result.constructors,
            exportedRecs, result.recursors
          )
          env = result.env
          blocks += 1
          recsSeen += exportedRecs.length
          i = j
        case info =>
          env = dc.addInfo(env, info)._1
          i += 1
    (blocks, recsSeen)

  test("the kernel regenerates the recursors Lean exports") {
    // isRec, isReflexive, numIndices, cidx, numFields, the recursor types and
    // every computation rule right-hand side are recomputed and compared against
    // the values in the file. The second number is how many recursors were
    // compared, so an empty comparison cannot pass unnoticed.
    assertEquals(checkInductiveBlocks("nat-add-3.1.0.ndjson"), (3, 3))
    assertEquals(checkInductiveBlocks("nat-add-succ-3.0.0.ndjson"), (6, 6))
    assertEquals(checkInductiveBlocks("quot-sound-3.1.0.ndjson"), (1, 1))
  }

  test("a mutated recursor is rejected") {
    val infos = ExportReader.fromLines(resource("nat-add-3.1.0.ndjson")).infos
    val natName = Name.parse("Nat")
    val natInd = infos.collectFirst {
      case ConstantInfo.InductInfo(v) if v.toConstantVal.name == natName => v
    }.get
    val natCtors = infos.collect { case ConstantInfo.CtorInfo(v) if v.induct == natName => v }.toList
    val natRec = infos.collectFirst {
      case ConstantInfo.RecInfo(v) if v.toConstantVal.name == Name.parse("Nat.rec") => v
    }.get
    val declaration = InductiveChecker.declarationOf(List(natInd), natCtors)
    val r = new InductiveChecker(Environment.empty, declaration, KernelProfile.v4_35).run()

    // Unmutated, Lean's recursor and the regenerated one agree.
    InductiveChecker.validate(List(natInd), natCtors, r.inductives, r.constructors, List(natRec), r.recursors)
    assertEquals(natRec.rules.length, 2)
    assertEquals(r.recursors.length, 1)
    assertEquals(r.recursors.head.toConstantVal.name, Name.parse("Nat.rec"))
    assert(!r.kTarget)

    def reject(label: String, mutated: RecursorVal, expected: String): Unit =
      val got =
        try
          InductiveChecker.validate(
            List(natInd), natCtors, r.inductives, r.constructors, List(mutated), r.recursors
          )
          None
        catch case e: KernelException => Some(e.getMessage)
      got match
        case None      => fail(s"mutation '$label' was accepted")
        case Some(msg) => assert(msg.contains(expected), clue(label) + " / " + clue(msg))

    // Altered rule right-hand side.
    reject(
      "rule rhs",
      natRec.copy(rules = natRec.rules.head.copy(rhs = Expr.natLit(0)) :: natRec.rules.tail),
      "the kernel derives"
    )
    // Altered field count on a rule.
    reject(
      "rule nfields",
      natRec.copy(rules = natRec.rules.map(x => x.copy(nfields = x.nfields + 1))),
      "nfields"
    )
    reject("numMinors", natRec.copy(numMinors = natRec.numMinors + 1), "numMinors")
    reject("numMotives", natRec.copy(numMotives = 2), "numMotives")
    reject("k", natRec.copy(k = true), "K-like reduction flag")
    reject("numIndices", natRec.copy(numIndices = 1), "numIndices")
    // A changed universe level in the recursor type.
    reject(
      "recursor type",
      natRec.copy(toConstantVal = natRec.toConstantVal.copy(tpe = Expr.Sort(Level.zero))),
      "the recursor type is"
    )
    // A dropped rule.
    reject("dropped rule", natRec.copy(rules = natRec.rules.take(1)), "the rule count")
  }

  test("a swapped constructor index is rejected") {
    val infos = ExportReader.fromLines(resource("nat-add-3.1.0.ndjson")).infos
    val natInd = infos.collectFirst {
      case ConstantInfo.InductInfo(v) if v.toConstantVal.name == Name.parse("Nat") => v
    }.get
    val natCtors = infos.collect {
      case ConstantInfo.CtorInfo(v) if v.induct == Name.parse("Nat") => v
    }.toList
    assertEquals(natCtors.length, 2)
    val declaration = InductiveChecker.declarationOf(List(natInd), natCtors)
    val result = new InductiveChecker(Environment.empty, declaration, KernelProfile.v4_35).run()
    // Unmutated, the derived values agree.
    InductiveChecker.validate(List(natInd), natCtors, result.inductives, result.constructors)
    // Swap cidx on the two constructors.
    val swapped = natCtors.map(c => c.copy(cidx = 1 - c.cidx))
    val e = intercept[KernelException](
      InductiveChecker.validate(List(natInd), swapped, result.inductives, result.constructors)
    )
    assert(clue(e.getMessage).contains("cidx"))
    // Claim a wrong field count.
    val wrongFields = natCtors.map(c => c.copy(numFields = c.numFields + 1))
    assert(clue(intercept[KernelException](
      InductiveChecker.validate(List(natInd), wrongFields, result.inductives, result.constructors)
    ).getMessage).contains("numFields"))
    // Claim the type is not recursive.
    val notRec = List(natInd.copy(isRec = false))
    assert(clue(intercept[KernelException](
      InductiveChecker.validate(notRec, natCtors, result.inductives, result.constructors)
    ).getMessage).contains("isRec"))
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
