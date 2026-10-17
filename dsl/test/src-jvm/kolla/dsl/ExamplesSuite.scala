package kolla.dsl

import kolla.kernel.*
import kolla.leanexport.*
import kolla.dsl.LeanDsl.*
import kolla.dsl.LeanInterpolator.lean

/** The two worked examples: a hand-built identity function, and a theorem taken
  * from an environment that Lean exported.
  */
class ExamplesSuite extends munit.FunSuite:

  private def resource(name: String): Vector[String] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src = scala.io.Source.fromInputStream(in, "UTF-8")
    try src.getLines().toVector
    finally src.close()

  /** Replays an export file, checking each entry. */
  private def replay(file: String): Environment =
    val infos = ExportReader.fromLines(resource(file)).infos
    val dc    = new DeclarationChecker(KernelProfile.v4_35)
    var env   = Environment.empty
    var i     = 0
    while i < infos.length do
      infos(i) match
        case ConstantInfo.InductInfo(first) =>
          val block = first.all.toSet
          val inds  = List.newBuilder[InductiveVal]
          val ctors = List.newBuilder[ConstructorVal]
          var j = i
          var scanning = true
          while scanning && j < infos.length do
            infos(j) match
              case ConstantInfo.InductInfo(v) if block.contains(v.toConstantVal.name) => inds += v; j += 1
              case ConstantInfo.CtorInfo(v) if block.contains(v.induct)                => ctors += v; j += 1
              case ConstantInfo.RecInfo(v) if v.all.toSet == block                     => j += 1
              case _                                                                   => scanning = false
          val r = AddInductive.add(env, InductiveChecker.declarationOf(inds.result(), ctors.result()), KernelProfile.v4_35)
          env = r.env
          i = j
        case info =>
          env = dc.addInfo(env, info)._1
          i += 1
    env

  private lazy val natAddEnv: Environment = replay("nat-add-3.1.0.ndjson")

  /** This one carries a theorem, `Nat.add_succ`. */
  private lazy val addSuccEnv: Environment = replay("nat-add-succ-3.0.0.ndjson")

  // -------------------------------------------- example 1: identity function

  test("a hand-built identity function type checks") {
    val u = Name.mkSimple("u")

    // With the builder API: binders are Scala functions.
    val idBuilt     = Lam("A".n, Sort("u".u))(a => Lam("a".n, a)(x => x))
    val idTypeBuilt = Pi("A".n, Sort("u".u))(a => Pi("a".n, a)(_ => a))

    // With the interpolator: the same term, parsed at compile time.
    val idLean     = lean"fun (A : Sort u) (a : A) => a"
    val idTypeLean = lean"forall (A : Sort u) (a : A), A"

    assertEquals(idBuilt, idLean)
    assertEquals(idTypeBuilt, idTypeLean)
    assert(Expr.isBiEqual(idBuilt, idLean))

    val tc = new TypeChecker(Environment.empty, KernelProfile.v4_35)
    val inferred = tc.check(idBuilt, List(u))
    assert(tc.isDefEq(inferred, idTypeBuilt), clue(Pretty.expr(inferred)))

    // It really is the identity: applied to a type and a value it reduces.
    val env = Environment.empty.addCore(ConstantInfo.AxiomInfo(
      AxiomVal(ConstantVal(Name.parse("Nat"), Nil, Expr.Sort(Level.one)), false)
    )).addCore(ConstantInfo.DefnInfo(DefinitionVal(
      ConstantVal(Name.parse("id"), List(u), idTypeBuilt), idBuilt,
      ReducibilityHints.Regular(1), DefinitionSafety.Safe, List(Name.parse("id"))
    )))
    val tc2 = new TypeChecker(env, KernelProfile.v4_35)
    val applied = lean"id.{1} Nat ${Expr.natLit(7)}"
    assertEquals(tc2.whnf(applied), Expr.natLit(7))
  }

  test("the identity definition is accepted by the declaration checker") {
    val u = Name.mkSimple("u")
    val dc = new DeclarationChecker(KernelProfile.v4_35)
    val env = dc.addDefinition(
      Environment.empty,
      DefinitionVal(
        ConstantVal(Name.parse("id"), List(u), lean"forall (A : Sort u) (a : A), A"),
        lean"fun (A : Sort u) (a : A) => a",
        ReducibilityHints.Abbrev,
        DefinitionSafety.Safe,
        List(Name.parse("id"))
      )
    )
    assert(env.contains(Name.parse("id")))

    // A wrong type is rejected, with a defeq trace.
    val e = intercept[KernelException](
      dc.addDefinition(
        Environment.empty,
        DefinitionVal(
          ConstantVal(Name.parse("bad"), List(u), lean"forall (A : Sort u) (a : A), A"),
          lean"fun (A : Sort u) (a : A) => A",
          ReducibilityHints.Abbrev,
          DefinitionSafety.Safe,
          List(Name.parse("bad"))
        )
      )
    )
    assertEquals(e.kind, ExceptionKind.DefinitionTypeMismatch)
    assert(e.trace.nonEmpty)
  }

  // ------------------------------------------- example 2: Nat.add_comm's kin

  test("the exported environment is replayed and its theorem statements check") {
    val env = addSuccEnv
    assert(env.contains(Name.parse("Nat")))
    assert(env.contains(Name.parse("Nat.add_succ")))
    // Every theorem's statement is a proposition and its value proves it.
    val thms = env.declarations.collect { case ConstantInfo.ThmInfo(v) => v }
    // The fixture must actually carry one, or this asserts nothing.
    assertEquals(thms.length, 1)
    assertEquals(thms.head.toConstantVal.name, Name.parse("Nat.add_succ"))
    thms.foreach { t =>
      val cv = t.toConstantVal
      val tc = new TypeChecker(env, KernelProfile.v4_35)
      assert(tc.isProp(cv.tpe), clue(cv.name.toString))
      val inferred = tc.check(t.value, cv.levelParams)
      assert(tc.isDefEq(inferred, cv.tpe), clue(cv.name.toString))
    }
  }

  test("a statement written with the interpolator matches the exported one") {
    val env = natAddEnv
    // `Nat.add` from the file, applied with the DSL, reduces as the kernel says.
    val tc = new TypeChecker(env, KernelProfile.v4_35)
    val sum = lean"Nat.add 2 3"
    assertEquals(tc.whnf(sum), Expr.natLit(5))
    assertEquals(tc.infer(sum), Expr.const("Nat"))

    // The declared type of `Nat.add` is what the interpolator writes.
    val declared = env.get(Name.parse("Nat.add")).tpe
    assert(tc.isDefEq(declared, lean"Nat -> Nat -> Nat"), clue(Pretty.expr(declared)))
  }

  test("a theorem restated with the interpolator still checks") {
    val env = addSuccEnv
    val t = env.declarations.collectFirst { case ConstantInfo.ThmInfo(v) => v }
      .getOrElse(fail("the fixture carries no theorem"))
    val cv = t.toConstantVal
    val tc = new TypeChecker(env, KernelProfile.v4_35)
    // A spliced statement is inserted unchanged, binder names included.
    val restated = lean"${cv.tpe}"
    assertEquals(restated, cv.tpe)
    assert(Expr.isBiEqual(restated, cv.tpe))
    val inferred = tc.check(t.value, cv.levelParams)
    assert(tc.isDefEq(inferred, restated))
    // And applying the proof to the statement's binders still type checks.
    assert(tc.isProp(cv.tpe))
  }

  test("a spliced declaration type is inserted unchanged") {
    val env = natAddEnv
    val declared = env.get(Name.parse("Nat.add")).tpe
    assertEquals(lean"$declared", declared)
    assert(Expr.isBiEqual(lean"$declared", declared))
    // Inside a binder the splice is still unchanged, which is why it has to be
    // closed.
    val wrapped = lean"fun (z : Nat) => $declared"
    assertEquals(wrapped.asInstanceOf[Expr.Lam].body, declared)
  }
