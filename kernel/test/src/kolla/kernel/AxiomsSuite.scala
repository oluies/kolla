package kolla.kernel

/** What a declaration rests on, which type-checking does not answer.
  * See docs/semantics.md A1.
  */
class AxiomsSuite extends munit.FunSuite:

  private val prop  = Expr.Sort(Level.zero)
  private def n(s: String): Name = Name.parse(s)

  private def axiom(name: String, tpe: Expr): ConstantInfo =
    ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(n(name), Nil, tpe), isUnsafe = false))

  private def thm(name: String, tpe: Expr, value: Expr): ConstantInfo =
    ConstantInfo.ThmInfo(TheoremVal(ConstantVal(n(name), Nil, tpe), value, List(n(name))))

  private def defn(name: String, tpe: Expr, value: Expr): ConstantInfo =
    ConstantInfo.DefnInfo(
      DefinitionVal(ConstantVal(n(name), Nil, tpe), value,
                    ReducibilityHints.Abbrev, DefinitionSafety.Safe, List(n(name)))
    )

  test("a declaration resting on nothing reports no axioms") {
    val env = Environment.empty.addCore(defn("P", prop, prop))
    val c   = Axioms.of(env, n("P")).toOption.get
    assertEquals(c.axioms, Vector.empty[Name])
    assert(!c.hasSorry)
    assert(clue(c.render).contains("no axioms"))
  }

  test("a sorry-backed theorem is reported as not a proof") {
    // The case this exists for: it type-checks exactly like a real proof.
    val goal = Expr.Const(n("Goal"), Nil)
    val env = Environment.empty
      .addCore(defn("Goal", prop, prop))
      .addCore(axiom("sorryAx", Expr.ForallE(n("α"), prop, Expr.BVar(0), BinderInfo.Default)))
      .addCore(thm("big_result", goal, Expr.App(Expr.Const(Axioms.sorry, Nil), goal)))
    val c = Axioms.of(env, n("big_result")).toOption.get
    assert(c.hasSorry, clue(c.render))
    assertEquals(c.axioms, Vector(Axioms.sorry))
    assert(clue(c.render).contains("NOT A PROOF"))
  }

  test("a sorry in a dependency is found, not only in the declaration itself") {
    // Reading the source of `uses_lemma` would show no sorry at all.
    val goal = Expr.Const(n("Goal"), Nil)
    val env = Environment.empty
      .addCore(defn("Goal", prop, prop))
      .addCore(axiom("sorryAx", Expr.ForallE(n("α"), prop, Expr.BVar(0), BinderInfo.Default)))
      .addCore(thm("lemma", goal, Expr.App(Expr.Const(Axioms.sorry, Nil), goal)))
      .addCore(thm("uses_lemma", goal, Expr.Const(n("lemma"), Nil)))
    val c = Axioms.of(env, n("uses_lemma")).toOption.get
    assert(c.hasSorry, clue(c.render))
  }

  test("Lean's trust base is reported apart from anything unusual") {
    val goal = Expr.Const(n("Goal"), Nil)
    val env = Environment.empty
      .addCore(defn("Goal", prop, prop))
      .addCore(axiom("propext", prop))
      .addCore(axiom("Classical.choice", prop))
      .addCore(axiom("myOwnAxiom", prop))
      .addCore(thm("t", goal, Expr.mkAppN(Expr.Const(n("Goal"), Nil), Seq(
        Expr.Const(n("propext"), Nil), Expr.Const(n("Classical.choice"), Nil),
        Expr.Const(n("myOwnAxiom"), Nil)))))
    val c = Axioms.of(env, n("t")).toOption.get
    assertEquals(c.axioms.map(_.toString), Vector("Classical.choice", "myOwnAxiom", "propext"))
    assertEquals(c.unusual.map(_.toString), Vector("myOwnAxiom"))
    assert(!c.hasSorry)
    assert(clue(c.render).contains("outside Lean's trust base"))
    assert(clue(c.render).contains("trust base"))
  }

  test("the type is followed, not only the value") {
    // A statement's meaning rests on its type's constants too.
    val viaType = Expr.Const(n("shaky"), Nil)
    val env = Environment.empty
      .addCore(axiom("myOwnAxiom", prop))
      .addCore(defn("shaky", prop, Expr.Const(n("myOwnAxiom"), Nil)))
      .addCore(thm("t", viaType, Expr.Const(n("t_proof"), Nil)))
      .addCore(defn("t_proof", prop, prop))
    val c = Axioms.of(env, n("t")).toOption.get
    assertEquals(c.axioms.map(_.toString), Vector("myOwnAxiom"))
  }

  test("a cycle does not loop") {
    val env = Environment.empty
      .addCore(defn("a", Expr.Const(n("b"), Nil), prop))
      .addCore(defn("b", Expr.Const(n("a"), Nil), prop))
    assert(Axioms.of(env, n("a")).isRight)
  }

  test("an unknown constant is an error, not an empty closure") {
    // Reporting "no axioms" for a name that is not there would read as a
    // clean bill of health for something never checked.
    assertEquals(Axioms.of(Environment.empty, n("nope")), Left("unknown constant 'nope'"))
  }
