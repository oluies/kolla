package kolla.kernel

class EnvironmentSuite extends munit.FunSuite:

  def ax(n: String, lp: List[String] = Nil): ConstantInfo =
    ConstantInfo.AxiomInfo(
      AxiomVal(ConstantVal(Name.parse(n), lp.map(Name.mkSimple), Expr.Sort(Level.zero)), false)
    )

  test("add and look up") {
    val env = Environment.empty.addCore(ax("A")).addCore(ax("B"))
    assertEquals(env.size, 2)
    assertEquals(env.find(Name.parse("A")).map(_.name), Some(Name.parse("A")))
    assertEquals(env.find(Name.parse("C")), None)
    assertEquals(env.get(Name.parse("B")).name, Name.parse("B"))
    intercept[KernelException](env.get(Name.parse("C")))
  }

  test("declaration order is preserved") {
    val env = Environment.empty.addCoreAll(List(ax("C"), ax("A"), ax("B")))
    assertEquals(env.names.map(_.toString).toList, List("C", "A", "B"))
    assertEquals(env.declarations.map(_.name.toString).toList, List("C", "A", "B"))
  }

  test("duplicate declarations are rejected") {
    val env = Environment.empty.addCore(ax("A"))
    val e = intercept[KernelException](env.addCore(ax("A")))
    assertEquals(e.kind, ExceptionKind.AlreadyDeclared)
  }

  test("duplicate universe parameters are rejected") {
    val e = intercept[KernelException](Environment.empty.addCore(ax("A", List("u", "u"))))
    assertEquals(e.kind, ExceptionKind.DuplicateUniverseParam)
  }

  test("quot initialization flag") {
    assert(!Environment.empty.quotInitialized)
    assert(Environment.empty.markQuotInitialized.quotInitialized)
  }

  test("ConstantInfo accessors") {
    val cv = ConstantVal(Name.parse("f"), List(Name.mkSimple("u")), Expr.Sort(Level.zero))
    val d  = ConstantInfo.DefnInfo(
      DefinitionVal(cv, Expr.const("Nat"), ReducibilityHints.Regular(7), DefinitionSafety.Safe, List(cv.name))
    )
    assertEquals(d.name, Name.parse("f"))
    assertEquals(d.numLevelParams, 1)
    assert(d.isDefinition)
    assert(d.hasValue())
    assertEquals(d.value(), Some(Expr.const("Nat")))
    assertEquals(d.hints, ReducibilityHints.Regular(7): ReducibilityHints)
    assert(!d.isUnsafe)

    val t = ConstantInfo.ThmInfo(TheoremVal(cv, Expr.const("Nat"), List(cv.name)))
    assert(t.hasValue())
    assertEquals(t.hints, ReducibilityHints.Opaque: ReducibilityHints)

    val o = ConstantInfo.OpaqueInfo(OpaqueVal(cv, Expr.const("Nat"), false, List(cv.name)))
    assert(!o.hasValue())
    assert(o.hasValue(allowOpaque = true))
    assertEquals(o.value(), None)
    assertEquals(o.value(allowOpaque = true), Some(Expr.const("Nat")))
  }

  test("ReducibilityHints.compare") {
    import ReducibilityHints.*
    assertEquals(compare(Regular(3), Regular(3)), 0)
    assert(compare(Regular(5), Regular(3)) < 0)
    assert(compare(Regular(3), Regular(5)) > 0)
    assertEquals(compare(Opaque, Opaque), 0)
    assertEquals(compare(Abbrev, Abbrev), 0)
    assert(compare(Opaque, Regular(1)) > 0)
    assert(compare(Regular(1), Opaque) < 0)
    assert(compare(Abbrev, Regular(1)) < 0)
    assert(compare(Regular(1), Abbrev) > 0)
    assert(compare(Abbrev, Opaque) < 0)
    assert(compare(Opaque, Abbrev) > 0)
  }

  test("RecursorVal indices") {
    val cv = ConstantVal(Name.parse("Nat.rec"), Nil, Expr.Sort(Level.zero))
    val r = RecursorVal(cv, List(Name.parse("Nat")), 0, 0, 1, 2, Nil, false, false)
    assertEquals(r.majorIdx, 3)
    assertEquals(r.majorInduct, Name.parse("Nat"))
    // Read off the recursor's type, not `all`: see the nested case below.
    assertEquals(r.all, List(Name.parse("Nat")))
  }

  test("Declaration names") {
    val it = InductiveType(
      Name.parse("T"),
      Expr.Sort(Level.one),
      List(Constructor(Name.parse("T.mk"), Expr.const("T")))
    )
    assertEquals(
      Declaration.InductDecl(Nil, 0, List(it), false).declNames.map(_.toString),
      List("T", "T.mk")
    )
    assert(!Declaration.QuotDecl.anyUnsafe)
    assertEquals(Declaration.QuotDecl.declNames, Nil)
  }

  test("a nested recursor's major premise is not the block's own type") {
    // `SnapshotTree.rec_3` in Lean's own source has `all = [SnapshotTree]` but
    // a major premise of type `SnapshotTask SnapshotTree`. Taking `all.head`
    // asks `to_cnstr_when_structure` about the wrong inductive, which decides
    // whether a structure major gets eta-expanded into a constructor
    // application, so iota silently fails to fire. See docs/semantics.md K17.
    val tree = Name.parse("Tree")
    val task = Name.parse("Task")
    val u    = Name.mkSimple("u")
    def pi(n: String, dom: Expr, body: Expr): Expr =
      Expr.ForallE(Name.mkSimple(n), dom, body, BinderInfo.Default)

    // motive, minor, major : Task Tree  ->  Sort u
    val tpe =
      pi("motive", Expr.Sort(Level.Param(u)),
        pi("minor", Expr.Sort(Level.Param(u)),
          pi("t", Expr.App(Expr.Const(task, Nil), Expr.Const(tree, Nil)), Expr.Sort(Level.Param(u)))))
    val rec = RecursorVal(
      ConstantVal(Name.parse("Tree.rec_3"), List(u), tpe),
      all = List(tree),
      numParams = 0, numIndices = 0, numMotives = 1, numMinors = 1,
      rules = Nil, k = false, isUnsafe = false
    )
    assertEquals(rec.majorIdx, 2)
    assertEquals(rec.majorInduct, task)
    assertNotEquals(rec.majorInduct, rec.all.head)
  }

  test("majorInduct falls back when the type is not a recursor telescope") {
    val rec = RecursorVal(
      ConstantVal(Name.parse("Bad.rec"), Nil, Expr.Sort(Level.zero)),
      all = List(Name.parse("Bad")),
      numParams = 0, numIndices = 0, numMotives = 1, numMinors = 1,
      rules = Nil, k = false, isUnsafe = false
    )
    assertEquals(rec.majorInduct, Name.parse("Bad"))
  }
