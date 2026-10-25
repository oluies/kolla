package kolla.kernel

/** The `maxSteps` report, which is the only thing a check that does not
  * terminate ever says. See docs/semantics.md K21.
  */
class WorkReportSuite extends munit.FunSuite:

  /** A definition that unfolds to itself, which is what a budget is for.
    *
    * `whnf` reduces without type-checking, so no inductive is needed: the
    * point is that delta plus beta never settles and the counters have
    * something to attribute.
    */
  private val loopName = Name.parse("slowAdd")

  private def loopingEnv: Environment =
    val prop = Expr.Sort(Level.zero)
    val self = Expr.Const(loopName, Nil)
    val ty   = Expr.ForallE(Name.parse("x"), prop, prop, BinderInfo.Default)
    val body = Expr.Lam(Name.parse("x"), prop, Expr.App(self, Expr.BVar(0)), BinderInfo.Default)
    Environment.empty.addCore(
      ConstantInfo.DefnInfo(
        DefinitionVal(
          ConstantVal(loopName, Nil, ty), body,
          ReducibilityHints.Regular(1), DefinitionSafety.Safe, List(loopName)
        )
      )
    )

  test("exceeding the budget reports where the reduction went") {
    val tc = new TypeChecker(loopingEnv, KernelProfile.v4_35, DefinitionSafety.Safe,
                             LocalContext.empty, maxSteps = 5000L)
    val e  = Expr.App(Expr.Const(loopName, Nil), Expr.Sort(Level.zero))
    val ex = intercept[KernelException](tc.whnf(e))
    val msg = ex.reason
    assert(msg.contains("exceeded 5000 reduction steps"), clue(msg))
    // The point of the entry: it names the constant the search kept
    // reaching for. Whether it was re-derived is the misses column.
    assert(msg.contains("most attempted"), clue(msg))
    assert(msg.contains("slowAdd"), clue(msg))
    assert(msg.contains("delta attempts"), clue(msg))
    assert(msg.contains("cache misses"), clue(msg))
  }

  test("a default-budget run reports counters but no breakdown") {
    // The per-constant tables cost a HashMap pair per delta attempt, so they
    // are only kept when a budget was set and a report can actually print.
    val tc = new TypeChecker(Environment.empty, KernelProfile.v4_35)
    // Nothing has been reduced, so there is nothing to attribute.
    assert(!tc.work.contains("most attempted"), clue(tc.work))
    assert(tc.work.contains("is_def_eq calls: 0"), clue(tc.work))
  }

  test("the default budget is unchanged") {
    // A diagnostic flag must not quietly become a semantic one.
    assertEquals(new TypeChecker(Environment.empty).maxSteps, TypeChecker.defaultMaxSteps)
    assertEquals(new DeclarationChecker(KernelProfile.v4_35).maxSteps, TypeChecker.defaultMaxSteps)
  }

  test("the budget reaches an inductive block too") {
    // `--max-steps` is documented as per declaration, and an inductive block
    // is a declaration. AddInductive and InductiveChecker build their own
    // TypeCheckers, so the budget has to be forwarded or the flag does
    // nothing for exactly the kind of declaration it is wanted for.
    val prop = Expr.Sort(Level.Succ(Level.zero))
    val decl: Declaration.InductDecl = Declaration.InductDecl(
      levelParams = Nil, numParams = 0,
      types = List(InductiveType(Name.parse("Flag"), prop,
        List(Constructor(Name.parse("Flag.up"), Expr.Const(Name.parse("Flag"), Nil))))),
      isUnsafe = false
    )
    // A budget of one step cannot complete any derivation, so the guard must
    // fire from inside the inductive path rather than being ignored.
    val ex = intercept[KernelException](AddInductive.add(Environment.empty, decl, KernelProfile.v4_35, 1L))
    assertEquals(ex.kind, ExceptionKind.DeepRecursion, clue(ex.reason))
    assert(ex.reason.contains("exceeded 1 reduction steps"), clue(ex.reason))
  }
