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
    // The point of the entry: it names the constant it kept re-deriving.
    assert(msg.contains("most attempted"), clue(msg))
    assert(msg.contains("slowAdd"), clue(msg))
    assert(msg.contains("delta attempts"), clue(msg))
    assert(msg.contains("cache misses"), clue(msg))
  }

  test("the report is empty of unfoldings when nothing unfolded") {
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
