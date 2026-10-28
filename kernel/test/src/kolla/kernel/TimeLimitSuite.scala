package kolla.kernel

/** The wall-clock budget, with a clock the suite controls.
  *
  * `TimeLimit` takes its clock rather than naming one, so none of this depends
  * on how long anything actually takes.
  */
class TimeLimitSuite extends munit.FunSuite:

  /** A clock that stands still until it is moved, or ticks on every read. */
  private class Fake(perRead: Long = 0L):
    var nanos: Long = 0L
    var reads: Int  = 0
    val now: () => Long = () => { reads += 1; val t = nanos; nanos += perRead; t }

  private val prop: Expr  = Expr.Sort(Level.zero)
  private val type0: Expr = Expr.Sort(Level.Succ(Level.zero))

  private val natDecl: Declaration.InductDecl =
    val nat = Name.parse("Nat")
    Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(nat, Expr.Sort(Level.one), List(
        Constructor(Name.parse("Nat.zero"), Expr.const(nat)),
        Constructor(Name.parse("Nat.succ"),
          Expr.ForallE(Name.mkSimple("n"), Expr.const(nat), Expr.const(nat), BinderInfo.Default))
      ))),
      false
    )

  private def limit(ms: Long, c: Fake, every: Long = 1L): TypeChecker.TimeLimit =
    new TypeChecker.TimeLimit(ms * 1000000L, c.now, every)


  test("a limit has to be positive, and so does its interval") {
    val c = new Fake
    intercept[IllegalArgumentException](new TypeChecker.TimeLimit(0L, c.now))
    intercept[IllegalArgumentException](new TypeChecker.TimeLimit(-1L, c.now))
    intercept[IllegalArgumentException](new TypeChecker.TimeLimit(1L, c.now, 0L))
  }

  test("the start is read once when the checker is built") {
    val c = new Fake
    new TypeChecker(Environment.empty, timeLimit = Some(limit(10, c)))
    assertEquals(c.reads, 1)
  }

  test("a clock that stands still never exceeds the budget") {
    val c  = new Fake
    val tc = new TypeChecker(Environment.empty, timeLimit = Some(limit(1, c)))
    assertEquals(tc.check(type0), Expr.Sort(Level.Succ(Level.Succ(Level.zero))))
  }

  test("a clock past the budget ends the declaration, and says so") {
    val c  = new Fake
    val tc = new TypeChecker(Environment.empty, timeLimit = Some(limit(5, c)))
    c.nanos = 5L * 1000000L
    val e = intercept[KernelException](tc.check(type0))
    assertEquals(e.kind, ExceptionKind.DeepRecursion)
    assert(e.getMessage.contains("exceeded the 5 ms budget"), clue(e.getMessage))
    // The report is what makes the budget useful rather than just a stop.
    assert(e.getMessage.contains("is_def_eq calls"), clue(e.getMessage))
  }

  test("just under the budget is not over it") {
    val c  = new Fake
    val tc = new TypeChecker(Environment.empty, timeLimit = Some(limit(5, c)))
    c.nanos = 5L * 1000000L - 1L
    assertEquals(tc.check(type0), Expr.Sort(Level.Succ(Level.Succ(Level.zero))))
  }

  test("the clock is read every `every` steps and not oftener") {
    val c  = new Fake
    val tc = new TypeChecker(Environment.empty, timeLimit = Some(limit(10, c, every = 1000000L)))
    val before = c.reads
    tc.check(type0)
    // One read at construction, none after: the declaration is far short of
    // the interval, which is why the default has to be smaller than a
    // declaration costs.
    assertEquals(c.reads, before)
  }

  test("no limit means the clock is never consulted") {
    val c  = new Fake
    val tc = new TypeChecker(Environment.empty)
    tc.check(type0)
    assertEquals(c.reads, 0)
  }

  test("milliseconds above the bound would wrap, so the bound is stated") {
    val c = new Fake
    assertEquals(TypeChecker.maxTimeMillis, Long.MaxValue / 1000000L)
    // Just inside is a legal limit; the caller is expected to refuse above it
    // rather than multiply, since the product wraps silently.
    new TypeChecker.TimeLimit(TypeChecker.maxTimeMillis * 1000000L, c.now)
    assert(TypeChecker.maxTimeMillis * 1000000L > 0L)
    assert((TypeChecker.maxTimeMillis + 1L) * 1000000L < 0L, clue("the next one wraps"))
  }

  test("one window covers every checker built from the same limit") {
    // The scope of a budget is the scope of its instance: an inductive block
    // builds more than twenty checkers and must not restart for each.
    val c     = new Fake(perRead = 1000000L)
    val bound = limit(5, c)
    val a     = new TypeChecker(Environment.empty, timeLimit = Some(bound))
    val b     = new TypeChecker(Environment.empty, timeLimit = Some(bound))
    assertEquals(c.reads, 1, clue("the second checker did not restart the window"))
    assert(a != null && b != null)
    // A fresh one opens a new window.
    new TypeChecker(Environment.empty, timeLimit = Some(bound.fresh()))
    assertEquals(c.reads, 2)
  }

  test("an inductive block opens one window, not one per checker") {
    // `InductiveChecker.tc` is a `def` and `AddInductive` builds two more, so
    // the clock used to be read once per checker and the budget restarted
    // every time. With the interval set beyond reach, no step reads the
    // clock, so what is left to count is the constructions.
    val c = new Fake
    // One limit for the run, as `Replay` holds it.
    val run = new TypeChecker.TimeLimit(10000L * 1000000L, c.now, Long.MaxValue)
    AddInductive.add(Environment.empty, natDecl, KernelProfile.default,
                     TypeChecker.defaultMaxSteps, Some(run))
    assertEquals(c.reads, 1, clue("the block restarted its window"))

    // And the next block opens its own: a run-long window would be as wrong
    // as a per-checker one, since the bound is per declaration.
    AddInductive.add(Environment.empty, natDecl, KernelProfile.default,
                     TypeChecker.defaultMaxSteps, Some(run))
    assertEquals(c.reads, 2, clue("the second block reused the first window"))
  }

  test("every public entry point opens its own window") {
    // The hole this closes: Replay checks a text-v1 definition by calling
    // addDefinition directly, around add and addInfo, and the window used to
    // come from a field whose default was the run's own already-started limit.
    val prop = Expr.Sort(Level.zero)
    def cv(n: String) = ConstantVal(Name.parse(n), Nil, prop)

    def readsFor(f: (DeclarationChecker, Environment) => Environment): Int =
      val c  = new Fake
      val dc = new DeclarationChecker(
        KernelProfile.default, TypeChecker.defaultMaxSteps,
        Some(new TypeChecker.TimeLimit(10000L * 1000000L, c.now, Long.MaxValue))
      )
      val e1 = f(dc, Environment.empty)
      val after1 = c.reads
      f(dc, e1)
      c.reads - after1

    // Each call opens a window of its own, so each reads the clock again.
    assert(readsFor((dc, e) => dc.addAxiom(e, AxiomVal(cv(s"A${e.size}"), isUnsafe = false))) >= 1)
    // `D : Type := Prop`, so the value's type is the declared one.
    val type0 = Expr.Sort(Level.Succ(Level.zero))
    assert(readsFor { (dc, e) =>
      val n = Name.parse(s"D${e.size}")
      dc.addDefinition(e, DefinitionVal(ConstantVal(n, Nil, type0), prop,
                                        ReducibilityHints.Abbrev, DefinitionSafety.Safe, List(n)))
    } >= 1)
    assert(readsFor((dc, e) =>
      dc.addInfo(e, ConstantInfo.AxiomInfo(AxiomVal(cv(s"I${e.size}"), isUnsafe = false)))._1) >= 1)
  }

  test("each declaration opens its own window") {
    // One limit for the run, a fresh window per declaration: otherwise the
    // budget would be spent by whichever declaration came first.
    val c  = new Fake
    val dc = new DeclarationChecker(
      KernelProfile.default, TypeChecker.defaultMaxSteps,
      Some(new TypeChecker.TimeLimit(10000L * 1000000L, c.now, Long.MaxValue))
    )
    val prop = Expr.Sort(Level.zero)
    val env1 = dc.addInfo(Environment.empty,
      ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("P"), Nil, prop), isUnsafe = false)))._1
    val reads1 = c.reads
    dc.addInfo(env1,
      ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("R"), Nil, prop), isUnsafe = false)))
    assert(reads1 >= 1, clue(reads1))
    assert(c.reads > reads1, clue(s"the second declaration reused the first window: ${c.reads}"))
  }

  test("the budget reaches an inductive block, which has its own checkers") {
    val c = new Fake
    val nat = Name.parse("Nat")
    val decl: Declaration.InductDecl = natDecl
    // Clean under a clock that does not move.
    assert(AddInductive.add(Environment.empty, decl, KernelProfile.default,
                            TypeChecker.defaultMaxSteps, Some(limit(10, c))).env.contains(nat))
    // A clock that ticks a millisecond per read, since the checkers here are
    // built inside `add` and each reads the clock when it starts.
    val c2 = new Fake(perRead = 1000000L)
    val e = intercept[KernelException](
      AddInductive.add(Environment.empty, decl, KernelProfile.default,
                       TypeChecker.defaultMaxSteps, Some(limit(5, c2)))
    )
    assert(e.getMessage.contains("exceeded the 5 ms budget"), clue(e.getMessage))
  }
