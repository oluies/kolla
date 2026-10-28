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

  test("the budget reaches an inductive block, which has its own checkers") {
    val c = new Fake
    val nat = Name.parse("Nat")
    val decl: Declaration.InductDecl = Declaration.InductDecl(
      Nil, 0,
      List(InductiveType(nat, Expr.Sort(Level.one), List(
        Constructor(Name.parse("Nat.zero"), Expr.const(nat)),
        Constructor(Name.parse("Nat.succ"),
          Expr.ForallE(Name.mkSimple("n"), Expr.const(nat), Expr.const(nat), BinderInfo.Default))
      ))),
      false
    )
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
