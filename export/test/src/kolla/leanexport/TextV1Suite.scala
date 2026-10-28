package kolla.leanexport

import kolla.kernel.*

/** Checking a text-v1 export, as distinct from reading one.
  *
  * `ExportReaderSuite` and `RoundTripSuite` cover the format's syntax. Nothing
  * covered what `Replay` does with it, and that is where its two bugs were:
  * `ExportItem.Decl`'s recover put nothing in the environment (P18), and
  * `DefnWithoutHints` reaches `DeclarationChecker.addDefinition` directly,
  * around `add` and `addInfo`, which is how it ended up sharing a time window
  * with whatever ran before it (S2).
  *
  * The format is the only one that goes around `addInfo`, so it is the only one
  * whose checking has to be pinned separately.
  */
class TextV1Suite extends munit.FunSuite:

  import Fixtures.*

  private val profile = KernelProfile.v4_35

  private def items(src: String): Vector[ExportItem] =
    val env = ExportReader.fromLines(src.linesIterator.toVector)
    assertEquals(env.format, ExportFormat.TextV1)
    env.items

  private def verdicts(xs: Vector[ExportItem], check: Name => Boolean = _ => true): Vector[(String, String)] =
    val replay = new Replay(profile, true, Replay.defaultHoistWindow, check)
    xs.foreach(replay.feed)
    replay.finish()
    val out = Vector.newBuilder[(String, String)]
    while replay.hasNext do
      val step = replay.next()
      step.names.foreach(n => out += ((n.toString, ReplayTally.label(step.outcome))))
    out.result()

  /** The details of every step, for pinning why something was rejected. */
  private def detailOf(xs: Vector[ExportItem]): Vector[String] =
    val replay = new Replay(profile, true, Replay.defaultHoistWindow, _ => true)
    xs.foreach(replay.feed)
    replay.finish()
    val out = Vector.newBuilder[String]
    while replay.hasNext do
      ReplayTally.detail(replay.next().outcome).foreach(out += _)
    out.result()

  private def environmentOf(xs: Vector[ExportItem], check: Name => Boolean): Environment =
    val replay = new Replay(profile, true, Replay.defaultHoistWindow, check)
    xs.foreach(replay.feed)
    replay.finish()
    while replay.hasNext do replay.next()
    replay.environment

  /** A text-v1 file with two definitions and nothing else. */
  private val twoDefinitions: Vector[ExportItem] =
    val a = Name.parse("A")
    val b = Name.parse("B")
    Vector(
      ExportItem.DefnWithoutHints(a, Nil, Expr.Sort(Level.Succ(Level.zero)), prop),
      ExportItem.DefnWithoutHints(b, Nil, Expr.Sort(Level.Succ(Level.zero)), Expr.Const(a, Nil))
    )

  test("a text-v1 definition is checked, not admitted") {
    assertEquals(verdicts(twoDefinitions), Vector(("A", "accepted"), ("B", "accepted")))

    // The point of "checked": a definition whose value does not have its
    // declared type is rejected. A path that admitted instead would accept it.
    val wrong = Vector(
      ExportItem.DefnWithoutHints(Name.parse("Wrong"), Nil, prop, Expr.Sort(Level.Succ(Level.zero)))
    )
    assertEquals(verdicts(wrong).map(_._2), Vector("rejected"))
  }

  test("a text-v1 definition left unselected is admitted and reported as such") {
    assertEquals(
      verdicts(twoDefinitions, _ => false),
      Vector(("A", "carried-over"), ("B", "carried-over"))
    )
    // And it is in the environment, so a later declaration can refer to it.
    val env = environmentOf(twoDefinitions, _ => false)
    assert(env.contains(Name.parse("A")), clue(env.names.toString))
    assert(env.contains(Name.parse("B")))
  }

  test("each text-v1 definition gets a time window of its own") {
    // The regression: `addDefinition` is reached around `add` and `addInfo`,
    // so it used to read a field whose default was the run's own, already
    // started limit, and every definition after the first shared one budget.
    // The interval is beyond reach, so only a checker's construction reads
    // the clock, and the count is what distinguishes one window from two.
    var reads = 0
    val clock = () => { reads += 1; 0L }
    val limit = new TypeChecker.TimeLimit(10000L * 1000000L, clock, Long.MaxValue)
    val replay = new Replay(profile, true, Replay.defaultHoistWindow, _ => true, None,
                            TypeChecker.defaultMaxSteps, Environment.empty, Some(limit))
    twoDefinitions.foreach(replay.feed)
    replay.finish()
    replay.next()
    val afterFirst = reads
    replay.next()
    assert(afterFirst >= 1, clue(afterFirst))
    assert(reads > afterFirst, clue(s"the second definition reused the first window: $reads"))
  }

  test("the quotient declaration is named, so a selector can reach it") {
    // It used to carry no names, and `Replay` asks whether any of a step's
    // names is selected: none of an empty list is, under any predicate. So a
    // text-format `#QUOT` always took the admit path, was reported with no
    // names at all, and when `Quot.add` threw there the `Try` swallowed it,
    // leaving `quotInitialized` false — which is P21's silent failure.
    assertEquals(
      Declaration.QuotDecl.declNames.map(_.toString),
      List("Quot", "Quot.mk", "Quot.lift", "Quot.ind")
    )
    val xs = Vector(ExportItem.Decl(Declaration.QuotDecl))
    val got = verdicts(xs)
    assertEquals(got.map(_._1), Vector("Quot", "Quot.mk", "Quot.lift", "Quot.ind"))
    // `add_quot` needs `Eq`, which an environment of one `#QUOT` has not got.
    // The point is that the failure is now a reported rejection rather than
    // nothing at all.
    assertEquals(got.map(_._2).distinct, Vector("rejected"))
    assert(detailOf(xs).exists(_.contains("'Eq'")), clue(detailOf(xs).toString))
  }

  test("an unselected quotient declaration is reported under its own names") {
    val xs = Vector(ExportItem.Decl(Declaration.QuotDecl))
    assertEquals(
      verdicts(xs, _ => false).map(_._1),
      Vector("Quot", "Quot.mk", "Quot.lift", "Quot.ind")
    )
  }

  test("a whole text-v1 file as the exporter writes it") {
    // The committed literal is a grammar exerciser rather than a coherent
    // environment: it declares an axiom and an inductive both named `Nat`, so
    // its verdicts are pinned as they are, not as a real export's would be.
    val xs  = items(textV1Literal)
    val got = verdicts(xs)
    // Eight, not four: the quotient declaration's own names are reported now.
    assertEquals(got.length, 8, clue(got.toString))
    assert(got.map(_._1).containsSlice(Vector("Quot", "Quot.mk", "Quot.lift", "Quot.ind")),
           clue(got.toString))
    // A text-format inductive reaches `DeclarationChecker.add`, which does not
    // derive recursors, so it cannot be checked at all (X4).
    assert(detailOf(xs).exists(_.contains("inductive declarations are not implemented")),
           clue(detailOf(xs).toString))
  }

  test("an unselected text-v1 inductive is admitted with its constructor and recursor") {
    // P18: `Decl`'s recover was `identity`, so the type, its constructors and
    // its recursor were all missing and every later reference was unknown.
    // `AddInductive.add` derives the recursor, which the file does not carry.
    val env = environmentOf(items(textV1Literal), _ => false)
    assert(env.contains(nat), clue(env.names.toString))
    assert(env.contains(zero))
    assert(env.contains(natRec), clue("the recursor is derived, not exported"))
  }
