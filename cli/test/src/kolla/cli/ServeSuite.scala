package kolla.cli

import cats.effect.IO
import kolla.kernel.*
import kolla.leanexport.*
import munit.CatsEffectSuite

class ServeSuite extends CatsEffectSuite:

  private val prop: Expr  = Expr.Sort(Level.zero)
  private val type0: Expr = Expr.Sort(Level.Succ(Level.zero))

  private def axiom(name: String, tpe: Expr): ExportItem =
    ExportItem.Info(ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse(name), Nil, tpe), isUnsafe = false)))

  private def defn(name: String, tpe: Expr, value: Expr): ExportItem =
    ExportItem.Info(
      ConstantInfo.DefnInfo(
        DefinitionVal(
          ConstantVal(Name.parse(name), Nil, tpe), value,
          ReducibilityHints.Abbrev, DefinitionSafety.Safe, List(Name.parse(name))
        )
      )
    )

  /** Serialized rather than fed as items, so the suite drives the same reader
    * the protocol does and runs on the native build too.
    */
  private def ndjson(items: Vector[ExportItem]): String =
    val sb = new StringBuilder
    new ExportWriter(ExportFormat.Ndjson("3.1.0"), s => { sb ++= s; sb += '\n' })
      .write(ExportEnv(ExportFormat.Ndjson("3.1.0"), None, items))
    sb.result()

  // Q refers to P, so its axiom closure has something in it.
  private val baseItems: Vector[ExportItem] =
    Vector(axiom("P", prop), defn("Q", prop, Expr.Const(Name.parse("P"), Nil)))
  private val goodItems: Vector[ExportItem] = baseItems :+ defn("R", type0, prop)
  private val badItems: Vector[ExportItem]  = baseItems :+ defn("Broken", prop, type0)

  private val files: Map[String, String] = Map(
    "base" -> ndjson(baseItems),
    "good" -> ndjson(goodItems),
    "bad"  -> ndjson(badItems)
  )

  private def bytes(name: String): fs2.Stream[IO, Byte] =
    files.get(name) match
      case Some(text) => fs2.Stream.emits(text.getBytes("UTF-8")).covary[IO]
      case None       => fs2.Stream.raiseError[IO](new RuntimeException(s"no such file '$name'"))

  private val start = Serve.State(KernelProfile.default, Environment.empty, TypeChecker.defaultMaxSteps, 0L)

  private def ask(state: Serve.State, line: String): IO[(Serve.State, String, Boolean)] =
    Serve.handle(state, line, bytes).map { (s, out, go) =>
      (s, out.getOrElse(fail(s"'$line' produced no reply")), go)
    }

  private def loaded: IO[Serve.State] = ask(start, "load base").map(_._1)

  test("an operation and its argument split at the first space") {
    assertEquals(Serve.split("status"), ("status", ""))
    assertEquals(Serve.split("  axioms   Nat.add_comm  "), ("axioms", "Nat.add_comm"))
    assertEquals(Serve.split("eval Nat.add 2 3"), ("eval", "Nat.add 2 3"))
    assertEquals(Serve.split(""), ("", ""))
  }

  test("the delta is what the base does not already hold") {
    loaded.map { s =>
      val d = Serve.delta(s.env)
      assert(!d(Name.parse("P")), clue("P is in the base"))
      assert(d(Name.parse("R")), clue("R is not"))
    }
  }

  test("a load keeps the environment it built") {
    for (s, out, go) <- ask(start, "load base")
    yield
      assert(go)
      assert(out.contains("\"accepted\":2"), clue(out))
      assert(out.contains("\"ok\":true"), clue(out))
      assertEquals(s.declarations, 2)
  }

  test("a check reports only what the base did not hold, and keeps nothing") {
    for
      base        <- loaded
      (s, out, _) <- ask(base, "check good")
    yield
      assert(out.contains("\"accepted\":1"), clue(out))
      assert(out.contains("\"carriedOver\":2"), clue(out))
      // The candidate's R is checked against the base and then dropped.
      assertEquals(s.declarations, 2)
      assert(!s.env.contains(Name.parse("R")))
  }

  test("a rejected candidate is answered, not fatal, and leaves the base alone") {
    for
      base         <- loaded
      (s, out, go) <- ask(base, "check bad")
      (_, after, _) <- ask(s, "status")
    yield
      assert(go, clue("the session stays open"))
      assert(out.contains("\"ok\":false"), clue(out))
      assert(out.contains("\"rejected\":1"), clue(out))
      assertEquals(s.declarations, 2)
      assert(after.contains("\"declarations\":2"), clue(after))
  }

  test("a file that cannot be read is answered, not fatal") {
    for (s, out, go) <- ask(start, "load nope")
    yield
      assert(go)
      assert(out.contains("\"ok\":false"), clue(out))
      assertEquals(s.declarations, 0)
  }

  test("axioms and type answer from the resident environment") {
    for
      base          <- loaded
      (_, ax, _)    <- ask(base, "axioms Q")
      (_, tpe, _)   <- ask(base, "type Q")
      (_, miss, _)  <- ask(base, "axioms Nope")
    yield
      assert(ax.contains("\"axioms\":[\"P\"]"), clue(ax))
      assert(tpe.contains("\"type\":\"Sort 0\""), clue(tpe))
      assert(miss.contains("\"ok\":false"), clue(miss))
  }

  test("an operation with no argument, and an unknown one, are answered") {
    for
      (_, noArg, go1)   <- ask(start, "axioms")
      (_, noFile, go2)  <- ask(start, "load")
      (_, unknown, go3) <- ask(start, "frobnicate x")
    yield
      assert(go1 && go2 && go3, clue("none of them ends the session"))
      assert(noArg.contains("needs a name"), clue(noArg))
      assert(noFile.contains("needs a file"), clue(noFile))
      assert(unknown.contains("unknown operation"), clue(unknown))
  }

  test("a blank line is not a request") {
    Serve.handle(start, "   ", bytes).map { (s, out, go) =>
      assertEquals(out, None)
      assertEquals(s.served, 0L)
      assert(go)
    }
  }

  test("quit ends the session") {
    for (_, out, go) <- ask(start, "quit")
    yield
      assert(!go)
      assert(out.contains("\"ok\":true"), clue(out))
  }

  test("standard input is the protocol, so it is not an export") {
    for (_, out, go) <- ask(start, "load -")
    yield
      assert(go)
      assert(out.contains("\"ok\":false"), clue(out))
  }

  test("a seeded replay refuses a digest cache") {
    val seeded = Environment.empty.addCore(
      ConstantInfo.AxiomInfo(AxiomVal(ConstantVal(Name.parse("P"), Nil, prop), isUnsafe = false))
    )
    intercept[IllegalArgumentException] {
      new Replay(KernelProfile.default, true, Replay.defaultHoistWindow, _ => true,
                 Some(new ReplayCache {
                   def contains(d: Digest): Boolean = false
                   def accepted(d: Digest): Unit    = ()
                 }), TypeChecker.defaultMaxSteps, seeded)
    }
  }
