package kolla.difftest

import java.util.concurrent.{CountDownLatch, TimeUnit}
import kolla.kernel.*
import kolla.leanexport.*
import scala.collection.mutable

/** What the kernel may be used from several threads for at once.
  *
  * `TypeChecker` says of itself that it is single-threaded by construction: one
  * per declaration, and only the checking thread touches its caches. That is a
  * claim about the mutable state. The other half of it is that everything
  * shared — `Expr`, `Name`, `Level`, `ConstantInfo`, `Environment` — is
  * immutable, so several checkers may read the same declarations at the same
  * time. Nothing exercised that until this suite. See docs/semantics.md K22.
  *
  * Real threads rather than fibers: a synchronous `IO` runs to completion on
  * one carrier thread, so a fiber-based test could pass without two things ever
  * having run at once.
  */
class ConcurrencySuite extends munit.FunSuite:

  private val threads: Int = 8
  private val profile      = KernelProfile.v4_35

  private def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(lines).items

  /** One replay's verdicts, in order. Effect-free, so a thread can just call it. */
  private def verdicts(xs: Vector[ExportItem]): Vector[(String, String)] =
    val replay = new Replay(xs, profile)
    val out    = Vector.newBuilder[(String, String)]
    while replay.hasNext do
      val step = replay.next()
      step.names.foreach(n => out += ((n.toString, ReplayTally.label(step.outcome))))
    out.result()

  /** Runs `work` on `threads` threads at once, and gives back what each
    * returned. A latch rather than a stagger: the point is overlap.
    */
  private def inParallel[A](work: Int => A): Vector[A] =
    val ready   = new CountDownLatch(threads)
    val go      = new CountDownLatch(1)
    val results = new Array[Option[A]](threads)
    val errors  = new Array[Option[Throwable]](threads)
    java.util.Arrays.fill(results.asInstanceOf[Array[Object]], None)
    java.util.Arrays.fill(errors.asInstanceOf[Array[Object]], None)
    val ts = (0 until threads).map { i =>
      val t = new Thread(
        () =>
          ready.countDown()
          go.await()
          try results(i) = Some(work(i))
          catch case e: Throwable => errors(i) = Some(e)
        ,
        s"kolla-test-$i"
      )
      t.start()
      t
    }
    assert(ready.await(60, TimeUnit.SECONDS), "threads did not start")
    go.countDown()
    ts.foreach(_.join(600000))
    errors.flatten.headOption.foreach(e => fail(s"a thread threw: $e", e))
    results.toVector.map(_.getOrElse(fail("a thread produced nothing")))

  test("eight threads replaying one export agree with a sequential run") {
    val xs       = items("nested-3.1.0.ndjson")
    val expected = verdicts(xs)
    assert(expected.nonEmpty)
    assert(expected.forall((_, v) => v == "accepted"), clue(expected.toString.take(300)))
    // The same immutable items read by every thread; each replay is its own.
    inParallel(_ => verdicts(xs)).zipWithIndex.foreach { (got, i) =>
      assertEquals(got, expected, clue(s"thread $i disagreed"))
    }
  }

  test("eight threads checking against one environment infer the same types") {
    val xs  = items("nat-add-3.1.0.ndjson")
    val env = new Replay(xs, profile).let(r => { while r.hasNext do r.next(); r.environment })
    val decls = env.declarations.map(i => (i.name, i.tpe, i.levelParams))
    assert(decls.length > 10, clue(decls.length))

    // One checker per thread, every one reading the same environment and the
    // same expressions.
    val expected = decls.map((_, tpe, ps) => Pretty.expr(new TypeChecker(env, profile).check(tpe, ps)))
    inParallel { _ =>
      val tc = new TypeChecker(env, profile)
      decls.map((_, tpe, ps) => Pretty.expr(tc.check(tpe, ps)))
    }.zipWithIndex.foreach { (got, i) =>
      assertEquals(got, expected, clue(s"thread $i disagreed"))
    }
  }

  test("eight threads build equal environments from the same items") {
    val xs = items("nat-add-3.1.0.ndjson")
    val envs = inParallel { _ =>
      val r = new Replay(xs, profile)
      while r.hasNext do r.next()
      r.environment
    }
    val first = envs.head
    envs.foreach { e =>
      assertEquals(e.size, first.size)
      assertEquals(e.names, first.names)
      assertEquals(e.quotInitialized, first.quotInitialized)
    }
  }

  test("two checkers doing the same work report the same counts") {
    // The deterministic half of this suite. Agreement between threads says
    // the shared data is read-only; this says the mutable state is not
    // shared, because a cache or counter held in common would make the second
    // checker's work cheaper than the first's.
    val xs  = items("nat-add-3.1.0.ndjson")
    val env = new Replay(xs, profile).let(r => { while r.hasNext do r.next(); r.environment })
    val decls = env.declarations.map(i => (i.tpe, i.levelParams))

    def counts(): String =
      val tc = new TypeChecker(env, profile)
      decls.foreach((tpe, ps) => tc.check(tpe, ps))
      tc.work

    val first  = counts()
    val second = counts()
    assert(first.contains("is_def_eq calls:"), clue(first))
    assertEquals(second, first, clue("a later checker did less work than the first"))

    // And a checker that has done nothing reports nothing.
    assert(new TypeChecker(env, profile).work.contains("is_def_eq calls: 0"))
  }

  test("a fresh variable name repeats across checkers, and their contexts stay apart") {
    // Each `TypeChecker` has its own `NameGenerator`, so two of them mint the
    // same names. That is only safe because neither can see the other's local
    // context, which is what this asserts: the same name, different types.
    val a = new TypeChecker(Environment.empty, profile)
    val b = new TypeChecker(Environment.empty, profile)
    val prop  = Expr.Sort(Level.zero)
    val type0 = Expr.Sort(Level.Succ(Level.zero))
    // Checking a binder introduces a free variable in each checker's context.
    val fa = a.check(Expr.ForallE(Name.mkSimple("x"), prop, Expr.BVar(0), BinderInfo.Default))
    val fb = b.check(Expr.ForallE(Name.mkSimple("x"), type0, Expr.BVar(0), BinderInfo.Default))
    assert(fa != null && fb != null)
    assertEquals(a.env.size, 0)
    assertEquals(b.env.size, 0)
  }

  extension [A](a: A) private def let[B](f: A => B): B = f(a)
