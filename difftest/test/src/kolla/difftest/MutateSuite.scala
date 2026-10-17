package kolla.difftest

import cats.effect.IO
import kolla.kernel.*
import kolla.leanexport.*
import munit.CatsEffectSuite

class MutateSuite extends CatsEffectSuite:

  private def items(name: String): Vector[ExportItem] =
    val in  = getClass.getResourceAsStream("/" + name)
    val src = scala.io.Source.fromInputStream(in, "UTF-8")
    val ls  = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(ls).items

  private lazy val base = items("nat-add-3.1.0.ndjson")

  private def check(v: Vector[ExportItem]): IO[CheckerRun] =
    KollaChecker.check(v, KernelProfile.v4_35, "t", "c", stopOnFirstRejection = true)

  test("the base export is accepted, so a rejection means the mutation caused it") {
    check(base).map(r => assertEquals(r.rejected, 0, clue(r.results.filter(!_.verdict.isJudgement).toString)))
  }

  test("mutations are deterministic from the seed") {
    MutationKind.values.foreach { k =>
      val a = Mutate(k, 42L, base)
      val b = Mutate(k, 42L, base)
      assertEquals(a.map(_.target), b.map(_.target), clue(k.toString))
      assertEquals(a.map(_.items), b.map(_.items), clue(k.toString))
      assertEquals(a.map(_.description), b.map(_.description), clue(k.toString))
    }
  }

  test("a different seed can select a different target") {
    val targets = (1L to 12L).flatMap(s => Mutate(MutationKind.ChangeUniverseLevel, s, base)).map(_.target).distinct
    assert(targets.length > 1, clue(targets.map(_.toString).toString))
  }

  test("every applicable mutation changes the export") {
    val ms = Mutate.generate(7L, base)
    assert(ms.nonEmpty)
    ms.foreach(m => assertNotEquals(m.items, base, clue(m.id)))
    // Each mutation names what it did and where.
    ms.foreach { m =>
      assert(m.description.nonEmpty, clue(m.id))
      assert(m.id.startsWith(m.kind.slug), clue(m.id))
    }
  }

  test("the corrupting mutations are rejected") {
    // These five change the meaning of the file and must be rejected.
    val corrupting = List(
      MutationKind.SwapConstructorIndices,
      MutationKind.ChangeUniverseLevel,
      MutationKind.AlterRecursorRuleRhs,
      MutationKind.RetypeAxiom
    )
    corrupting.traverseList { k =>
      Mutate(k, 5L, base) match
        case None => IO.pure(s"${k.slug}: not applicable")
        case Some(m) =>
          check(m.items).map { r =>
            assert(r.rejected >= 1, clue(s"${m.id}: ${m.description} was accepted"))
            s"${k.slug}: rejected"
          }
    }.map(rs => assert(rs.nonEmpty, clue(rs.toString)))
  }

  test("changing a definitional height changes no verdict") {
    // A reducibility hint only steers which side is unfolded first, so kolla
    // must not reject on the strength of one.
    Mutate(MutationKind.ChangeDefinitionalHeight, 3L, base) match
      case None => IO.pure(())
      case Some(m) =>
        check(m.items).map { r =>
          assertEquals(r.rejected, 0, clue(s"${m.description}: ${r.results.filter(_.verdict.isInstanceOf[Verdict.Rejected]).map(_.name.toString)}"))
        }
  }

  test("a diff round-trips a mutation") {
    val m = Mutate(MutationKind.RetypeAxiom, 11L, base)
      .orElse(Mutate(MutationKind.ChangeUniverseLevel, 11L, base))
      .getOrElse(fail("no applicable mutation"))
    val fmt     = ExportFormat.Ndjson("3.1.0")
    val baseL   = ExportWriter.toLines(ExportEnv(fmt, None, base), fmt)
    val mutL    = ExportWriter.toLines(ExportEnv(fmt, None, m.items), fmt)
    val patch   = Diff.unified(baseL, mutL)
    assert(patch.nonEmpty, "a mutation must produce a non-empty diff")
    assertEquals(Diff.apply(baseL, patch), mutL)
    // Replaying the diff reproduces the mutated items.
    assertEquals(ExportReader.fromLines(Diff.apply(baseL, patch)).items, m.items)
  }

  test("a diff of identical inputs is empty and applies cleanly") {
    val a = Vector("one", "two", "three")
    assertEquals(Diff.unified(a, a), "")
    assertEquals(Diff.apply(a, ""), a)
  }

  test("diff handles insertion, deletion and replacement") {
    val a = Vector("a", "b", "c", "d")
    List(
      Vector("a", "b", "c", "d", "e"),
      Vector("a", "c", "d"),
      Vector("a", "X", "c", "d"),
      Vector.empty[String],
      Vector("z")
    ).foreach { b =>
      val p = Diff.unified(a, b)
      assertEquals(Diff.apply(a, p), b, clue(s"patch for $b:\n$p"))
    }
  }

  extension [A](xs: List[A])
    private def traverseList[B](f: A => IO[B]): IO[List[B]] =
      xs.foldRight(IO.pure(List.empty[B]))((a, acc) => f(a).flatMap(b => acc.map(b :: _)))
