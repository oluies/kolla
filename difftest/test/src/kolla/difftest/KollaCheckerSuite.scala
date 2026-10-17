package kolla.difftest

import cats.effect.IO
import kolla.kernel.*
import kolla.leanexport.*
import munit.CatsEffectSuite

class KollaCheckerSuite extends CatsEffectSuite:

  private def items(name: String): Vector[ExportItem] =
    val in = getClass.getResourceAsStream("/" + name)
    assert(in != null, s"missing test resource $name")
    val src = scala.io.Source.fromInputStream(in, "UTF-8")
    val lines = try src.getLines().toVector finally src.close()
    ExportReader.fromLines(lines).items

  private def run(file: String): IO[CheckerRun] =
    KollaChecker.check(items(file), KernelProfile.v4_35, "leanprover/lean4:v4.35.0", file)

  test("every declaration of a real export is accepted") {
    run("nat-add-3.1.0.ndjson").map { r =>
      assertEquals(r.errored, 0, clue(r.results.filter(_.verdict.isInstanceOf[Verdict.Error]).toString))
      assertEquals(r.rejected, 0, clue(r.results.filter(_.verdict.isInstanceOf[Verdict.Rejected]).toString))
      // Inductive blocks are now checked, not carried over.
      assertEquals(r.notChecked, 0)
      assertEquals(r.accepted, r.results.length)
      assert(r.results.length >= 17, clue(r.results.length))
      assert(r.wallNanos > 0L)
      assert(r.peakHeapBytes > 0L)
      assert(r.failure.isEmpty)
    }
  }

  test("the nested fixture is accepted, including its two extra recursors") {
    run("nested-3.1.0.ndjson").map { r =>
      assertEquals(r.rejected, 0, clue(r.results.filter(_.verdict.isInstanceOf[Verdict.Rejected]).map(_.name.toString).toString))
      assertEquals(r.errored, 0)
      val names = r.results.map(_.name.toString).toSet
      assert(names.contains("Tree.rec_1"), clue(names.toString.take(400)))
      assert(names.contains("RoseTree.rec_1"))
      assert(names.contains("EvenList.rec"))
    }
  }

  test("the quotient fixture is accepted") {
    run("quot-sound-3.1.0.ndjson").map { r =>
      assertEquals(r.rejected, 0)
      assertEquals(r.errored, 0)
      assert(r.results.map(_.name.toString).contains("Quot.lift"))
    }
  }

  test("a 3.0.0 export is accepted under the same profile") {
    run("nat-add-succ-3.0.0.ndjson").map { r =>
      assertEquals(r.rejected, 0)
      assertEquals(r.errored, 0)
      assert(r.results.map(_.name.toString).contains("Nat.add_succ"))
    }
  }

  test("a corrupted declaration is rejected, not an error, and carries a trace") {
    val base = items("nat-add-3.1.0.ndjson")
    // Replace the first definition's value with a nat literal.
    var replaced = false
    val mutated = base.map {
      case ExportItem.Info(ConstantInfo.DefnInfo(v)) if !replaced =>
        replaced = true
        ExportItem.Info(ConstantInfo.DefnInfo(v.copy(value = Expr.natLit(0))))
      case other => other
    }
    assert(replaced)
    KollaChecker.check(mutated, KernelProfile.v4_35, "t", "mutated").map { r =>
      assertEquals(r.errored, 0)
      assertEquals(r.errored, 0)
      val bad = r.results.filter(_.verdict.isInstanceOf[Verdict.Rejected])
      // The rejected declaration is carried into the environment with its
      // mutated value, so a later declaration that reduces through it fails
      // too. Those rejections are real, not artefacts.
      assert(bad.nonEmpty)
      assertEquals(bad.head.name, Name.parse("Nat.below"))
      assert(bad.head.trace.nonEmpty, "a rejection must carry the defeq trace")
      assert(bad.head.nanos > 0L)
    }
  }

  test("comparison mode stops at the first rejection, as lean4checker does") {
    val base = items("nat-add-3.1.0.ndjson")
    var replaced = false
    val mutated = base.map {
      case ExportItem.Info(ConstantInfo.DefnInfo(v)) if !replaced =>
        replaced = true
        ExportItem.Info(ConstantInfo.DefnInfo(v.copy(value = Expr.natLit(0))))
      case other => other
    }
    KollaChecker.check(
      mutated, KernelProfile.v4_35, "t", "mutated", stopOnFirstRejection = true
    ).map { r =>
      assertEquals(r.rejected, 1)
      // Everything after the rejection is not reached, so it cannot be mistaken
      // for agreement with a reference that aborted.
      assert(r.notChecked > 0)
      assertEquals(r.accepted + r.rejected + r.notChecked, r.results.length)
      val idx = r.results.indexWhere(_.verdict.isInstanceOf[Verdict.Rejected])
      assert(r.results.drop(idx + 1).forall(_.verdict.isInstanceOf[Verdict.NotChecked]))
      assert(clue(r.results.last.verdict.detail.getOrElse("")).contains("not reached"))
    }
  }

  test("comparison mode is unchanged when nothing is rejected") {
    KollaChecker.check(
      items("nat-add-3.1.0.ndjson"), KernelProfile.v4_35, "t", "clean", stopOnFirstRejection = true
    ).map { r =>
      assertEquals(r.rejected, 0)
      assertEquals(r.notChecked, 0)
      assertEquals(r.accepted, r.results.length)
    }
  }

  test("a malformed export is reported as a run failure, not a crash") {
    KollaChecker.checkFile(
      Layout.repoFile("build.mill"), KernelProfile.v4_35, "t", "bogus"
    ).map { r =>
      assert(r.failure.isDefined, clue(r.results.toString))
      assertEquals(r.results.length, 0)
    }
  }

  test("every declaration gets exactly one result") {
    run("nat-add-3.1.0.ndjson").map { r =>
      val names = r.results.map(_.name)
      assertEquals(names.distinct.length, names.length, clue(names.groupBy(identity).filter(_._2.length > 1).keys.toString))
    }
  }
