package kolla.difftest

/** When a non-zero exit from the reference is a verdict and when it is not. */
class Lean4CheckerSuite extends munit.FunSuite:

  /** A non-zero exit is only a rejection when `lean4checker` said so. */
  private def failed(stderr: String, stdout: String = ""): ProcResult =
    ProcResult(exitCode = 1, stdout = stdout, stderr = stderr, nanos = 1000L)

  test("a kernel rejection is a rejection, whichever path printed it") {
    // The multi-module path prints this marker...
    assert(Lean4Checker.rejected(failed("lean4checker found a problem in Init.Core")))
    // ...and a single module run with --fresh rethrows instead. This is the
    // real output from the negative corpora, which P19's first attempt
    // misread as a failure to run.
    assert(
      Lean4Checker.rejected(
        failed(
          "uncaught exception: (kernel) declaration type mismatch, 'kollaFalse' has type\n" +
            "  Prop\nbut it is expected to have type\n  False"
        )
      )
    )
  }

  test("a toolchain that would not download is not a rejection") {
    // The v4.28.0 CI failure: reported as
    // "DISAGREES (lean4checker rejected vs kolla accepted)" when elan had
    // simply failed to fetch the release. See docs/semantics.md P19.
    val r = failed(
      "info: downloading https://releases.lean-lang.org/lean4/v4.28.0/lean-4.28.0-linux.tar.zst\n" +
        "error: could not download file\ninfo: caused by: error during download"
    )
    assert(!Lean4Checker.rejected(r))
  }

  test("a missing toolchain, binary or file is not a rejection") {
    assert(!Lean4Checker.rejected(failed("error: toolchain 'leanprover/lean4:v4.28.0' is not installed")))
    assert(!Lean4Checker.rejected(failed("error: unknown executable lean4checker")))
    assert(!Lean4Checker.rejected(failed("error: no such file or directory")))
    assert(!Lean4Checker.rejected(failed("lake: command not found")))
  }

  test("an unrecognised failure defaults to a rejection") {
    // Deliberate: a wrong "rejection" shows up as a disagreement someone
    // investigates, where a wrong "no verdict" silently drops the comparison.
    assert(Lean4Checker.rejected(failed("")))
    assert(Lean4Checker.rejected(failed("something nobody has seen before")))
  }
