package kolla.difftest

/** When a non-zero exit from the reference is a verdict and when it is not. */
class Lean4CheckerSuite extends munit.FunSuite:

  /** A non-zero exit is only a rejection when `lean4checker` said so. */
  private def failed(stderr: String, stdout: String = ""): ProcResult =
    ProcResult(exitCode = 1, stdout = stdout, stderr = stderr, nanos = 1000L)

  test("a named problem is a rejection") {
    val r = failed("lean4checker found a problem in Init.Core\nuncaught exception: ...")
    assert(Lean4Checker.rejected(r))
  }

  test("the marker is accepted on stdout too") {
    assert(Lean4Checker.rejected(failed("", "lean4checker found a problem in Std.Data")))
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

  test("a missing binary or build is not a rejection") {
    assert(!Lean4Checker.rejected(failed("error: unknown executable lean4checker")))
    assert(!Lean4Checker.rejected(failed("error: no such file or directory")))
    assert(!Lean4Checker.rejected(failed("")))
  }
