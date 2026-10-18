# kolla

A type checker for the [Lean 4](https://lean-lang.org) kernel, written in
Scala 3 and cross-built for the JVM, Scala.js and Scala Native.

It reads [lean4export](https://github.com/leanprover/lean4export) files and
re-derives every declaration in them: no elaborator, no surface syntax, no
tactics. What it accepts is meant to be what Lean's own kernel accepts, and the
differential platform exists to hold it to that.

```
mill cli.jvm.run path/to/export.ndjson
```

## Modules

| module | platforms | what it is |
|---|---|---|
| `kernel` | JVM, JS, Native | names, levels, expressions, the type checker, inductives |
| `export` | JVM, JS, Native | the export-file reader and writer, and `Replay` |
| `dsl` | JVM, JS, Native | term builders and the `lean"..."` interpolator |
| `cli` | JVM, Native | the command line |
| `web` | JS | the browser page |
| `difftest` | JVM | the differential platform |

The checking itself is `kolla.leanexport.Replay`, a pure stepper shared by all
three frontends; they differ only in how they interleave its steps — a fiber
yield, an animation frame, a blocking loop.

## The command line

```
kolla [options] <export-file>...

  --profile <v>   the Lean release to check as (default the newest)
  --json          one JSON object per declaration on stdout
  --abort         stop at the first rejection
  --only <name>   report only this declaration, repeatable
  --check <pre>   check only declarations under this name prefix,
                  admitting the rest unchecked; repeatable
  -v, --verbose   name each declaration as it is checked
  -q, --quiet     only the counts and the verdict
  --progress      note declarations and bytes read on stderr
  --cache <file>  reuse and extend a file of accepted digests
  --profiles      list the profiles and exit
```

`-` reads standard input. Exit code 0 means every declaration was accepted, 1
that one was rejected, 2 that the file could not be read — an unreadable file
is not a proof of anything — and 3 that kolla ran out of memory before
reaching a verdict, which a script can retry with more room.

The file is checked as it is read, so a large export is never materialised;
`docs/semantics.md` P13 covers what that costs the hoisting pass. `--check`
suits a project with a few declarations of its own on top of a large library:
it admits everything outside the prefix into the environment unchecked and
reports how many, so the verdict covers the selection rather than the file
(P14). `--only` filters the report instead, and changes no checking.

`--cache` keys each declaration by a digest of itself and of everything it
depends on, so a rerun skips what has not changed and a run that dies partway
keeps the digests it had already accepted. Reusing an entry is trusting it; the
file is part of what the verdict rests on, which is why it is opt-in. See
docs/semantics.md P15.

`mill cli.native.nativeLink` builds a native binary. It is the faster of the two
on small inputs and much the slower on large ones; see docs/semantics.md F7.

## The browser

`mill web.js.bundle` produces a directory to serve. The page is built by
`kolla.web.Layout` rather than written as markup, so the element ids the checker
writes to are the ones that exist. Nothing leaves the page.

## Kernel profiles

Lean's kernel is not behaviourally stable across releases, so kolla checks
*as* a release rather than in general. `KernelProfile` pins the differences —
the string-literal constructor, whether `is_prop` normalises, the `Nat` size
cap, bounded projection indices, the extra inductive checks, which structures
eta, and the positive defeq cache. docs/semantics.md K1 has the matrix with
source references.

An export is accepted under its own profile and generally rejected under the
others, which is the signal the profiles are there for.

## The differential platform

`difftest` runs kolla against other checkers and against kolla's own builds.

```
mill difftest.run list                      # toolchains and corpora
mill difftest.run provision --toolchain v4.35.0
mill difftest.run run --toolchain v4.35.0   # check and compare
mill difftest.run platforms                 # jvm vs native vs js vs browser
mill difftest.run mutants                   # the negative corpus
```

- **References.** `lean4checker` replays oleans through Lean's own kernel;
  `nanoda_lib` reads the same export files kolla does. Both report one verdict
  per module, so they are compared at corpus level. Each is pinned to an exact
  revision: a reference built from the wrong source is not a reference.
- **Corpora.** Handwritten cases under `difftest/cases/`, negative cases under
  `difftest/cases-negative/` that the kernel must reject, the committed exports
  under `difftest/test/resources/`, the `init`, `std` and `lean` libraries, and
  a sample of mathlib.
- **Positive and negative.** A corpus Lean itself accepted must be accepted in
  full, which is a reference in its own right. A negative corpus must have
  something rejected. Both are checked.
- **Mutants.** Deterministic corruptions of an export — swapped constructor
  indices, altered recursor rules, retyped axioms — which must be rejected, and
  a changed definitional height, which must not. Credit is given only for
  rejections the unmutated corpus did not already have.
- **Platforms.** The JVM, native and browser builds are compared declaration by
  declaration through one JSON wire format. A count would hide two platforms
  rejecting different declarations and reaching the same total.

`.github/workflows/ci.yml` runs the unit suites and the platform comparison on
every push, and a job per toolchain; `nightly.yml` runs the libraries and the
mathlib sample.

## docs/semantics.md

Every place where the behaviour was not obvious from the specification is
recorded there with a reference into Lean's source: name, level, expression and
declaration semantics, the export formats, the kernel, the DSL, the differential
platform and the frontends. When kolla and Lean disagreed, that file says which
one is right and why.

## Building

Mill, pinned by `.mill-version`; `./mill` bootstraps it.

```
./mill __.compile
./mill __.test
```

Scala Native needs clang and the usual native toolchain; the browser smoke test
needs Playwright.

## What it costs

`docs/scale.md` has measured wall times and peak memory per corpus, what a
Mathlib-scale export costs, and why a pre-v4.35 profile costs more.

## Licence

Apache-2.0, the licence Lean 4 and nanoda_lib use. See `LICENSE`.
