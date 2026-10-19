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

## As a library

**Nothing is published yet.** `repo1.maven.org` has no `kolla-kernel_3`, there
is no release tag, and the release workflow has never run, so a dependency on a
Central coordinate does not resolve today. To depend on kolla now, build it
locally:

```bash
./mill kernel.jvm.publishM2Local     # also export.jvm, dsl.jvm
```

and take the dependency from your own `~/.m2`. `kernel`, `export` and `dsl` are
the three that publish; `cli` and `web` are programs and `difftest` is a test
harness. When a release does happen the coordinates will be
`io.github.oluies::kolla-kernel`, `::kolla-export` and `::kolla-dsl`, at the
version in `publishVersion`.

`docs/build.md` has the release path, the three workflow modes, and why there is
no cross-build over Scala versions: Scala 3 reads the TASTy of earlier 3.x
releases, so a consumer on 3.10 can use an artifact built with the pinned
3.9.0.

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
  --defeq-cache   keep the positive is_def_eq cache on a profile that
                  predates it; needed for a library corpus before v4.35
  --trace         name each declaration before checking it, so one that
                  never finishes can be identified
  --eval <term>   reduce a term against the export's environment and print
                  it, instead of checking the file
  --profiles      list the profiles and exit
  -h, --help      this message
  --version       the version and the default profile
```

`-` reads standard input. Exit code 0 means every declaration was accepted, 1
that one was rejected, 2 that the file could not be read — an unreadable file
is not a proof of anything — and 3 that kolla ran out of memory before
reaching a verdict, which a script can retry with more room.

### What a green run means

Every declaration was re-derived, inductive blocks included. A block is added
through `AddInductive` and then checked against what the file claimed by
`InductiveChecker.validate`, so its constructors and recursors are not taken on
trust. The summary counts say so for themselves, and the one to read is
`carried over`: it is the number of declarations the file supplied and the
kernel did not re-derive, and on `init`, `std`, `lean` and the mathlib sample it
is zero.

Two qualifications, both visible in the output rather than only here.

A declaration is carried over rather than checked when the file presents a
constructor or a recursor detached from its own inductive block, since a rule's
right-hand side may call a sibling recursor and cannot be checked one entry at a
time. A well-formed lean4export file never does this, which is why the count is
zero above; if it is not zero, that many declarations were admitted on the
file's word. `--check` and `--cache` also move declarations out of `accepted`,
into `carried over` and `cached` respectively, and both print their own count.

How much is checked depends on the profile, because Lean's kernel changed. The
extra `check_recursors` pass — each generated recursor's type, and each
computation rule checked to be type-preserving — exists from v4.35 and is gated
on `KernelProfile.checkRecursors`, so a run on an older profile does not perform
it, exactly as that release did not. The profile is named in every summary line
for this reason.

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

## Reducing a term

`--eval` type-checks a term against an export's environment and reduces it,
which is `#eval` for the part of it the kernel can do:

```
$ kolla --profile v4.35.0 --eval 'Nat.add 2 3' init.export
5 : Nat
$ kolla --profile v4.35.0 --eval 'Nat.decEq 2 2' init.export
Decidable.intro (Eq.{1} Nat 2 2) Bool.true (Eq.refl.{1} Nat 2) : Decidable (Eq.{1} Nat 2 2)
```

It is reduction and not execution. Arithmetic is native and fast; strings
reduce only by unfolding and are impractical; nothing reduces under a binder;
and the environment is admitted rather than checked, which the command says on
stderr. A Lean program in the sense of `main : IO Unit` cannot be run this way,
because `IO` bottoms out in `@[extern]` primitives the kernel sees as constants
with no definition. docs/semantics.md D13 has the detail.

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

### A library corpus before v4.35 needs `--defeq-cache`

Lean added a positive `is_def_eq` cache in v4.35, and kolla follows the release,
so `v4.25.0` and `v4.27.0` do without one. At library scale that is the
difference between slow and unfinishable:

| corpus | profile | result |
|---|---|---|
| `init` | v4.27.0 | 51,759 accepted, 127s, 1.10 GB |
| `init` | v4.27.0 `--defeq-cache` | 51,759 accepted, 95s, 1.65 GB |
| `std` | v4.27.0 | no verdict; exceeds a 24 GB heap after 55 minutes |
| `std` | v4.35.0 | 99,619 accepted, 305s, 3.8 GB |

`--defeq-cache` keeps the cache on a profile that predates it. It is an
optimisation and not a change of profile: an entry is written only where
`is_def_eq` already answered true. On the `init` export above, the two runs
agree name by name and verdict by verdict across all 51,759 declarations, and
`DefEqCacheEquivalenceSuite` requires the same of every fixture on both uncached
profiles. The profile is reported as `v4.27.0+defeq-cache` so a summary never
claims to be a plain run of that release.

Without the flag, kolla says so before starting rather than after failing — an
export over 128 MB on an uncached profile prints the advice and names the flag.
The remaining cost is concentrated in one declaration,
`Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift`; docs/semantics.md
P12 has the isolation and K18 the cache.

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
every push, and a job per toolchain. `nightly.yml` runs the libraries and the
mathlib sample, on request rather than on a schedule: it costs hours of runner
time whether or not anything changed. Below v4.35 it passes `--defeq-cache`,
without which `std` and `lean` do not finish; that changes no verdict and the
profile reports itself as `+defeq-cache` so a report cannot be mistaken for a
plain run of the release (docs/semantics.md P20).

A reference that reaches no verdict — one that timed out, or that has no
release for the toolchain — is reported as such and does not fail the run. It
also does not confirm anything, so a comparison is only evidence when it says
`agrees`; see docs/semantics.md P17.

### What it has found

At v4.35.0, every declaration of four corpora was accepted, with an independent
checker accepting each of the same four export files:

| corpus | declarations | reference |
|---|---|---|
| `init` | 59,349 | nanoda |
| `std` | 99,619 | nanoda |
| `lean` | 171,705 | nanoda |
| `mathlib-sample` | 19,020 | nanoda |

A full Mathlib export is a different matter, and the honest answer is split.
Reading one is routine: module `Mathlib` at v4.35.0 is 6.26 GB and 729,263
declarations, and kolla reads and admits all of them in 83 seconds and 9.40 GB.
Checking them is not: a full check stops making progress 325,090 declarations
in, on `CategoryTheory.Localization.Monoidal.braidingNatIso`, with memory to
spare. docs/scale.md has the figures and docs/semantics.md K19 the two
declarations of that shape on record, one of them explained.

`init` at v4.28.0 adds 51,759 more against `lean4checker`. Read that precisely:
both references report one verdict for a whole file, so the agreement is at file
granularity. Only the comparison of kolla's own four builds is declaration by
declaration.

Two kernel bugs came out of it, neither of which the unit suites reached:
the kernel's literal extensions refer to constants that are not syntactic
dependencies, so an export can declare them after their first use
(docs/semantics.md P10); and a nested inductive's recursor took its major
premise from the block's head rather than from its own type, which falsely
rejected 9 declarations (K17).

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
needs Playwright. `docs/build.md` covers the Scala version pin, the Scala.js
linker failure behind it, and publishing.

## What it costs

`docs/scale.md` has measured wall times and peak memory per corpus, what a
Mathlib-scale export costs, and why a pre-v4.35 profile costs more.

## Authors

Örjan Lundberg and
[Anthony Lundberg](https://www.linkedin.com/in/anthony-lundberg2/).

## Licence

Apache-2.0, the licence Lean 4 and nanoda_lib use. See `LICENSE`.

---

kolla — Örjan Lundberg and
[Anthony Lundberg](https://www.linkedin.com/in/anthony-lundberg2/)
