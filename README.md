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

`.claude/skills/` holds two skills for an agent driving kolla:
[`kolla-serve`](.claude/skills/kolla-serve/SKILL.md) for checking candidates
against a resident kernel, and
[`kolla-audit`](.claude/skills/kolla-audit/SKILL.md) for finding out what a
declaration rests on.

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
  --max-steps <n> reduction budget per declaration; on exceeding it the
                  kernel reports where the reduction went
  --max-time <ms> wall-clock budget per declaration, with the same report;
                  independent of --max-steps
  --axioms <name> report the axioms this declaration rests on, and whether
                  it was left as sorry; repeatable
  --eval <term>   reduce a term against the export's environment and print
                  it, instead of checking the file
  --serve         keep the environment and answer requests on stdin:
                  load, check, axioms, type, eval, status, quit
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

### Memory, and the native binary

The checker holds little. On the v4.35.0 `std` export, 99,619 declarations,
the live heap is about 185 MB, and the JVM build checks it with `-Xmx512m` in
270 seconds against 254 with `-Xmx28g`. A large resident figure from
the JVM is headroom it was allowed to take, not what the check requires. A
larger corpus needs more, so measure before reading a resident figure as the
requirement.

`mill cli.native.nativeLink` builds a native binary. It is the faster of the two
on small inputs and much the slower on large ones, and with the default `immix`
collector it does not finish `std`: it runs out of heap at a 51.6 GB footprint.
Built with `nativeGC = "boehm"` and started with a heap near what the run needs,
it does:

| corpus | native, `boehm` | wall | resident | JVM |
|---|---|---|---|---|
| `init` | `GC_INITIAL_HEAP_SIZE=4G` | 208–218s | 4.9–5.2 GB | 48s |
| `std` | `GC_INITIAL_HEAP_SIZE=8G` | 1,919s | 9.16 GB | 254s |

Size the initial heap to the corpus rather than generously: `std` at 16G took
3,058 seconds. `boehm` with its default heap hung on 2 of 15 `init` runs; none of
10 with a 4 GB start did. For a library corpus the JVM is still the build to use.
docs/semantics.md F7 has the measurements, including the `commix` and `immix`
failures and what was ruled out.

Why `immix` needs so much is reproduced without kolla in
`repro/immix-recycle/`, a single scala-cli file. A long-lived structure built
among short-lived garbage pins immix's 256-byte lines: 30 MB of retained nodes
needs a 512 MB heap rather than 48 MB. Idle threads raise that further,
because each collection hands reclaimed blocks to every thread in turn: 2 GB
with 16 idle threads. A cats-effect program has an idle compute pool by
default, which is how kolla meets it. Fresh allocations of 8 KiB or more add a
full collection each time one does not fit.

## Finding a slow declaration

`--trace` names each declaration on stderr before checking it, and reports any
step that took over a second. The first part is the one that matters: a
declaration that does not terminate is reported only by its start line, so the
last unpaired name is the one a run is inside. A progress counter cannot tell
you that, and neither can a thread dump — these steps do not reach a safepoint,
so `jstack`, `jcmd` and `SIGQUIT` are all refused.

That is how the Mathlib tail was measured and how the declaration a full check
stops on was identified; docs/semantics.md K19 records both, including an
earlier wrong answer that came from reading an exact position off a counter
that only reports every 25000 declarations.

`--max-steps <n>` goes a layer deeper. The kernel reports where a reduction
went when it exceeds the budget — `is_def_eq` calls, how many were answered by
identity or by the cache, delta attempts against cache misses, and the
most-attempted constants — which is the only moment a check that does not
finish says anything. On the declaration above it names `Set.ofPred`,
`Set.range` and their typeclass projections, and shows that the cost is the
search rather than the unfolding: 128 delta cache misses in 17.8 million
attempts. docs/semantics.md K21 has the figures and two readings the numbers
refuted.

## What a theorem rests on

Type-checking says a declaration follows from what the file declared. It does
not say what the file declared — and `sorry` elaborates to the `sorryAx` axiom,
so a theorem with no proof type-checks exactly like one with a proof.
`--axioms` reports the difference:

```
$ kolla --profile v4.35.0 --axioms Classical.em init.export
Classical.em rests on 3 axiom(s), reached through 120 constant(s)
  Classical.choice  (Lean's trust base)
  Quot.sound  (Lean's trust base)
  propext  (Lean's trust base)

$ kolla --profile v4.35.0 --axioms sorryAx init.export
sorryAx rests on 1 axiom(s), reached through 4 constant(s)
  sorryAx  <- NOT A PROOF: left as sorry
```

Exit 0 when nothing unusual, 1 when a declaration rests on `sorryAx` or on an
axiom outside the three Lean ships, 2 when the name is not in the file. A
verdict outranks a misspelling: 1 wins over 2.

`--require-axioms propext,Classical.choice,Quot.sound` replaces that judgement
with a set you state, and an empty list permits nothing. "Nothing unusual" says
depending on Lean's three axioms is unremarkable, which is true of ordinary
mathematics and not something to assume on a caller's behalf;
`ComparatorChallenges/*.json` states its `permitted_axioms` for the same
reason. docs/semantics.md S3. The point is dependencies: a `sorry` in the
declaration you are reading is visible in the source, and one in a dependency
is not — nor is either, when all you have is an export. docs/semantics.md A1.

## Answering many questions

Every mode above builds an environment, answers one question and throws it
away, and the environment is what costs: 90 seconds for `init`, 83 seconds to
read and admit Mathlib. `--serve` keeps it and takes requests on standard
input, one per line, replying with one JSON object per line.

```
$ kolla --profile v4.35.0 --serve
load .difftest/leanprover-lean4-v4.35.0/init.export
{"op":"load","ok":true,"file":"...","accepted":59349,"rejected":0,"carriedOver":0,"errored":0,"declarations":59349,"ms":82815}
check .difftest/leanprover-lean4-v4.35.0/case-natlit.export
{"op":"check","ok":true,"file":"...","accepted":11,"rejected":0,"carriedOver":320,"errored":0,"declarations":59349,"ms":17}
axioms Classical.em
{"op":"axioms","ok":true,"result":{"declaration":"Classical.em","axioms":["Classical.choice","Quot.sound","propext"],"sorry":false,"unusual":[],"profile":"v4.35.0"},"constants":120,"ms":6}
eval Nat.add 2 3
{"op":"eval","ok":true,"partial":false,"result":{"eval":"Nat.add 2 3","value":"5","type":"Nat","profile":"v4.35.0"},"ms":2}
```

The operations are `load`, `check`, `axioms`, `type`, `eval`, `deadline`,
`status` and `quit`. A file named on the command line is preloaded, so `kolla
--serve init.export` answers immediately.

`gate <name> <a,b,c>` answers whether a declaration rests on anything outside
the set you name, which is the criterion a comparator challenge states; an
empty set permits nothing. `names <prefix>`, `mentions <name>` and `unfold
<name>` read the environment, answering what you would otherwise go back to
Lean for — `mentions` scans every declaration's references, so it costs 2.2
seconds over `init` and proportionally more on a library.

`deadline <ms>` bounds each declaration by the clock, and `deadline 0` removes
it. A caller cannot convert reduction steps into milliseconds, which is what
`--max-steps` offers, so this is the budget it can actually state. Every reply
carries `reason`: the first declaration that did not pass, with what stopped
it, so a budget that runs out names the constant the reduction was in rather
than only adding to a count. docs/semantics.md S2.

Two skills in `.claude/skills/` describe this for an agent driving kolla rather
than a person reading a manual: `kolla-serve` is the session — the requests, the
deadline, and how to read a reply — and `kolla-audit` is what a declaration
rests on and why grepping for `sorry` is not the same question. A coding agent
with that directory on its path picks them up by name.

`check` is the one an iterating caller wants: it checks only the declarations
the base does not already hold and keeps nothing, so a candidate costs its own
declarations rather than the library's. `load` is the same check and keeps what
it built, and only if every declaration in it was accepted — a rejected one is
still carried into the environment a replay returns (P6), and keeping that
would leave the base resting on something the kernel refused. The reply says
`kept` either way.

Discarding is sound rather than careful: `Environment` is immutable, so a
rejected candidate has nothing to leave behind. A failed request is answered
with `"ok": false` and the session goes on. docs/semantics.md S1.

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
| `std` | v4.27.0 `--defeq-cache` | 87,309 accepted, 322s, 5.63 GB |
| `std` | v4.35.0 | 99,619 accepted, 305s, 3.8 GB |

`--defeq-cache` keeps the cache on a profile that predates it, and on `std` it
is the difference between a verdict and none. It is an optimisation and not a
change of profile: an entry is written only where
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
Checking them is not. The cost is concentrated in a thin tail: 105 of the first
225,053 declarations take over a second each and account for about half the
elapsed time, the slowest finishing one at 133 seconds, and the run stops making
progress on `IntermediateField.restrictScalars_top` with memory to spare.
docs/scale.md has the figures and docs/semantics.md K19 the distribution.

One theorem out of a real development has also been checked end to end:
`openai/math`'s claimed proof that the Exponential Time Hypothesis is false.
Compiling the 3,091 modules it imports took 16.4 hours of Lean; checking the
2.36 GB export they produce took 46.2 minutes and 24.45 GB, and came out at
95,176 declarations accepted, none rejected, resting on exactly `propext`,
`Classical.choice` and `Quot.sound` — the three that challenge's
`permitted_axioms` allows. The statement file beside it rests on `sorryAx`,
which is what `--axioms` is for. docs/scale.md has both and the qualifications.

`init` at v4.28.0 adds 51,759 more against `lean4checker`. Read that precisely:
both references report one verdict for a whole file, so the agreement is at file
granularity. Only the comparison of kolla's own four builds is declaration by
declaration.

Four bugs came out of it, none of which the unit suites reached.

Two in the kernel: the literal extensions refer to constants that are not
syntactic dependencies, so an export can declare them after their first use
(docs/semantics.md P10); and a nested inductive's recursor took its major
premise from the block's head rather than from its own type, which falsely
rejected 9 declarations (K17).

Two in the frontends, both found by pointing the tools at something large. The
content digest behind `--cache` walked a declaration's term graph structurally,
which is exponential in the sharing an export produces, so a Mathlib run
stopped dead and every run paid for a digest nothing had asked for (P16). And
admitting the quotient package with `addCore` left `quotInitialized` unset, so
`--check` and `--eval` built environments with quotient reduction switched off
and rejected declarations Lean accepts — 79 of them on one Mathlib closure,
all false (P21). Mathlib reaches quotients almost at once, because `Multiset`
is `Quotient (List.Perm)` and `Finset` wraps it.

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
