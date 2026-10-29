# What it costs

Measured on one host: Apple M-series, 48 GB, JDK 27. Every figure is
`/usr/bin/time -l` peak resident set size for the `cli.jvm` assembly, not heap,
so it includes the JVM itself, and every size is decimal GB.

The commit matters, because the flags did not all exist at once. The `init`,
`std` and `lean` rows are from 2597da6. The Mathlib rows are from 009ed9b:
`--cache` arrives in 0af1260 and the digest memoisation in c40e06f, and before
that last one a Mathlib run stalled at 150,036 declarations whatever the flags
(docs/semantics.md P16), so none of the Mathlib figures is reproducible at
2597da6.

## Corpora

| corpus | export | declarations | wall | peak RSS |
|---|---|---|---|---|
| `nat-add` fixture | 18 KB | 17 | 0.1s | — |
| `mathlib-sample` | 76 MB | 19,020 | 8.0s | — |
| `init` v4.35.0 | 330 MB | 59,349 | 47.7s | 1.19 GB |
| `std` v4.35.0 | 536 MB | 99,619 | 304.5s | — |
| `lean` v4.35.0 | 707 MB | 171,705 | 260.9s | 3.09 GB |
| `std` v4.28.0 on v4_27, `--defeq-cache` | 492 MB | 87,309 | 322.4s | 5.63 GB |
| `Mathlib` v4.35.0, read and admitted | 6.26 GB | 729,263 | 83.0s | 9.40 GB |
| `Mathlib` v4.35.0, same with `--cache` | 6.26 GB | 729,263 | 80.5s | 14.36 GB |
| `Mathlib` v4.35.0, fully checked | 6.26 GB | 729,263 in the file | no verdict | — |
| `Mathlib` v4.35.0, `--check Nat.Prime` | 6.26 GB | 120 of 729,263 | 199.6s | 8.13 GB |
| `Mathlib` v4.35.0, same with a warm `--cache` | 6.26 GB | 120 cached | 149.7s | 11.89 GB |
| `exact_count_and_sat` statement, v4.35.0 | 73.6 MB | 17,669 | 21.0s | 3.30 GB |
| `exact_count_and_sat` proof, v4.34.1 on v4_27, `--defeq-cache` | 2.36 GB | 95,176 | 2,773.8s | 24.45 GB |

`mathlib-sample` and `std` carry no resident figure because they were run
through `difftest`, which reports peak heap instead: 0.69 GB and 3.77 GB, with
2.74 GB for `init` and 5.09 GB for `lean`. Those runs read the whole file into
a `Vector`; every `cli` row streams it. `init` is the pair to compare, 2.74 GB
of heap against 1.19 GB resident, and `lean` 5.09 GB against 3.09 GB.

The fully-checked Mathlib row is neither: it is a `cli` run against a 24 GB
heap that never reached a verdict, so there is no total to quote. Its
declaration count is the file's, not a count of what was checked — the run
stopped after 325,090 of them.

## One theorem out of a real development

The two `exact_count_and_sat` rows are the largest single verdict kolla has
reached, and the only one where the whole closure of one claimed theorem was
checked rather than a library prefix. They come from `openai/math`, whose
`lean/docs/378.md` says Lean proves the Exponential Time Hypothesis is false.

The repository states its results twice. `ComparatorChallenges/*.lean` holds
the statements — all 418 of those files end in `sorry`, by design, because each
challenge's JSON names a separate `solution_module` that is supposed to prove
it. The statement row above is that file: 17,669 declarations, all accepted,
resting on `sorryAx`, which is what `--axioms` is for.

The proof row is the solution module. Getting to it cost more than checking it:
16.4 hours to compile the 3,091 modules its imports reach, against 46.2 minutes
to check the 2.36 GB export they produce. It came out at 95,176 accepted, none
rejected, resting on exactly `propext`, `Classical.choice` and `Quot.sound` —
the three the challenge's `permitted_axioms` allows, so
`--require-axioms propext,Classical.choice,Quot.sound` exits 0.

Two qualifications belong with that number. It was checked under `v4_27`,
because `KernelProfile.forToolchain` maps the repository's v4.34.1 to the
newest profile at or below it and there is no v4.34 profile; the kernel
behaviours exercised are therefore the pre-4.35 ones (K1). And the export came
from `lean4export`'s v4.34.0 tag built against v4.34.1, since no revision of
that repository pins v4.34.1 — the built binary's own metadata was checked to
report `4.34.1` before it was used.

24.45 GB of resident set for one theorem is the figure to carry forward: the
cost is the closure, not the file, and a library's worth of Mathlib comes along
with it.

## Per frontend

The figures above are `cli.jvm`. The four frontends do not cost the same.

| frontend | measured on | cost |
|---|---|---|
| `cli.jvm` | `init`, `lean` | 1.19 GB / 47.7s and 3.09 GB / 260.9s |
| `difftest` (JVM) | `init`, `std`, `lean`, `mathlib-sample` | 2.74-5.09 GB of heap, materialised |
| `cli.native` | `init`, `std`, `mathlib-sample`, the case corpora | `init` 434.4s, 12.79 GB resident and 36.69 GB of footprint; `std` no verdict |
| `web` (Node, browser) | handwritten fixtures only | not measured at library scale |

Two of those rows need qualifying rather than quoting.

The `cli.native` row is measured rather than inferred, and it needs its metric
read carefully. `/usr/bin/time -l` reports a resident set and a peak footprint;
for the JVM they nearly coincide, and for the native binary they differ by a
factor of three because Immix commits far more than stays resident. The 51.6 GB
this file used to quote was a footprint, so comparing it with a resident set
makes the improvement look four times larger than it is. On its own metric
`init` went 51.6 GB to 36.69 GB, with the time from about 13 minutes to 7.2.

51.6 GB was also the host rather than the demand: this machine has 51.54 GB,
and `std` reaches a 51.60 GB footprint and then fails with
`[ScalaNative GC|Error] Out of heap space grow heap` after 44.2 minutes, at
17.95 GB resident. So `std` still produces no verdict on native, as it did not
before, and the reason is the collector refusing to grow rather than the
machine dying. docs/semantics.md F7 has both metrics for every corpus and the
bracket on where native stops being the faster frontend.

`web` is not run on a library corpus at all. The browser takes its input
through a textarea, which is already slow at the 2.2 MB fixture, and a 330 MB
export is not something a page is handed. Node could take one, and has not been
tried. Neither is a gap in the kernel: all four frontends agree declaration by
declaration on the committed fixtures, which is what the platform checks them
for.

## What scales with what

Streaming bounds what the driver holds, not what the reader holds. An export
refers to expressions by index, so every expression stays reachable while a
later line might name it. The interning tables are therefore the floor, and
they scale with distinct expressions rather than with declarations.

## Mathlib

This was an extrapolation of 13-27 GB until it was measured, and the
extrapolation was wrong: reading the whole of Mathlib costs 9.40 GB, below the
bottom of that range. The numbers below replace it.

Exporting module `Mathlib` at v4.35.0 gives 6,258,342,501 bytes — 6.26 GB —
over 110,895,826 lines and 729,263 declarations. `lean4export` itself takes
26.3 minutes and peaks at 12.51 GB, which a user pays before kolla sees
anything.

Reading and admitting all 729,263 of them takes 83.0s and 9.40 GB. That is the
floor for any run over this file: the export names expressions by index, so the
reader's interning tables have to stay reachable, and no amount of streaming
avoids them. `--cache` adds 4.96 GB and no measurable time.

Checking them is another matter, and the cost is concentrated rather than
spread. Traced, 105 of the first 225,053 declarations took over a second each
and accounted for 973 seconds — about half the elapsed time — the slowest
finishing one being 133 seconds. The run then stops making progress on

    IntermediateField.restrictScalars_top

with resident near 4 GB of a 20 GB ceiling, so it is time rather than memory.

So kolla reads a Mathlib export comfortably and does not finish checking one.
An earlier draft of this named a different declaration, identified from a
progress counter that only reports every 25000 declarations; see
docs/semantics.md K19 for why that was not an identification at all.

Before streaming none of this was reachable: `cli` folded the file into one
`String`, and a 6.26 GB file exceeds both the maximum byte array and twice that
again once decoded to UTF-16. The run timed out with no output.

## A project with its own declarations

`--check <prefix>` is the shape a downstream project needs: a handful of
declarations of its own on top of a library it did not write. Measured on the
Mathlib export with `Nat.Prime` standing in for such a module — 120 of 729,263
declarations selected, the other 729,143 admitted:

| run | result | wall | peak RSS |
|---|---|---|---|
| cold, writing a cache | 120 accepted | 199.6s | 8.13 GB |
| warm, reusing it | 120 cached | 149.7s | 11.89 GB |

A quarter off, not more, because reading and digesting 6.26 GB is most of the
work and a warm run still has to do it. Both figures are post-P21: before that
fix the same selection reported two rejections, and widening it reported 79,
all false.

Choosing the prefix matters. An earlier attempt used `Real.log`, which selects
Mathlib's own definition rather than a leaf lemma, and did not finish at all —
a reminder that "my declarations" and "a declaration I named" are not the same
thing.

## Checking less

`--check <prefix>` admits everything outside the prefix unchecked, which is
what a downstream project with a handful of its own declarations wants. On
`init` v4.35.0:

| run | declarations checked | wall |
|---|---|---|
| whole file | 59,349 | 47.7s |
| `--check Nat` | 2,707 | 4.3s |

The remaining 56,642 are reported as admitted unchecked on stderr. A verdict
under `--check` covers the selection and not the file; see docs/semantics.md
P14.

## Checking again

`--cache <file>` keys each declaration by a digest of itself and everything it
depends on. On `init` v4.35.0, 59,349 declarations:

| run | result | wall |
|---|---|---|
| no cache | 59,349 accepted | 47.7s |
| cold, writing the cache | 59,349 accepted | 96.0s |
| warm, reusing it | 59,349 cached | 26.7s |

The cache file holds 57,919 digests for 59,349 declarations, because an
inductive block is one step and its names share a digest.

A warm run is not free: the file still has to be read and digested to establish
that it is the same file, and the digest is a second walk over every
expression, which is why the cold run costs about double. The gain therefore
follows how much of a run is checking rather than parsing — about half for
`init`, and far more for a corpus where single declarations are expensive.

## Profiles are not equal

The v4.35 kernel keeps a positive `is_def_eq` cache and earlier releases do
not, so kolla does not either below v4.35. `std` costs 304.5s and 3.77 GB of
heap on the v4_35 profile and exhausts a 24 GB heap after 55 minutes on v4_27.
`lean4checker` checks the same modules at v4.28.0 in 74s and 1.1 GB resident
with no positive cache of its own, so the gap is kolla's. See
docs/semantics.md P12.

---

kolla — Örjan Lundberg and
[Anthony Lundberg](https://www.linkedin.com/in/anthony-lundberg2/)
