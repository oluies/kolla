# What it costs

Measured on one host: Apple M-series, 48 GB, JDK 27, commit 2597da6. Every
figure is `/usr/bin/time -l` peak resident set size for the `cli.jvm` assembly,
not heap, so it includes the JVM itself.

## Corpora

| corpus | export | declarations | wall | peak RSS |
|---|---|---|---|---|
| `nat-add` fixture | 18 KB | 17 | 0.1s | — |
| `mathlib-sample` | 76 MB | 19,020 | 8.0s | — |
| `init` v4.35.0 | 330 MB | 59,349 | 47.7s | 1.19 GB |
| `std` v4.35.0 | 536 MB | 99,619 | 304.5s | — |
| `lean` v4.35.0 | 707 MB | 171,705 | 260.9s | 3.09 GB |

The rows without a resident figure were run through `difftest`, which reports
peak heap instead: 0.69 GB for `mathlib-sample`, 2.74 GB for `init`, 3.77 GB
for `std`, 5.09 GB for `lean`. Those runs read the whole file into a `Vector`;
the two `cli` rows stream it. `init` is the pair to compare, 2.74 GB of heap
against 1.19 GB resident, and `lean` 5.09 GB against 3.09 GB.

## What scales with what

Streaming bounds what the driver holds, not what the reader holds. An export
refers to expressions by index, so every expression stays reachable while a
later line might name it. The interning tables are therefore the floor, and
they scale with distinct expressions rather than with declarations.

A Mathlib-based project is bigger than anything in the table. One trivial
module importing Mathlib exported 6.26 GB, 110,906,882 lines, 712,261
declarations and 105.9M expression interning entries. That is 8.8x `lean` by
bytes and 4.1x by declarations, so expect something in the region of 13-27 GB
depending on which of the two the tables follow — this has not been measured
and the range is an extrapolation, not a result.

Before streaming it could not be read at all: `cli` folded the file into one
`String`, and a 6.26 GB file exceeds both the maximum byte array and twice that
again once decoded to UTF-16. The run timed out with no output.

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

## Profiles are not equal

The v4.35 kernel keeps a positive `is_def_eq` cache and earlier releases do
not, so kolla does not either below v4.35. `std` costs 304.5s and 3.77 GB of
heap on the v4_35 profile and exhausts a 24 GB heap after 55 minutes on v4_27.
`lean4checker` checks the same modules at v4.28.0 in 74s and 1.1 GB resident
with no positive cache of its own, so the gap is kolla's. See
docs/semantics.md P12.
