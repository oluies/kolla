# Comparing kolla's kernel with Lean's, comparison by comparison

Two kernels can agree on every verdict and still take different paths to it.
This compares the paths. Both kernels hash, per declaration, the sequence of
`is_def_eq_core` entries (depth, head and argument count of each side), results
and `unfold_definition_core` calls, and the hashes are joined by name.

An inductive block is one entry, under the name of its first type. Its hash
covers the comparisons and unfoldings its check makes and what it produces:
each type, constructor and recursor with their arities and flags, and each
recursor rule's right-hand side, spelled in one canonical form both patches
implement (binder names and info and `mdata` left out, levels and names in
full). Recursors are taken in name order so that neither kernel's internal
order matters.

docs/semantics.md K28, K29, K31, K32 and K33 are what it found.

## Lean's side

Apply `lean-kdigest.patch` to a checkout of Lean at the tag of the export
(v4.35.0 here) and build it: `cmake --preset release; make -C build/release -j`.

    LEAN_KDIGEST=lean.kd build/release/stage1/bin/leanchecker --fresh Std

Do not run it under `lake env`, which puts the official toolchain's libraries
first on `DYLD_LIBRARY_PATH`. For a module outside the toolchain, Mathlib say,
set `LEAN_PATH` to what `lake env printenv LEAN_PATH` prints in that project
instead; the patched build is the same commit as the release, so it reads the
project's oleans. `LEAN_KD_NAMES=<file>` with `LEAN_KD_DUMP=<file>` also writes
the events of the named declarations. `LEAN_KTRACE=<n>` prints the first n
events to stderr instead.

Keep the checkout and its build somewhere durable. macOS removes files under
`/tmp` that have not been read for three days, and a Lean build is 20 minutes
on a fast machine.

## kolla's side

Apply `kolla-kdigest.patch`, which is not for committing, and build
`cli.jvm.assembly`. The export must carry `mdata`, or the two kernels are given
different terms:

    lean4export Std --export-mdata > std.export
    KOLLA_KDIGEST=kolla.kd java -Xmx4g -jar out.jar -q std.export

`KOLLA_KD_NAMES` and `KOLLA_KD_DUMP` are the dump, as on Lean's side. The
digest is kept per thread, so `--jobs` is fine for the hashes and makes the
Mathlib side a 12-minute run; a dump, though, interleaves lines from different
workers in one file, so take dumps with one job. The dump also carries `#`
lines naming each phase of an inductive block's check, which are not hashed;
strip them before `firstdiff.py` if the other side has none.

## Comparing

    python3 -I join.py lean.kd kolla.kd          # how many differ, and the worst
    python3 -I firstdiff.py lean.dump kolla.dump # group by first differing event
    python3 -I context.py lean.dump kolla.dump <name> <index> [width]
