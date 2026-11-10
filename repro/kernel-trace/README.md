# Comparing kolla's kernel with Lean's, comparison by comparison

Two kernels can agree on every verdict and still take different paths to it.
This compares the paths. Both kernels hash, per declaration, the sequence of
`is_def_eq_core` entries (depth, head and argument count of each side), results
and `unfold_definition_core` calls, and the hashes are joined by name.
docs/semantics.md K28, K29 and K31 are what it found.

## Lean's side

Apply `lean-kdigest.patch` to a checkout of Lean at the tag of the export
(v4.35.0 here) and build it: `cmake --preset release; make -C build/release -j`.

    LEAN_KDIGEST=lean.kd build/release/stage1/bin/leanchecker --fresh Std

Do not run it under `lake env`, which puts the official toolchain's libraries
first on `DYLD_LIBRARY_PATH`. `LEAN_KD_NAMES=<file>` with `LEAN_KD_DUMP=<file>`
also writes the events of the named declarations. `LEAN_KTRACE=<n>` prints the
first n events to stderr instead.

## kolla's side

Apply `kolla-kdigest.patch`, which is not for committing, and build
`cli.jvm.assembly`. The export must carry `mdata`, or the two kernels are given
different terms:

    lean4export Std --export-mdata > std.export
    KOLLA_KDIGEST=kolla.kd java -Xmx4g -jar out.jar -q std.export

`KOLLA_KD_NAMES` and `KOLLA_KD_DUMP` are the dump, as on Lean's side.

## Comparing

    python3 -I join.py lean.kd kolla.kd          # how many differ, and the worst
    python3 -I firstdiff.py lean.dump kolla.dump # group by first differing event
    python3 -I context.py lean.dump kolla.dump <name> <index> [width]
