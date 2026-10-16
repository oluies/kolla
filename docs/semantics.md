# Kernel semantics decisions

Reference implementation: `leanprover/lean4` at tag `v4.35.0`. Line numbers below refer
to that tag. The files consulted are `src/kernel/*`, `src/Lean/Level.lean`,
`src/Lean/Expr.lean`, `src/util/name.cpp` and `src/include/lean/lean.h`.

## Names

### N1 — numeral components are arbitrary precision

`Name.num`'s index is a `Nat` in Lean (`src/kernel/declaration.h` uses `name` from
`src/util/name.h`, whose numeral limbs are `Nat`). `kolla` stores it as `BigInt`.

### N2 — total order on names

`Name.compare` mirrors `lean::name::cmp_core` (`src/util/name.cpp:191`): components are
compared from the outermost prefix inwards, numeral components sort before string
components, and a proper prefix sorts before the longer name.

String components are compared with `String.compareTo` (UTF-16 code units) where Lean uses
`std::string::operator<` (UTF-8 bytes). The two orders differ only for supplementary-plane
characters. The order is used only to sort the arguments of `max` inside
`Level.normalize`; equivalent inputs still normalize to identical levels under either
order, so `Level.isEquiv` and `Level.geq` are unaffected.

### N3 — hash values differ from Lean's

The hash mixer is Lean's `lean_uint64_mix_hash` (`src/include/lean/lean.h:2293`) and the
per-constructor tags are Lean's (`Name` 1723; `Level` 2221/2237/2239/2243/2251/2267;
`Expr` 3/5/7/11/13/17 and the depth-mixed binder/app cases). String and `Nat` leaf hashes
use `scala.util.hashing.MurmurHash3` rather than Lean's `hash_str` and `Nat.hash`, so the
resulting hash values are not Lean's. Hashes are used only as cache keys and as an
equality short-circuit.

## Levels

### L1 — depth

`depth(zero) = depth(param) = depth(mvar) = 0`, `depth(succ u) = depth(u) + 1`,
`depth(max u v) = depth(imax u v) = max(depth u, depth v) + 1`
(`src/Lean/Level.lean:98`). `lean::mk_max` compares depths to pick between two explicit
levels (`src/kernel/level.cpp:81`), and `lean::operator==` uses depth as a short-circuit,
so the definition is load-bearing.

### L2 — raw versus smart constructors

`Level.Max` and `Level.IMax` are `lean::mk_max_core` and `lean::mk_imax_core`:
no simplification. `Level.max` and `Level.imax` are `lean::mk_max`
(`src/kernel/level.cpp:81`) and `lean::mk_imax` (`src/kernel/level.cpp:112`).
`Level.succ` is `lean::mk_succ`, which never simplifies.

`Level.instantiate` mirrors `lean::instantiate` (`src/kernel/level.cpp:317`), which is
written in terms of `replace_level_fn` and therefore rebuilds changed nodes with the smart
constructors. Substitution can simplify a level even when the substitution is the identity
on parameters.

### L3 — `normalize` is not idempotent

`lean::normalize` handles `imax` by returning
`mk_succ(mk_imax(normalize lhs, normalize rhs), k)` without renormalizing the result
(`src/kernel/level.cpp:454`). `mk_imax` rewrites `imax u (succ v)` to `max u (succ v)`,
a shape that `normalize` would reduce further:

    normalize (imax (succ u) 1) = max (succ u) 1
    normalize (max (succ u) 1)  = succ u

`kolla` reproduces this. A consequence is that `Level.isEquiv` is not transitive.

### L4 — level equivalence

`Level.isEquiv(a, b)` is `a == b || normalize(a) == normalize(b)`, matching
`lean::is_equivalent` (`src/kernel/level.cpp:518`).

### L5 — `geq` is a conservative approximation

`Level.geq` mirrors `lean::is_geq` and `lean::is_geq_core`
(`src/kernel/level.cpp:523`, `542`), including the fact that every recursive step goes
through `is_geq`, which renormalizes both sides. It is incomplete:
`geq(succ (imax u v), imax u v)` is `false`, because the `is_imax(l2)` branch demands
`geq(l1, u) && geq(l1, v)`.

### L6 — level metavariables

`Level.MVar` exists (`src/Lean/Level.lean:95`) even though no export file contains one.
Declarations containing metavariables are rejected by the kernel, not by the
representation.

## Expressions

### E1 — cached data word

Each `Expr` caches one 64-bit word laid out as in `lean_expr_mk_data`
(`src/kernel/expr.cpp:105`):

| bits  | field |
|-------|-------|
| 0-31  | hash |
| 32-39 | approxDepth, saturating at 255 |
| 40    | hasFVar |
| 41    | hasExprMVar |
| 42    | hasLevelMVar |
| 43    | hasLevelParam |
| 44-63 | looseBVarRange |

`App` nodes use `lean_expr_mk_app_data` (`src/kernel/expr.cpp:120`), which mixes the two
full data words rather than just the two hashes.

Lean stores `looseBVarRange` in 20 bits and panics with `"too many bound variables"` above
1048575. `kolla` throws `KernelException(DeepRecursion)` at the same bound.

`hasLooseBVars` is derived as `looseBVarRange > 0`.

### E2 — structural equality

`Expr.==` is `lean::is_equal`, that is `expr_eq_fn<false>`
(`src/kernel/expr_eq_fn.cpp:123`). It does **not** compare binder names or `BinderInfo`,
it **does** compare `letE`'s `nondep` flag, and it compares `mdata` payloads.
`Expr.isBiEqual` is `expr_eq_fn<true>` (`src/kernel/expr_eq_fn.cpp:126`), which also
compares binder names and annotations.

`kolla`'s traversal is an explicit worklist with an identity-keyed visited set in place of
Lean's `expr_eq_fn` cache, so it is stack-safe on all three platforms.

Lean's hash excludes binder names, `BinderInfo`, `letE`'s `declName` and `letE`'s
`nondep`; the first three are also excluded from equality, so hashing stays consistent
with `==`.

### E3 — `letE` carries `nondep`

`Expr.letE` has five fields including `nondep : Bool` (`src/Lean/Expr.lean:421`). The
kernel does not verify it, but it participates in structural equality (see E2).

### E4 — no global interning

`Expr` nodes are not interned in a global table. The cached data word makes hashing and
the equality short-circuit O(1), and sharing is whatever the producer supplies.

## Declarations and environment

### D1 — `Declaration` and `ConstantInfo` are distinct

`Declaration` is the kernel's input (`src/kernel/declaration.h:192`): `axiomDecl`,
`defnDecl`, `thmDecl`, `opaqueDecl`, `quotDecl`, `mutualDefnDecl`, `inductDecl`.
`ConstantInfo` is the environment entry (`src/kernel/declaration.h:416`): `axiomInfo`,
`defnInfo`, `thmInfo`, `opaqueInfo`, `quotInfo`, `inductInfo`, `ctorInfo`, `recInfo`.
`kolla` models both.

### D2 — reducibility hint comparison

`ReducibilityHints.compare` mirrors
`lean::compare(reducibility_hints const &, reducibility_hints const &)`
(`src/kernel/declaration.cpp:24`): negative unfolds the first argument, zero unfolds both,
positive unfolds the second.

### D3 — which constants have values

`Declaration.hasValue` is `is_definition()` (`src/kernel/declaration.h:230`): only
definitions are unfolded during reduction. `ConstantInfo.hasValue(allowOpaque)` is
`is_theorem() || is_definition() || (allowOpaque && is_opaque())`
(`src/kernel/declaration.h:466`).

### D4 — environment ordering

`lean::environment` is a map from `Name` to `constant_info`. `kolla`'s `Environment` also
keeps the insertion order, so an export file's declaration order is preserved and can be
replayed.

## Export formats

Reference: `leanprover/lean4export`. Three source revisions are relevant:
`d797849` (text, Lean v4.12.0), `3245035` (text v2.0.0, Lean v4.25.0-rc2) and
`master` (NDJSON, `format_ndjson.md` plus the reference parser `Export/Parse.lean`).

### X1 — two item shapes

`ExportItem.Info` carries a `ConstantInfo`, an environment entry. `ExportItem.Decl`
carries a `Declaration`, a kernel input. The text v1 format emits kernel inputs for
inductives (`#IND`) and for the quotient package (`#QUOT`), because it contains
neither the derived recursors nor the constructor metadata. Text v2 and NDJSON emit
environment entries throughout, including the recursors. `ExportItem.DefnWithoutHints`
covers text v1's `#DEF`, which carries no reducibility hint.

### X2 — the text formats have no version header

Only NDJSON announces itself, with a leading `{"meta":{...}}` object. The format
version is `meta.format.version`; `meta.exporter.version` is a separate,
independently hard-coded literal in lean4export's `Export.lean` and is used only
as a fallback when the `format` object is absent. The two have drifted apart in
the past, which is what commit `4fb1b91` ("Actually bump format in metadat")
repaired, so they must not be conflated.

Neither text format writes a header, so `ExportReader` resolves the text version
from the first declaration command that distinguishes them:

| command | resolution |
|---------|------------|
| `#THM`, `#OPAQ`, `#CTOR`, `#REC`, `#RR` | v2 |
| `#QUOT` with arguments | v2 |
| `#QUOT` with no arguments | v1 |
| `#DEF` whose fourth argument is `O`, `A` or `R` | v2 |
| `#DEF` whose fourth argument is an index or absent | v1 |
| `#AX`, `#IND` | undecided |

Index-prefixed lines are identical in both formats (apart from `#RR`) and are
applied immediately. Declaration lines seen while the version is undecided are
buffered and replayed in file order once it is known. `#AX` and `#IND` are the only
undecided commands and neither writes to the index tables, so if the input contains
nothing else the buffer is tried as v2 and then as v1.

### X3 — text v1 collapses definitions, theorems and opaques

`dumpConstant` in `d797849` emits `#DEF` for `defnInfo`, `thmInfo` and
`opaqueInfo` alike, and skips unsafe definitions and unsafe opaques. The reader
cannot recover which of the three a `#DEF` was, so it produces
`ExportItem.DefnWithoutHints`.

### X4 — text v1 cannot represent mutual inductives

`dumpConstant` emits one `#IND` line per `inductInfo`, carrying only that type's
own constructors, and the `#IND` grammar has no slot for sibling types
(`val.all` is never written). A mutual inductive block therefore cannot be
reconstructed: checking the first type fails because its constructors mention a
type that has not been declared. `difftest/toolchains.txt` excludes the toolchains
that emit this format; the reader still accepts it, which is enough for
single-type inductives.

### X5 — text v1 has no reducibility hints

`#DEF` carries no hint, so the definitional height has to be computed when the
declaration is added, as `lean::mk_definition(environment const &, ...)` does
(`src/kernel/declaration.h`). `ExportItem.DefnWithoutHints` records that the hint
is absent rather than inventing one.

### X6 — text v2 omits the unsafe flags

`#IND`, `#CTOR`, `#REC`, `#AX`, `#OPAQ` and `#QUOT` have no `isUnsafe` field in
`3245035`, and `dumpConstant` skips unsafe declarations unless `--export-unsafe`
is given. The reader sets `isUnsafe = false` for all of them. `#DEF` carries
`ReducibilityHints` but no `DefinitionSafety`, so safety is read as `safe`.

### X7 — text v2 derives the quotient kind from the name

`#QUOT <nidx> <eidx> <uparams>` has no kind field. The kind comes from the name:
`Quot` is `type`, `Quot.mk` is `ctor`, `Quot.lift` is `lift`, `Quot.ind` is `ind`.
Any other name is an error.

### X8 — NDJSON 3.0.0 and 3.1.0

3.0.0 wraps `axiom`, `def`, `thm`, `opaque` and `quot` payloads in one-element
arrays and names the inductive group's fields `inductiveVals`,
`constructorVals` and `recursorVals`. 3.1.0 uses bare objects and `types`,
`ctors`, `recs` (`a6a63cc`, "refine format: no arrays around definitions"). The
reader accepts an object or an array for the former and either spelling for the
latter, so one code path covers both.

### X9 — `mdata` payloads are dropped

`Expr.mdata`'s `data` object has no documented encoding, and the reference parser
returns `.mdata {} expr`. The reader produces `Expr.MData(KVMap.empty, inner)`,
which keeps the node (so that `Expr` structure matches what the exporter emitted
under `--export-mdata`) while discarding the payload. The kernel strips `mdata`
during reduction, so the payload has no effect on type checking.

### X10 — numeric encodings

NDJSON writes `natVal` as a JSON string so that arbitrary `Nat` values survive
(`parseExprNatLit` in `Export/Parse.lean`); the reader also accepts a JSON
integer. `Name.num`'s index is a JSON integer, parsed as `BigInt`. The text
formats write `#ELN` as a decimal integer and `#ELS` as space-separated
uppercase hex bytes of the UTF-8 encoding.

### X11 — index tables are sparse but bounded by the line count

The exporter assigns dense, sequential indices, but the reference parser stores
them in a `HashMap Nat _`, so out-of-order and sparse indices are accepted.
`Table` matches that behaviour with a growable array.

Because the array grows to the largest index seen, the bound on an index has to
bound memory as well. The exporter assigns `idx = map.size` and emits at most one
entry per line, so no index in a well-formed file exceeds the number of lines read
so far; `Table` rejects anything above that, with 2^28 as an absolute ceiling. A
single malformed line such as `268435455 #EV 0` is therefore an error instead of a
multi-gigabyte allocation. This is stricter than the reference parser, which would
accept such a file, but no file lean4export produces is affected.

Name index 0 is pre-seeded with the anonymous name and level index 0 with `zero`,
as both the exporter and the reference parser do.

### X12 — the writer is not byte-identical to lean4export

`ExportWriter` assigns indices on first use during a depth-first walk, as the
exporter does, but it takes declaration order from the item sequence instead of
re-running `dumpDeps`, and it does not reproduce the trailing space the exporter
leaves after an `#EC` with no universe arguments. Round-trip tests compare
`write(read(write(env)))` against `write(env)` rather than against the original
file.

### X13 — the writer refuses to write lossily

The text formats have no field for `DefinitionSafety`, for the `isUnsafe` flag of
an axiom, opaque, inductive, constructor or recursor, for `Expr.letE`'s `nondep`,
or for the sibling types of a mutual inductive block (X4). Dropping any of those
would silently relabel an unsafe or partial declaration as safe, so the writer
raises an `ExportException` instead, as it already did for `Expr.mdata`, `fvar`,
`mvar` and level metavariables. lean4export takes the same position from the other
end: `dumpConstant` skips unsafe declarations unless `--export-unsafe` is given.
NDJSON carries all of these fields and round-trips them.

### X14 — expression deduplication is binder-blind, as in lean4export

The exporter's expression table is `HashMap Expr Nat`, and Lean's `BEq Expr` is
`Expr.eqv`, that is `lean_expr_eqv`/`expr_eq_fn<false>`, which ignores binder
names and binder annotations (`src/Lean/Expr.lean:811`, see E2). Two binder nodes
that differ only in binder name or `BinderInfo` therefore receive a single index,
and the file records whichever annotation occurred first. Export files already
have this property, and `ExportWriter` reproduces it by keying its table on
`Expr`, whose `==` is the same relation.

A term round-trips with its binder names and annotations intact only when no
binder-equal variant of it appears elsewhere in the same file.
