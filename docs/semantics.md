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

### N4 — `parse` is the inverse of `toString`

`Name.render` writes a `Num` component as bare digits and escapes a `Str` that
looks like one as `«0»`, which is what tells the two apart. `Name.parse` has to
read both back, or `Name.parse(n.toString) != n` for every name with a numeric
component — every macro scope, every `_private` prefix.

This is not cosmetic. `ReplayJson` identifies a declaration by `Name.toString`,
so a name that does not survive the round trip is a name two platforms appear to
disagree about: the first cross-platform run reported
`_private.Init.Core.0.Lean.injEq_helper.match_1_1` as judged only by the JVM and
`_private.Init.Core.«0».Lean.injEq_helper.match_1_1` as judged only by the
native build, when both had accepted the same declaration.

A `.` inside guillemets does not separate components, so an escaped component
containing one survives too.

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

The consequence for `InductiveChecker.validateRecursors` is that a regenerated
recursor can only be compared to the exported one with `Expr.==`. Comparing with
`Expr.isBiEqual` rejects correct declarations: `PProd.rec`'s computation rule
ends in `fun (x : _) (y : _) => _ _ _`, the same shape as `And.rec`'s, which is
written first with binder names `left`/`right`, so the file hands PProd's rule
those names where the kernel derives `fst`/`snd` from `PProd.mk`'s type. The
annotations `infer_implicit` computes still have to be right, because they go
into the environment kolla builds; they just cannot be checked against a file.

## Kernel

### K1 — the kernel is not behaviourally stable across Lean releases

`src/kernel` changes semantics between releases, so a checker that must agree
with `lean4checker` from more than one release needs the release as a parameter.
Comparing `v4.25.0`, `v4.27.0` and `v4.35.0` (the toolchains in
`difftest/toolchains.txt`):

| behaviour | v4.25.0 | v4.27.0 | v4.35.0 |
|---|---|---|---|
| `string_lit_to_constructor` wrapper | `String.mk` | `String.ofList` | `String.ofList` |
| `is_prop` | `whnf(infer_type e) == Prop` | same | `normalizes_to_zero(sort_level s)` |
| `Nat` numeral size limit | none | none | 128 MB, `LEAN_NAT_MAX_SIZE` |
| projection index bound | truncated to `unsigned` | same | rejected if it does not fit |
| `check_uniform_ind_occs` | absent | absent | present |
| `check_recursors` | absent | absent | present |
| eta-struct / unit-like guard | `is_structure_like` | same | `is_non_rec_structure`, which also requires the inductive not be recursive |
| positive `is_def_eq` cache | absent | absent | present |

Three of these can flip a verdict rather than just performance:
`is_prop` (v4.35's comment records that the syntactic test let `infer_proj`
extract non-proof data out of a proof), `check_uniform_ind_occs` and
`check_recursors` are soundness checks v4.35 added, and the string-literal
wrapper changes which terms are definitionally equal.

`KernelProfile` carries these as fields, `KernelProfile.forToolchain` maps an
elan toolchain spec to the nearest pinned profile at or below it, and the
differential platform selects the profile per toolchain. Releases between the
pinned ones take the lower profile, which is a guess until a release is added to
the corpus and diffed.

### K2 — substitution follows `replace_fn`

`ExprOps.replace` mirrors `lean::replace_fn`: `f` sees each subterm with its
binder depth, a `Some` result replaces the subterm and stops the descent, and
results are cached per `(subterm identity, depth)`. `forEach` mirrors
`lean::for_each_fn`, including its child order: `app_fn` before `app_arg`, a
binder's domain before its body, and a `let`'s type and value before its body
(`src/kernel/for_each_fn.cpp`, the offset-carrying `apply`). The order is
observable through `undefinedLevelParam`, which reports the first undefined
parameter, so it decides which name an error message carries. Both traversals run
in `cats.Eval` or on an explicit stack, so neither grows the call stack.

### K3 — beta reduction substitutes arguments in reverse

`whnf_core` collects an application's arguments with `get_app_rev_args` and hands
that reversed buffer to `instantiate`, so `#0` takes the *last* consumed
argument and `#(m-1)` the first. `ExprOps.betaReduce` takes its arguments in
application order and uses `instantiateRev`, which is the same mapping.
`cheap_beta_reduce` instead collects arguments with `get_app_args` in forward
order and indexes them as `args[i - idx - 1]`; `ExprOps.cheapBetaReduce` keeps
that form.

### K4 — `local_ctx::mk_binding` and dead lets

`LocalContext.mkPi`/`mkLambda` abstract free variables back into binders as
`lean::local_ctx::mk_binding` does, rebuilding a `let` for a let-bound variable.
`infer_let` passes `remove_dead_let = true`, which drops a `let` whose variable
does not occur in the body and lowers the remaining bound variables; `infer_lambda`
does not.

A `let` rebuilt this way always has `nondep = false`, and `LocalDecl` has no field
for it. That is Lean's behaviour, not an omission:

- `lean::local_decl` stores only `idx`, `name`, `user_name`, `type` and `value`
  (`src/kernel/local_ctx.h`); there is no `nondep` field and no accessor for one.
- the only let-shaped `local_ctx::mk_local_decl` passes `non_dep = false` as a
  literal to `lean_local_ctx_mk_let_decl` (`src/kernel/local_ctx.cpp`).
- `mk_binding` rebuilds with the four-argument `mk_let`, whose overload supplies
  `nondep = false` (`src/kernel/expr.h:225`).
- `infer_let` calls `m_lctx.mk_local_decl(ngen, let_name(e), type, val)` and never
  passes `let_nondep(e)` (`src/kernel/type_checker.cpp`).

So the flag is lost on the way through the local context in Lean too. It survives
in `Expr` itself, where `==` compares it (E2, E3), and the kernel never reads it.

### K5 — string literals decode to code points

`string_lit_to_constructor` calls `utf8_decode`, which yields Unicode code
points, so a character outside the basic multilingual plane becomes one
`Char.ofNat` application. `ExprOps.codePoints` iterates code points rather than
UTF-16 units to match.

### K6 — the local context is append-only

`type_checker` scopes `m_lctx` with `flet`, restoring it when `infer_lambda`,
`infer_pi`, `infer_let`, `is_def_eq_binding` or `eta_expand` return. `kolla` lets
it grow instead. The two agree because free variable identifiers come from one
generator per checker and each identifier keeps the same type for the whole run,
so a stale entry can never be read for the wrong variable; `mk_pi`/`mk_lambda`
only consult the variables they are handed. Restoring the context would also be
unsound under `cats.Eval`, where a deferred computation runs after the
expression that created the scope has returned.

The `idx` a declaration receives therefore counts every variable created so far
rather than the ones currently in scope. `local_decl::get_idx` is not consulted by
anything in `src/kernel` that affects acceptance.

### K7 — the infer cache is keyed on the term alone

`m_infer_type[infer_only]` is a map from expression to type, with no dependence on
`m_lparams`. Two `check(e, ps)` calls with different `ps` on one `type_checker`
therefore share a cache entry and the second one skips `check_level`. That is why
there is one `type_checker` per declaration: `environment::add_*` constructs a
fresh one, and `kolla`'s `DeclarationChecker` does the same.

### K8 — what is checked, and what is not yet

`DeclarationChecker` mirrors `environment::add_axiom`, `add_definition`,
`add_theorem`, `add_opaque` and `add_mutual`. Replaying an export file's
environment entries splits into two cases, reported as `CheckOutcome`:

- `Checked`: axioms, definitions, theorems and opaques go through the same
  sequence Lean uses, including `check_constant_val`, `check_no_metavar_no_fvar`,
  the theorem-is-a-Prop test and the value-against-type `is_def_eq`.
- `TypeOnly`: inductive types, constructors, recursors and the quotient package
  have their types checked and a recursor's rule right-hand sides type checked,
  but the block is not yet validated — no `add_inductive`, no recursor
  regeneration, no `check_uniform_ind_occs`, no `check_recursors`.

A `TypeOnly` verdict is not a judgement about the declaration, so the differential
platform must not treat it as agreement with `lean4checker`.

### K9 — a step budget replaces `scope_rec_depth`

Lean bounds reduction with `scope_rec_depth` and `check_system`. Since the
`cats.Eval` trampoline has no stack to overflow, `kolla` counts reduction steps
instead and raises `KernelException(DeepRecursion)` past `maxSteps`. An ill-typed
term can make `whnf` diverge in either implementation; the budget is what stops
it.

### K10 — the quotient package is built, not read

`Declaration.quotDecl` carries no data: `environment::add_quot`
(`src/kernel/quot.cpp`) builds `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`
itself after `check_eq_type` has confirmed that `Eq` is the inductive it expects,
and it refuses to overwrite a name already in the environment. `Quot.declarations`
rebuilds the same four constants, and the types it produces are equal to the ones
Lean v4.35.0 exports, which is checked against a real export file.

The text v2 and NDJSON formats ship the four constants, so the driver installs the
package the first time one of them appears and then validates each exported
constant against the built one, comparing the type after renaming the exported
universe parameters. Only `Quot.lift` has two universe parameters.

Reduction is gated on `is_quot_initialized`, so `Quot.lift` and `Quot.ind`
applications do not reduce in an environment where the package was never
installed.

### K11 — inductive checking, and what is still missing

`InductiveChecker` mirrors `add_inductive_fn` (`src/kernel/inductive.cpp`) up to
but not including the recursor:

- `check_inductive_types`: each type is checked against the declaration's
  universe parameters, the parameter prefix is shared across a mutual block,
  the parameter count matches, the indices are counted, and the result universes
  must be equivalent.
- `check_constructors`: duplicate constructor names, the parameter prefix,
  each field's universe against the datatype's (`is_geq(resultLevel, fieldLevel)`
  or the datatype is an inductive predicate), positivity, and the result type via
  `is_valid_ind_app`.
- `is_valid_ind_app` also rejects an occurrence of a datatype being declared among
  the *indices*, which `leanprover/lean4#2125` records as unsound.
- `check_positivity` is skipped entirely for an unsafe declaration, as Lean skips
  it.
- `is_rec`, `is_reflexive`, `numIndices`, `cidx` and `numFields` are derived, not
  read from the file.

The inductive-predicate test uses the profile: v4.35 asks
`normalizes_to_zero(resultLevel)` where earlier releases asked `is_zero` (K1).

`InductiveChecker.validate` compares the derived `InductiveVal`s and
`ConstructorVal`s against the ones an export file ships, field by field. Running
it over the three committed exports reproduces every value Lean emitted for all
ten blocks.

Recursor generation is implemented: `elim_only_at_universe_zero`,
`init_elim_level`, `init_K_target`, `mk_rec_infos`, `mk_rec_rules`,
`declare_recursors`, and under the v4.35 profile the `check_recursors` pass that
type checks each generated recursor and verifies each computation rule is
type-preserving.

`InductiveChecker.validate` compares the recursors an export file ships against
the regenerated ones: the universe parameter count, `numParams`, `numIndices`,
`numMotives`, `numMinors`, the K-like reduction flag, the mutual block, the
recursor type, and every rule's `nfields` and right-hand side. The exported
recursor may name its elimination universe differently, so the derived type and
rule bodies are renamed to the exported parameters before comparison.

The comparison is made twice: with `Expr.==`, which ignores binder names and
annotations (E2), and then with `Expr.isBiEqual`, which does not. Without the
second one the `inferImplicit` annotations and the generated binder names would
never be compared against anything, since they are invisible to the first. With
both, all ten recursors in the three committed exports are reproduced exactly.

### K14 — generated binder names use `append_after`

`name::append_after(unsigned i)` separates the index with an underscore, so the
fresh elimination universe is `u_1` and a mutual block's motives are `motive_1`,
`motive_2`; `append_after(char const *)` extends the last string component, so
the induction hypothesis for an argument `n` is `n_ih`, not `n.ih`. The exported
recursors confirm both: `nat-add-3.1.0.ndjson` contains the name components
`u_1` and `n_ih`.

A minor premise is named by `name::replace_prefix(ind_type_name, anonymous)`, so
`Nat.succ`'s premise is `succ`.

Both are wrapped in `Name.modifyBase` (`src/Init/Meta/Defs.lean:308`), which for
a hygienic name applies the suffix to the *unhygienic base* and re-attaches the
macro scopes: `appendAfter` of `_ih` to `n._@.M._hyg.0` is
`n_ih._@.M._hyg.0`, not `n._@.M._hyg.0._ih`. A name is hygienic when it ends in
`._hyg.<scopes>` (`Name.hasMacroScopes`), and the base is the prefix of the
rightmost `_@` component (`Name.eraseMacroScopes`). Constructor arguments
routinely carry such names — `HAdd.mk`'s fields are `a._@._internal._hyg.0` in
the committed export — so getting this wrong would make the `isBiEqual`
comparison below *falsely reject* any block with a hygienic recursive argument,
which is worse than not comparing at all.

These are binder and universe-parameter names, so only `Expr.isBiEqual` and the
positional universe renaming see them. They were wrong (`u1`, `n.ih`) while the
export comparison used `Expr.==` alone and nothing noticed.

`environment::add_inductive` runs two checks before `add_inductive_fn`, and both
are implemented:

- `check_no_nested_aux`: user input must not mention the `_nested` prefix the
  preprocessor reserves for its auxiliary declarations. Projections are checked
  as well as constants, because a projection's structure name is resolved the
  same way and could name an auxiliary type without the declaration mentioning
  it as a constant.
- `check_uniform_ind_occs` (v4.35 only): every occurrence of a datatype being
  declared must be applied to exactly `nparams` arguments which are the bound
  variables `#(offset-1) … #(offset-nparams)`, with the declaration's universe
  levels. An occurrence with *more* than `nparams` arguments is skipped at that
  node and its parameter application is checked as a subterm.

### K17 — a nested recursor's major premise is not the block's own type

`recursor_val::get_major_induct` reads the major premise's inductive off the
recursor's own type: it walks `majorIdx` binders, takes that binder's domain and
returns its head constant (`src/kernel/declaration.cpp:145`). It is not
`all.head`, and for the recursors a nested inductive generates the two differ.
`Lean.Language.SnapshotTree.rec_3` has `all = [SnapshotTree]`, because every
recursor of the block shares the block's `all`, while its major premise has type
`SnapshotTask SnapshotTree`.

The distinction is load-bearing because `majorInduct` is what
`to_cnstr_when_structure` is asked about, and that decides whether a major which
is not yet a constructor application gets eta-expanded into one so that iota can
fire. `SnapshotTask` is a non-recursive structure and `SnapshotTree` is not, so
asking about the block's own type answers "no" where Lean answers "yes": the
recursor application stays stuck, and a proof that needed one iota step fails
with a type mismatch two levels up.

Nothing but a nested inductive shows this, and only one whose nested occurrence
is a non-recursive structure. The handwritten corpora did not reach it; the
`lean` corpus rejected nine `_sizeOf_N_eq` lemmas on `SnapshotTree`,
`Do.Code`, `DiscrTree.Trie`, `TacticParsedSnapshot` and `EqCnstr`, while `init`
and `std` passed clean across 159,000 declarations.

### K16 — nested inductives

`AddInductive.add` is `environment::add_inductive`, and it is the entry point for
an inductive declaration. `InductiveChecker` is `add_inductive_fn` and sees only
the nested-free auxiliary block, which is why `check_no_nested_aux` and
`check_uniform_ind_occs` live in the driver: the auxiliary declaration mentions
the reserved `_nested` prefix by construction, so running the first of them
inside `InductiveChecker` rejects every nested block.

`ElimNestedInductive` replaces each nested occurrence `I Ds is` — an application
of an already declared inductive whose parametric arguments mention a type being
declared — with `Iaux As is`, where `As` are the block's own parameters. Notes
that are load-bearing:

- every type of `I`'s mutual block is copied, not just `I`.
- the parameters are rebuilt for each constructor so that each keeps its own
  binder info, which is why the `nested_aux` lookup key is restated in terms of
  the declaration's parameters before comparison.
- the parametric arguments `Ds` must be closed; a bound variable there is an
  error, since `Ds` does not appear in the auxiliary declaration.
- an auxiliary type's name is `_nested.<J>_<n>`, made unique against the
  environment.

`ElimNestedResult.restoreNested` rewrites the auxiliary types and their
constructors back, and renames the auxiliary recursors to
`<main type>.rec_1`, `.rec_2`, ... (`mk_aux_rec_name_map`). The restored
declarations are added to the *original* environment, so no auxiliary type can
leak; the test asserts that. `Ds` is type checked at the end, in the restored
environment, because it appears nowhere in the auxiliary block and would
otherwise escape checking entirely.

Validated against `nested-3.1.0.ndjson`, exported from Lean v4.35.0: `Tree`
(nested `List Tree`) and `RoseTree` (nested with a parameter) both reproduce
Lean's two recursors each — `Tree.rec`/`Tree.rec_1` and
`RoseTree.rec`/`RoseTree.rec_1` — with types and rule right-hand sides equal up
to `Expr.isBiEqual`.

### K15 — a block's recursors must all be installed before any rule is checked

`declare_recursors` installs every recursor of a block and `check_recursors`
runs afterwards, because a rule's right-hand side can call a sibling recursor of
the same block. A nested inductive makes this visible: Lean generates both
`Tree.rec` and `Tree.rec_1` for

    inductive Tree where
      | leaf : Nat → Tree
      | node : List Tree → Tree

and `Tree.rec`'s rules call `Tree.rec_1`. `DeclarationChecker.addInfo`
therefore checks a recursor's own type but not its rules; rules are checked by
`InductiveChecker.run`, which has the whole block. The extra recursor's name
comes from `appendIndexAfter` (K14).

### K12 — `consume_type_annotations` is not just `mdata`

`add_inductive_fn::mk_local_decl_for` puts every binder domain through
`consume_type_annotations` before it enters the local context, and that strips
four *application* gadgets, not metadata: `optParam α d` and `autoParam α tac`
reduce to `α` (their first argument), `outParam α` and `semiOutParam α` to `α`
(`Expr.consumeTypeAnnotations`, `src/Lean/Expr.lean:1739`). Nested annotations
under a binder are left alone.

This is load-bearing for recursor generation. `HAdd` declares its third parameter
as `outParam (Sort w)`, so without stripping, the generated `HAdd.rec` carries
`forall (γ : outParam.{succ (succ w)} Sort succ w)` where Lean's carries
`forall (γ : Sort succ w)`, and the two do not compare equal.

### K13 — a constructor type must be walked once

`mk_rec_infos`, `mk_rec_rules` and `check_recursors` each walk a constructor type
collecting the non-parameter arguments as free variables, and each needs the
*result* type instantiated with those same variables. Splitting the walk into one
pass for the arguments and another for the result gives the result type a
different set of free variables, which produces a recursor whose minor premise
applies the motive to the wrong index. `ctorParts` returns both from one pass.
v4.35's `check_recursors` rejects the result, which is what it is for.

## DSL

### D5 — binders are Scala functions

`LeanDsl.Lam`, `Pi` and `Let` take the body as `Expr => Expr`. The bound variable
is a free variable with a fresh identifier while the body is built and is
abstracted immediately afterwards, which is `local_ctx::mk_binding` for one
variable. Each binder abstracts its own variable, so `k` nested binders cost
O(k²); that is fine for hand-written terms, and a generated telescope should use
`LocalContext.mkPi`/`mkLambda`, which abstract every variable in one pass.

### D6 — `->:` and Scala's operator rules

An arrow has to be right associative, which in Scala means the operator name has
to end in `:`. For such an extension method Scala binds the *extension receiver*
to the left operand, not the right, so `->:` is declared on the domain:
`extension (domain: Expr) infix def ->:(codomain: Expr)`. Declaring it the other
way round reverses every arrow, and `Nat ->: Nat` cannot show it because it is
symmetric: `a ->: b ->: c` produced `(a -> b) -> c`.

### D7 — the interpolator shares the parser

`lean"..."` is a macro that runs `LeanParser` at compile time and emits
construction code for the resulting term, so the grammar has one implementation
and a syntax error is a compile error. A `${...}` hole becomes a `$i` marker that
the parser turns into an `Expr.MVar` under the reserved prefix `_leanSplice`,
which the macro's lifter replaces with the argument. A spliced `Expr` is inserted
unchanged and must therefore be closed; the syntax has no way to name an
enclosing binder from Scala. A `Level` splices as `Sort l` and a `Name` as a
constant.

Because the macro *runs* the parser, changing the parser does not by itself force
call sites to be re-expanded, and a stale expansion can survive an incremental
build. The interpolator tests compare against `LeanParser.parseOrThrow` at
runtime, which turns that staleness into a test failure rather than a silent
divergence.

### D8 — the DSL reads a digit component as a numeral

`LeanParser.parseName` makes an all-digit component of a dotted identifier a
`Name.Num`, as Lean's name syntax does; `Foo.3` is `Name.num 3` and the string
form would be written `Foo.«3»`, which this syntax does not support.
`Name.parse` in the kernel is the plain splitter and keeps every component a
string, so the two deliberately disagree on `Foo.3`.

### D9 — parser nesting is bounded

The grammar is parsed by recursive descent, so nesting is bounded explicitly at
`LeanParser.maxDepth` and reported as a parse error. Scala.js has a much smaller
stack than the JVM: 2000 nested `fun`s parse on the JVM and raise
`RangeError: Maximum call stack size exceeded` under Node.

The bound has to cover *every* recursion in the grammar, not just `expr` and
`atom`. Universe levels recurse through their own functions, so `levelAtom` goes
through the same guard; without it `Sort ((((u))))` nested 20 000 deep threw a
`StackOverflowError` out of `parse`, which catches only its own
`ParseException` and so returned no `Left` at all.

### D10 — a multi-name binder group lifts its shared type

`(a b : A)` is one group whose type is read in the scope *before* the group, but
the k-th name sits under the k names before it, so the type's loose bound
variables are shifted by k. Without that, `forall (A : Sort u) (a b : A), A`
parses as `... (b : a) ...`, pointing `b`'s type at `a`. A closed group type such
as `Nat` cannot show this, and when the shifted target happens to be a type —
`fun (u : Sort 2) (A B : u) => A` — the result is well typed and silently wrong.

### D11 — a keyword is not the prefix of an identifier

`fun`, `forall`, `let`, `Sort`, `max`, `imax` and `succ` are only keywords when
the next character cannot continue an identifier. Matching them by raw prefix
makes `funext` fail, and makes `SortedList` *silently* parse as `Sort edList`, a
sort over a universe parameter named `edList`. `λ`, `∀` and `→` are not
identifier characters and need no boundary test.

### D12 — a splice marker is delimited

The interpolator emits `$i ` with a trailing space, because the index is read as
a numeral: concatenating `$i` straight onto a literal part that begins with a
digit merges the two, so `lean"f ${a}1 ${b}"` built the source `f $01 $1` and
read the first marker as index 1, silently expanding to `f b b` with the literal
`1` gone.

### D13 — reduction is not execution

`Evaluate` type-checks a closed term against an environment and reduces it,
which is `#eval` for the part of `#eval` the kernel can do. `--eval` is the
command line for it. What comes back is a normal form and the type the term was
checked at:

    Nat.add 2 3     ->  5 : Nat
    Nat.pow 2 16    ->  65536 : Nat
    Nat.ble 2 3     ->  Bool.true : Bool
    Nat.decEq 2 2   ->  Decidable.intro (Eq.{1} Nat 2 2) Bool.true
                        (Eq.refl.{1} Nat 2) : Decidable (Eq.{1} Nat 2 2)

The last one is the point: a decidability proof is computed, not just
arithmetic.

Three limits, all consequences of being the kernel rather than an interpreter.

Arithmetic is fast because the kernel reduces it natively: `reduceNat` answers
`succ`, `add`, `sub`, `mul`, `pow`, `gcd`, `mod`, `div`, `beq`, `ble`, `land`,
`lor`, `xor` and both shifts straight on literals. Strings have no such thing.
The only string extension is the literal-to-constructor expansion through
`profile.stringLiteralCtor`, so `String.append "ab" "cd"` can only unfold the
definition: both literals expand to `List Char`, the recursive `List.append`
runs over them, and the result is a `String.mk (List.cons ...)` term that
nothing folds back into `"abcd"`. It did not finish within a minute when tried,
and no time is quoted here because it was not run to completion. That is Lean's
kernel too, not a gap in kolla.

Reduction is bounded. `Evaluate.maxDepth` caps how far into an application
spine arguments are reduced, so a deeply nested constructor chain can come back
with redexes still in it; `Result.partial` says when that happened and the
command line prints a warning, because otherwise an unfinished term is
presented as the answer. The printing is unbounded on this path for the same
reason: `Expr.toString` truncates at `Pretty.defaultMaxChars`, which is right
for a rejection diagnostic and wrong when the term *is* the result, so
`--eval` uses `Pretty.expr(e, Int.MaxValue)`.

Reduction does not go under a binder. A lambda's body has loose bound variables
and the kernel reduces closed terms, so `fun (x : Nat) => Nat.add 2 3` comes
back with its body intact. `EvaluateSuite` asserts that, so the limit is pinned
rather than incidental.

The environment is admitted, not checked. `--eval` replays the export with
nothing selected for checking (P14), because re-deriving a library in order to
compute `Nat.add 2 2` would be absurd, and it says how many declarations it
admitted on stderr. The answer is therefore only as good as the file; check the
file separately if that matters.

A Lean *program* is out of reach, and not by a small margin. `main : IO Unit`
is `EStateM IO.Error IO.RealWorld Unit`, and while that shape maps onto
`cats.effect.IO` cleanly enough, the primitives do not: `IO.println` descends
through `IO.print` and `IO.FS.Stream.putStr` to `@[extern]` declarations that
the kernel sees as constants with no definition to unfold, and `main` is run by
a binary the Lean compiler produced. Running one would mean supplying a Scala
implementation for each primitive and owning the `RealWorld` discipline — a
Lean runtime, which is a different project with a different risk profile, since
nothing would check those implementations against Lean's C. It would also have
to live outside `kernel`, where `cats.effect` is not allowed.

## Differential platform

### P1 — a tool revision must pin exactly the target toolchain

`lean4export` and `lean4checker` are written against Lean's internal APIs, so a
revision compiles only against the toolchain its own `lean-toolchain` names.
`Provision.resolveRevision` therefore requires an exact match — a tag named
after the toolchain, else the newest commit pinning that spec — and
`Provision.lakeBuild` leaves `lean-toolchain` alone.

Rewriting it to the target instead, or falling back to the newest revision at or
below the target, builds the wrong source: `lean4checker` at its v4.29.0-rc8 head
calls `Environment.addDeclCore` with the v4.29 signature, which v4.35 changed,
and `lake build` fails. Accepting a near-miss revision would be worse than
failing, because a reference checker built from the wrong source is not a
reference.

### P2 — `lean4checker` has no release for every toolchain

`lean4checker`'s newest tag is v4.29.0-rc8. By P1 it cannot be built for
v4.35.0, so `difftest/toolchains.txt` marks that toolchain `no-reference` rather
than attempting and failing the build on every run. v4.28.0 is in the matrix for
the same reason: it is the newest release both tools tag, and it carries the same
NDJSON 3.1.0 format as v4.35.0, so the reader and the reference comparison are
exercised against `lean4checker` on that format.

### P3 — a positive corpus is its own reference

Every corpus is the export of an environment Lean itself built and accepted, so
each declaration in it must be accepted. `Report.falseRejections` holds kolla to
that independently of any reference checker, which is what makes a toolchain
marked `no-reference` under P2 still worth running: a false rejection there is
caught without `lean4checker`.

### P4 — `lean4checker` reports per module, not per declaration

`lean4checker`'s `main` replays a module and, on the first failure, prints
`lean4checker found a problem in <module>` and rethrows; it names no declaration
and does not continue. Its runs therefore carry `perDeclaration = false` and a
single synthetic `DeclResult`, and are compared only through `CheckerRun.overall`
by `Compare.overall`. `Compare` itself stays per declaration, for kolla against
kolla across toolchains and platforms.

Because `lean4checker` aborts, kolla runs with `stopOnFirstRejection` whenever a
reference is available, so the two corpus-level verdicts mean the same thing.

### P5 — a handwritten case exports its own declarations, not its environment

`lean4export` with no declaration list exports the whole environment, which for
any file importing `Init` is around 330 MB. A handwritten case is instead
exported as the names its own module declares — read from the olean's
`constNames` by `difftest/lean/ListDecls.lean` — plus their dependencies, which
`lean4export` follows. `case-eta` goes from 330 MB to 105 KB that way. The whole
standard library is still covered, by the `init`, `std` and `lean` corpora.

`lean4checker` gets `--fresh` for a single-module handwritten case, which replays
that module's imports as well, so the two checkers see the same declaration set.

### P6 — a rejected declaration is still carried into the environment

`KollaChecker` adds a rejected declaration to the environment unchecked before
moving on. Leaving it out would make every later declaration mentioning it fail
with an unknown constant, turning one disagreement into a cascade of spurious
ones and hiding the first.

This only matters when `stopOnFirstRejection` is off, which is how the negative
corpus runs: a mutant has exactly one corruption, and the run has to show which
declaration it was caught at rather than a wall of consequences.

### P7 — a negative case names the toolchains it applies to

A negative corpus has to get an unchecked declaration into the environment,
which means calling `Environment.addDeclCore (doCheck := false)`. That is an
internal API and its signature changes between releases: the v4.28 call
`env.addDeclCore 0 decl none` does not elaborate under v4.35, the same drift
that stops `lean4checker` building there (P1).

A case therefore declares the versions it compiles under with a
`-- toolchains: v4.25.0 v4.27.0 v4.28.0` line, which is an ordinary Lean comment,
and a run skips the cases that do not name its toolchain. Every version named
has to be in `difftest/toolchains.txt`, so a typo cannot silently disable a case.

v4.35.0 consequently has no negative case. Its negative coverage is the mutants,
which are produced from the export file rather than from Lean and so are
toolchain-independent.

### P8 — a rejection reason is the exception kind, not its detail

`KernelException.detail` is not a reason on its own: for `InvalidProj` it is
just the projection, and the kind is what says what is wrong with it. Verdicts
record `KernelException.reason`, which is the kind, the declaration name and the
detail, and leave the defeq trace to `DeclResult.trace`.

### P9 — nanoda is the reference v4.35.0 does have

nanoda_lib reads an export file rather than oleans, so it is not built against a
Lean toolchain and one build serves every release. What it is tied to is the
export format: `check_semver` in its `src/parser.rs` accepts 3.1.0 up to but not
including 3.2.0, which in this matrix is v4.28.0 and v4.35.0.

Two gates apply, and only the second narrows the toolchains. `Nanoda.supports`
is about the reader, and since lean4export backported 3.1.0 to every release tag
every export in this matrix is readable. `Nanoda.matchesKernel` is what makes
nanoda a reference for v4.35.0 alone, and it is the gate to look at when nanoda
did not run: nanoda has no notion of a release, so it implements the v4.35
behaviours unconditionally and looks up `String.ofList`, which does not exist
before v4.27. Running it against v4.25.0 reproduces the `case-strlit` rejection
of P10 for its own reason, which says nothing about kolla.

That makes it the reference for v4.35.0, which `lean4checker` has no release for
(P2). Like `lean4checker` it reports one verdict for the whole file — a bad
declaration panics out of `check_all_declars` — so it is compared through
`CheckerRun.overall` and kolla runs with `stopOnFirstRejection` whenever either
reference is in play.

nanoda's revision is pinned in `Nanoda.rev` for the reason P1 gives for the Lean
tools: it tracks current Lean, so an unpinned clone would make the v4.35.0 run
disagree the first time upstream implements a kernel change, with nothing in
kolla having moved.

`nat_extension` and `string_extension` are off by default in nanoda and are
turned on, since Lean's kernel has them. `unpermitted_axiom_hard_error` is off:
an export file declares axioms none of its declarations use, such as `sorryAx`,
and nanoda would otherwise abort on them before checking anything.

### P10 — the kernel's ambient constants are hoisted to the front

The kernel's literal extensions refer to constants by name: the string
expansion builds `String.ofList (List.cons (Char.ofNat c) ..)`, the `Nat`
extension needs `Nat.zero` and `Nat.succ`. None of these is a *syntactic*
dependency of the declaration that needs them — a theorem about `"ab" ++ "cd"`
never mentions `String.ofList` — so lean4export, which orders a file by
syntactic dependency, can emit them after their first use.

In the v4.25.0 export of `case-strlit`, `appendLit` is item 406 and `String.mk`
is item 1822. A linear replay therefore reaches `"ab" ++ "cd" = "abcd"` with
nothing to expand the literal to, and rejects it. Lean never sees this: its
kernel always runs with `Init` imported, and `lean4checker` replays a module
into an environment that already holds its imports.

`KollaChecker.hoistExtensionConstants` moves those constants, and the groups
they depend on, to the front. An inductive block stays contiguous, which the
checker loop requires; nothing is added unchecked and nothing is checked twice.

The ordering guarantee is relative, not absolute: the pass never turns a
dependency the file satisfied into one it does not. Being a stable partition of
whole groups, it leaves every edge within a half untouched; an edge from a
hoisted group to a group declared earlier cannot escape, because `require`
follows it and hoists that group too; and an edge into a hoisted group is only
satisfied earlier than before. The pass does not claim to repair a file whose
declarations were not topologically ordered — an edge that already pointed
forwards still does, and such a file fails identically with the pass turned
off.

### P11 — a mutant is credited only with rejections the baseline did not have

`MutationRun` checks the unmutated corpus first and subtracts its rejections.
Without that, a corpus with a pre-existing failure makes every mutant look
correct, including `ChangeDefinitionalHeight`, which must stay accepted: the
v4.25.0 run before P10 reported `change-definitional-height` as a rejection of
`appendLit`, a declaration the mutation had not touched.

The subtraction is also why a negative corpus is never mutated. Its baseline
rejects by construction, so a mutation of the declaration already rejected
produces no new rejection and would be reported as a bad mutant.

### P12 — `std` cannot be checked on a pre-v4.35 profile

`KernelProfile.forToolchain` maps v4.28.0 to `v4_27`, where `cacheDefEqSuccess`
is false: Lean added the positive `is_def_eq` cache in v4.35 and keeps only the
negative one before that. kolla follows the release, and on a library corpus the
difference is not a constant factor.

Measured at commit 870368f on a 48 GB machine:

| corpus | profile | wall | peak heap |
|---|---|---|---|
| `init` | v4_35 | 48.2s | 2.74 GB |
| `init` | v4_27 | 77.3s | 2.86 GB |
| `std` | v4_35 | 304.5s | 3.77 GB |
| `std` | v4_27 | `OutOfMemoryError` after 55min | >24 GB |

`lean4checker` at v4.28.0 checks the same 394 `Std` modules in 74s with a peak
resident set of 1.1 GB, and Lean's kernel has no positive cache there either.
The cost is therefore kolla's, not the profile's: successful `is_def_eq` results
are being re-derived that Lean does not re-derive. Where is not established.
`TypeChecker` is one instance per declaration with unshared caches and `Expr`
has no global intern table, so this is not accumulation across declarations; a
blowup inside a single declaration fits the evidence but has not been localised.

The consequence for the platform is that `std` and `lean` are compared against a
reference only at v4.35.0, where nanoda is the reference (P9). At v4.28.0 the
library comparison stops at `init`. `lean4checker`'s own verdict on `Std` at
v4.28.0 is recorded here rather than in `difftest/history`, since no kolla run
completed to compare it against.

It is one declaration, not the corpus. A streamed run over `std` at the v4_27
profile accepts 19,574 declarations and then stops making progress on

    Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.blastDivSubtractShift

which bit-blasts a division subtract-and-shift step; its eight `_proof_*`
lemmas are accepted immediately before it. Isolating it with `--check` (P14),
so that the other 87,308 declarations of the same file are admitted unchecked
and only this one is checked:

| profile | result |
|---|---|
| v4.35.0 | accepted, whole run 80s, 2.57 GB resident |
| v4.27.0 | no verdict after 17 minutes, resident pinned at 5.93 GB of a 6 GB heap |

Nothing differs between those two but `cacheDefEqSuccess`. Whatever work the
positive cache absorbs, this declaration generates enough of it to exhaust a
heap that the entire corpus fits in otherwise, which makes it the term to
profile rather than the corpus.

### P13 — the hoisting pass holds a window, not the file

`Replay` is fed with `feed` and `finish` rather than constructed from a
`Vector`, so a driver can supply items from a stream and never materialise the
export. What stops that being free is P10: hoisting the kernel's ambient
constants to the front needs to know where they are, and the whole-file pass
reads every item before emitting any.

The pass is salvageable because `require` only follows dependencies to groups
declared *earlier*. The `needed` set computed from a prefix that contains every
ambient constant is therefore identical to the one computed from the whole
file: a dependency outside the prefix is one the full pass would have filtered
out anyway. So the prefix is held back only until the ambient constants have
all been declared and their group has closed, and released there.

A file that never declares one of them — `quot-sound` declares none of the nine
— would hold everything, so `hoistWindow` bounds it. The prefix is cut at the
first group boundary once the window is full, whichever comes first. The
default is 65536 items, against a widest measured need of 1416: in the v4.25.0
`case-strlit` export `appendLit` is item 406 and `String.mk` item 1822. The
`Vector` constructor passes `Int.MaxValue`, so a frontend that already holds
the items keeps exactly the whole-file order.

Cutting the window early is not silent. An ambient constant declared after the
cut is recorded in `lateAmbientConstants`, because a rejection downstream of it
may be P10 rather than a disagreement, and a frontend reports it. The streamed
`case-strlit` shape is tested both ways: within the window the verdicts match
the whole-file run, and with `hoistWindow = 1` the demoted `Nat` block is
rejected exactly as it is unhoisted.

What streaming does not bound is the reader's interning tables. The export
format refers to expressions by index, so every expression stays reachable for
as long as a later line might name it, and `ExportReader.pipe` drops items but
not the tables. Measured on the v4.35.0 `init` export, 330 MB and 59,349
declarations: 1.19 GB peak resident, against 2.74 GB of heap for the same
corpus read into a `Vector`.

### P14 — an unselected declaration is admitted, never accepted

`Replay`'s `check` predicate decides what is checked. A declaration it declines
takes the same path a rejected one takes (P6): it is added to the environment
unchecked, so that what depends on it still resolves rather than failing with
an unknown constant. Its outcome is `CarriedOver`, which `ReplayTally` counts
apart from `accepted` and which K8 already defines as never agreement.

Reusing `CarriedOver` rather than adding an outcome is deliberate. The two
cases mean the same thing to a caller — the export file supplied this constant
and the kernel did not re-derive it — and differ only in why, which the reason
string carries. `Replay.admittedUnchecked` counts the requested ones so a
frontend can report them separately, which the command line does on stderr.

The flag is `--check <prefix>`, not `--trust <prefix>`. The behaviour asked for
was to admit non-matching declarations and check the rest, so the prefix names
what is checked; calling that "trust" names the complement of what it takes.
`--only` stays what it was, a filter on the report, so the two are not confused:
one changes the work, the other changes the output.

A verdict under `--check` covers the selection, not the file. A rejection
outside the prefix is not reached, which is why the count is reported rather
than left implicit; a caller that treats exit 0 as "this file is sound" would
be wrong about every declaration it declined to check.

### P15 — a cache entry is a digest of the dependency closure

A declaration's verdict is not a function of its own text. It depends on every
constant it reaches, so a cache keyed on the declaration alone would report a
hit after a dependency changed underneath it and accept something that had
never been checked in that form. `Digest` is therefore a Merkle hash: an
`Expr.Const` mixes in the digest of what it names, and a `Expr.Proj` the digest
of the structure it projects from. A name not yet declared contributes its name
instead, which is the most that can be said about a forward reference.

Three things join the declaration in the key.

The profile, because the same declaration is accepted on one and rejected on
another — that is what the matrix exists to show. `KernelProfile.release` and
not `label`, though: the two differ only for `withDefEqSuccessCache` (K18),
which changes no verdict, and keying on the label would make `--defeq-cache`
discard every digest accepted without it. That is precisely the run the flag
exists for — exhaust the heap, then re-run with the cache — so the cache would
be empty exactly when it was most wanted.

Sharing digests across that flag is one step less conservative than keying on
the label, for the reason K18 gives: caching cuts the step count, so a
declaration accepted with the cache might have hit `maxSteps` without it, and a
run without the flag will reuse that entry rather than discover it. The limit
is kolla's own guard rather than Lean's and is `1 << 32`, so the trade is a
theoretical loss against a cache that works in the case it was built for.

The ambient constants, in a fixed order, because the kernel reaches for them
when it expands a literal without the declaration naming them (P10). A digest
that omitted them could hit after `Nat.succ` changed. They are mixed into every
declaration's digest rather than only into the ones containing literals, which
is conservative and costs nothing.

`Digest.epoch`, bumped by hand when kernel semantics change. This is the part
that cannot be derived from the input, and it is the sharp edge: if the kernel
changes what it accepts and the epoch does not change, every existing entry is
a false accept.

Binder names and `BinderInfo` are deliberately left out. `Expr.==` is
`lean::is_equal`, which ignores both (X14), so two declarations differing only
there are one declaration to the kernel and must not miss.

A hit is `ReplayOutcome.Cached`, counted apart from `accepted`, and
`ReplayTally.ok` treats it as judged. That makes the cache file part of what a
verdict rests on, which is why `--cache` is opt-in and why `difftest` never
passes one: a comparison against a reference has to be this run's own verdict,
not a stored answer. A rejection is never written, so a broken declaration is
re-checked every run.

The digest is not a cryptographic hash and does not need to be. Anything that
can write the cache file can put any digest in it, so collision resistance
against an adversary buys nothing that trusting the file has not already given
away; what matters is the accidental rate, and 128 bits is ample for millions
of declarations.

Measured on `init` v4.35.0, 59,349 declarations: 47.7s with no cache, 96.0s
cold while writing one, 26.7s reusing it. A warm run is not free because the
file still has to be read and digested to know it is the same file, and the
digest is a second walk over every expression — so the cold cost is roughly
double. The gain follows how much of the run is checking rather than parsing.

### K18 — the positive defeq cache can be kept on an older profile

Lean added a positive `is_def_eq` cache in v4.35 and `KernelProfile` follows
the release, so `v4_25` and `v4_27` do without it. P12 is what that costs: one
declaration of `Std` exhausts a 24 GB heap on `v4_27` where the whole corpus
takes 305 seconds on `v4_35`.

`KernelProfile.withDefEqSuccessCache` keeps the cache on a profile that
predates it, and `--defeq-cache` is the way to ask for it. It is an
optimisation rather than a change of profile. An entry is written only where
`is_def_eq` already answered true and `succeededBefore` does nothing but
short-circuit to that answer; `TypeChecker` is one instance per declaration,
and within one the environment is fixed and the local context append-only with
globally unique free variables (K6), so a pair that answered true cannot answer
otherwise later.

It is verified rather than argued. `DefEqCacheEquivalenceSuite` replays every
committed fixture on both uncached profiles each way and requires the outcome
sequences to be equal, and on the v4.28.0 `init` export — 51,759 declarations
on the `v4_27` profile — the two runs agree name by name and verdict by
verdict, 127.2s and 1.10 GB against 95.0s and 1.65 GB. Faster and larger, as a
cache should be.

One way it can change an outcome: caching cuts the step count, so a
declaration that would exhaust `TypeChecker.maxSteps` without it may pass with
it. That limit is kolla's own guard and not Lean's, so the direction is towards
Lean's behaviour rather than away from it.

The label carries the change — `v4.27.0+defeq-cache` — because every summary
line names the profile, and a run with the flag is not a faithful reproduction
of that release's performance even though it is of its verdicts. `difftest`
never sets it, for the same reason it never passes a cache (P15).

`release` is what the label strips that suffix back to, and it is what a cache
digest keys on, so turning the flag on does not invalidate a cache file built
without it. P15 has the reasoning and the one way it is less conservative.

The command line also says this before a run rather than after one. An export
over `Options.libraryScaleBytes` on a profile without the cache prints the
advice and names the flag: the largest committed fixture is 17 MB and `init` is
292 MB, so the threshold separates a fixture from a library and anything above
it is the scale at which the missing cache stops being a slowdown.

### P16 — a digest walks a DAG, so it has to memoise

An export names expressions by index, so a declaration's term graph is a DAG
and the reader hands out the same `Expr` instance everywhere a subterm is
shared. `Digest.exprDigest` walked it structurally at first, which re-digests
every shared subterm once per path: exponential in the sharing rather than
linear in the nodes.

It is not a theoretical cost. On the v4.35.0 export of `Mathlib` — 6.26 GB,
110,895,826 lines — a run stopped making progress after 150,036 declarations
and 1,235 MB, one core busy, resident flat at 1.5 GB of a 24 GB heap, and
stayed there for over thirty minutes. The JVM would not answer `jstack`,
`jcmd` or `SIGQUIT`, because the thread never reached a safepoint. Two runs
with different flags stalled at the same byte, which is what ruled out the
kernel: one of them checked nothing at all.

`Digest.Memo` fixes it, keyed on identity rather than structure —
`Expr.equals` is `is_equal` and O(size) on terms that are equal without being
the same instance, and what matters here is exactly the instances the reader
shared. `DigestSuite` builds a term of 2^40 paths over 41 distinct nodes and
requires the memo to hold 41 entries; without it that test does not finish.

The digest is also computed only when a cache is in use. It had been
unconditional, so every run paid a full extra walk over every expression for an
answer nothing consulted — which is why a run with no `--cache` stalled in the
same place as one with it.

Two things this changes that are worth stating. Digest values differ from the
pre-memo implementation, so a cache file written before it will miss rather
than hit; `Digest.epoch` is left alone because a stale entry can only fail to
match, not match something it should not. And a run without `--cache` no longer
maintains the name-to-digest map at all, so it carries nothing per declaration.

### K19 — one Mathlib declaration does not finish checking

Reading a Mathlib export is cheap and checking it is not. On the v4.35.0 export
of module `Mathlib` — 6.26 GB, 729,263 declarations — reading and admitting
everything takes 83 seconds (P16, docs/scale.md). A full check reaches 325,090
declarations and 3,008 MB in about 58 minutes and then stops advancing:

    CategoryTheory.Localization.Monoidal.braidingNatIso

the step immediately after its own `_proof_1`, which was accepted. Thirty
further minutes produced no progress, with the runtime spinning across roughly
seven cores and a live set under 4 GB against a 24 GB ceiling. So it is not
exhaustion, and `--defeq-cache` is not the answer either: this is the v4_35
profile, where the positive `is_def_eq` cache is already on.

That makes two declarations of this shape on record, single terms that swallow
unbounded time rather than memory:

| declaration | profile | what it is |
|---|---|---|
| `Std.…blastUdiv.blastDivSubtractShift` | v4_27 | P12, the missing positive cache |
| `CategoryTheory.…braidingNatIso` | v4.35.0 | 325,090 declarations in, unexplained |

A third was nearly recorded here and should not be. An earlier run with
`--check Real.log` over the same export also stopped dead, and it was tempting
to read that as a third expensive declaration. It was not: a run over the same
file that checked nothing at all stalled at the identical point — 150,036
declarations, 1,235 MB — which is the unmemoised digest of P16, and the fix
removed it. Attributing it to the kernel would have sent someone chasing a bug
that is already closed.

What remains unexplained is `braidingNatIso`. It is on the profile that caches,
it is not short of heap, and the full check that reaches it passes no cache, so
P16's digest is not computed at all. It also cannot be profiled from outside:
`jstack`, `jcmd` and `SIGQUIT` are all refused, because the thread does not
reach a safepoint. Finding out what the kernel is doing there needs
instrumentation inside the checking loop rather than a thread dump, and that has
not been done.

### F8 — resource exhaustion is its own exit code

Exit 2 means the file could not be read and 1 that a declaration was rejected.
Running out of room is neither: the file is well formed and kolla reached no
verdict, so a script that retries with a larger heap needs to tell it from a
parse failure. `Check.Failure` separates `Exhausted` from `Unreadable` and the
command line exits 3 for it.

Getting there takes more than an `attempt`. cats-effect classes
`OutOfMemoryError` as fatal and does not route it through `IO.attempt`: it goes
to the runtime, which prints the trace and exits 1 — the code for a rejected
declaration, so the one outcome a script must not confuse with a bad proof.
Matching `Left(_: OutOfMemoryError)` after `attempt` therefore never fires, and
with only that in place a 192 MB heap on the v4.35.0 `init` export exited 1
with a raw `OutOfMemoryError: Java heap space`.

So it is caught where it is thrown and rethrown as an ordinary
`RuntimeException`, which is `NonFatal` and visible to `attempt`. That forces
one more thing: the export's index tables are the largest allocation a run
makes, so exhaustion happens inside the reader, and inside `ExportReader.pipe`
the throw is in fs2's frame rather than one the command line owns. `Check` drives
the reader itself for that reason — the duplicated wiring buys a frame to catch
in. The same heap now reports `ran out of memory after 43441 declarations` and
exits 3.

An OOM thrown inside fs2's own decoding, rather than in the reader or the
kernel, is still fatal and still exits 1. The path is verified end to end
rather than by a unit test, since an `OutOfMemoryError` cannot be faked through
a cats-effect stream without becoming the fatal case again.

`--progress` notes declarations and bytes read on stderr every 25000
declarations. It is on request rather than by default so that a pipeline's
stderr stays empty, and it is on stderr so that `--json` stdout stays
machine-readable.

### P17 — a reference that did not answer is not a disagreement

`OverallAgreement.agrees` requires both sides to have reached a judgement and
to have reached the same one. What it did not distinguish was *why* a
comparison failed, so a reference that said nothing was reported exactly like a
reference that contradicted kolla.

The case that surfaced it: the v4.28.0 `mathlib-sample` nightly job. kolla
accepted all 17,240 declarations and `lean4checker` hit its 30-minute budget,
and the run printed

    DISAGREES (lean4checker error vs kolla accepted)

and exited 1. Nothing disagreed. The reference had not finished reading the
corpus, and the only honest reading of that is that there is no reference
verdict to compare against — the same situation P2 already describes for a
toolchain `lean4checker` has no release for.

So `comparable` is both sides having judged, and `referenceUnavailable` is the
reference not having judged while the subject did. `Report.agrees` excuses the
second and nothing else. The asymmetry is deliberate: silence from kolla is
still a failure, because kolla is the thing under test. Three of the four
combinations therefore still fail — a genuine disagreement, a subject that
reached no verdict, and neither side judging — and `ReportSuite` pins all four.

The 30-minute budget was also wrong for the corpus rather than merely unlucky.
`Lean4Checker.libraryTimeout` is six hours and is used wherever the worker cap
is, for the same reason: on a library corpus, finishing matters more than the
wall clock.

One thing this does not do is make the comparison stronger. A run whose
reference timed out is a kolla-only run, and the report now says so instead of
implying a reference confirmed or contradicted it. Reading `agrees` as "a
reference checked this too" is wrong whenever `comparable` is false.

### P18 — a text-format declaration has to be admittable too

`Replay.pending` gives every step a `recover`, the function that puts a
declaration into the environment without checking it. P6 uses it for a
rejection and P14 for a declaration that was not selected. For an
`ExportItem.Decl` it was `identity`, which added nothing.

That had no effect for as long as nothing admitted a `Decl`, because the
checked path builds the environment itself. `--eval` admits everything (D13),
and the NDJSON and text v2 formats carry `Info` items, so the gap only shows on
text v1, where an inductive arrives as `Declaration.InductDecl` and the
quotient package as `QuotDecl`. On such a file the environment came back with
no inductive types at all and every later reference to one was an unknown
constant — reported as `unknown constant 'Nat'`, which blames the file for
something the replay did.

`Replay.admit` fills it in: the value-carrying declarations go in with
`addCore`, `QuotDecl` through `Quot.add`, and an inductive block through
`AddInductive.add`, because its recursors are derived rather than exported and
there is nothing else to write down. Admitting an inductive is therefore nearly
as expensive as checking one, which is a property of the text formats carrying
blocks instead of infos rather than a choice made here.

The test builds a `Declaration.InductDecl` directly, because `ExportWriter`
refuses to write an inductive as text v1 at all — `requireNotV1` — so the shape
cannot be produced by round-tripping an NDJSON fixture through the writer. With
`identity` restored the environment has no entries and the term fails with
`UnknownConstant: Flag.up`, which is what makes the test a guard rather than a
description.

### P19 — a reference that could not run has not rejected anything

P17 stopped a reference with no verdict from being read as a disagreement.
This is the other half: deciding which non-zero exits are verdicts at all.

`Lean4Checker` mapped every non-zero exit to `Verdict.Rejected`. Most non-zero
exits are not rejections. `elan run` fails when a toolchain will not download,
`lake env` fails when a build is missing, the binary can be absent — and none
of those has looked at the corpus. A v4.28.0 CI job failed with

    v4.28.0 / case-eta / jvm: DISAGREES (lean4checker rejected vs kolla accepted)

and the reason underneath it was

    error: could not download file from
    https://releases.lean-lang.org/lean4/v4.28.0/lean-4.28.0-linux.tar.zst

The reference had not rejected `case-eta`; it had never started. Read at face
value that output says kolla accepts something Lean's own kernel refuses, which
is the most serious thing the platform can report, and it was infrastructure.

`Lean4Checker.rejected` is the discriminator: `main` prints
`lean4checker found a problem` before rethrowing (P4), so that marker in the
output is what separates a verdict from a failure to produce one. Without it
the run is an `Error`, which P17 then reports as no reference verdict. With it,
a genuine rejection still fails the comparison exactly as before.

This is narrower than it looks. It only decides how a non-zero exit is
labelled; it does not make a missing reference into a passing one, and a
reference that rejects while kolla accepts still fails the run. What it stops
is a transport failure wearing the costume of a disagreement.

## Frontends

### F1 — the checking is one implementation, the driver loop is three

`kolla.leanexport.Replay` replays an export file's declarations into an
environment one step at a time and has no effect type of its own. A step is one
declaration, or one whole inductive block, which has to be added at once since
the kernel derives its constructors and recursors together.

The three frontends differ only in how they interleave. `cli` wraps it in `IO`
with an `IO.cede` every 32 declarations. `difftest` does the same and records a
verdict per declaration. `web` runs it in slices on the browser's event loop.
If the loop were the shared part instead, each frontend would carry its own copy
of the block grouping and the hoisting pass, and the three could disagree about
what kolla accepts.

`ReplayTally` is shared for the same reason: "accepted" means one thing, and the
command line's exit code, the browser's banner and the platform's verdict all
come from it.

### F2 — the browser slices by time, not by count

`web.Main.sliceMillis` is a time budget per animation frame, not a number of
declarations. Declarations differ in cost by orders of magnitude — one `String`
theorem outweighs a thousand constructors — so a count either stutters on the
expensive ones or wastes frames on the cheap ones. A single declaration is still
atomic: a slice can overrun its budget by whatever one step costs, and nothing
can be done about that without splitting the kernel's own work.

### F3 — the page builds itself

`web/index.html` loads the bundle and declares nothing else; `web.Layout` creates
every element. The ids `web.Main` writes to are therefore the ids that exist, and
renaming one cannot leave a dangling lookup in markup nobody compiles.

`scalajs-dom` is not among the dependencies the project allows, so the handful
of browser calls are declared in `web.Dom`.

### F5 — the platforms are compared per declaration, not by a count

`Platforms` runs the native binary, the bundle under Node and the page in
Chromium, and reads their verdicts back through `ReplayJson`, the one wire
format all three write. They are then compared with `Compare.platforms`, which
is per declaration. A count would hide two platforms rejecting different
declarations and arriving at the same total.

That comparison is why `ReplayJson` lives in `export` rather than in `cli`: if
the browser and the command line each spelled their output, a difference in the
spelling would read as a difference in the verdicts.

The browser run goes through `web/smoke.js`, which drives the page the way a
person does — fill the box, pick the profile, press the button — and checks
that what the page displays agrees with what the checker concluded before
printing the verdicts. A page that renders a count it did not compute is a bug
the JSON alone would not catch. It does not use `page.fill`, which types the
value through the input pipeline and takes minutes on a multi-megabyte export.

Exit codes differ in meaning and the runner is told which: `kolla --json` uses 1
for a rejection, which is a verdict, while `smoke.js` uses 1 for a page that
misbehaved, which is a failure, and 3 for Playwright not being installed, which
is neither.

### F7 — the native build is not the one to run a library corpus with

On `init` — 59,349 declarations from 6.5 million export lines — the JVM peaks
at 3.0 GB of heap and finishes in 49 seconds. The native binary does the same
work with a peak memory footprint of 51.6 GB and takes about 13 minutes. On
`std`, half again as large, it had reached 6.5 GB of resident memory after 43
minutes without finishing, and exhausted a 48 GB machine.

That inverts the small-corpus result, where native is usually the faster of the
two: on the handwritten corpora it runs at 0.1x to 3x the JVM's time. The
crossover is somewhere between a few thousand declarations and sixty thousand.
The likely cause is the collector — Immix against a generational one, on a
workload that allocates an `Expr` per node of every term it reads — but that is
a hypothesis, not something measured here.

What follows for the platform comparison is only that it runs on the committed
fixtures (F6), which are thousands of declarations rather than tens of
thousands. A library corpus is checked on the JVM.

### F6 — a committed export is a corpus

`Corpus.fixtures` makes each file under `difftest/test/resources` a corpus with
its export already built. Those are real lean4export output, so comparing
kolla's builds against each other on them needs no Lean toolchain and no
network: the platform comparison runs on every push in seconds, while the
toolchain matrix runs per release. Both NDJSON format versions are represented,
so the 3.0.0 reader is covered on every platform too.

### F4 — the command line is `fs2.io.file`, not `java.nio`

`cli` is cross-built for the JVM and Scala Native, so it is subject to the same
rule as the other cross modules: no JVM-only APIs. Reading a file is
`fs2.io.file.Files`, and `-` is standard input, so one source builds both.

Exit codes are 0 for a file whose every declaration was accepted, 1 for a
rejection, and 2 for a file that could not be read — a distinction a caller
needs, since an unreadable file is not a proof of anything.

---

kolla — Örjan Lundberg and
[Anthony Lundberg](https://www.linkedin.com/in/anthony-lundberg2/)
