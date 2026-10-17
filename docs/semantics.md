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
