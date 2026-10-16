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
