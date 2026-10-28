---
name: kolla-audit
description: Find out what a Lean 4 declaration actually rests on — whether a theorem is a proof or a `sorry`, and which axioms it depends on. Use before reporting a formalization as proved, when grading your own or someone else's Lean output, when auditing a repository's claims, or when all you have is an export or an olean you did not build. Source reading is not equivalent and this skill says why.
---

# Auditing what a declaration rests on

Type-checking answers whether a declaration follows from what the file
declared. It does not answer what the file declared. `sorry` elaborates to the
`sorryAx` axiom, so **a theorem with no proof type-checks exactly like one with
a proof**, and every checker accepts both.

```bash
kolla --profile v4.35.0 --axioms My.Theorem export.ndjson
```

```
My.Theorem rests on 4 axiom(s), reached through 17183 constant(s)
  Classical.choice  (Lean's trust base)
  Quot.sound  (Lean's trust base)
  propext  (Lean's trust base)
  sorryAx  <- NOT A PROOF: left as sorry
```

Exit 0 when nothing unusual, 1 when it rests on `sorryAx` or on an axiom
outside the three Lean ships, 2 when the name is not in the file. A verdict
outranks a misspelling: 1 wins over 2. `--json` gives the same as one object.

**Measure the exit code without a pipe.** `kolla … | head` reports `head`'s
status, which is 0.

## Gating on a set you name

```bash
kolla --profile v4.35.0 --axioms My.Theorem \
      --require-axioms propext,Classical.choice,Quot.sound export.ndjson
```

"Nothing unusual" is a judgement — that depending on Lean's three axioms is
unremarkable. True of ordinary mathematics, and not something to assume on
someone's behalf. `--require-axioms` states the set instead, and an empty list
permits nothing, which is how to ask for a proof resting on no axiom at all.
This is the criterion a `leanprover/comparator` challenge states in its
`permitted_axioms`.

In a session, `gate <name> <a,b,c>` is the same question.

## Why source reading is not this

Grepping for `sorry` finds a `sorry` in the file you thought to open. It does
not find one in a dependency, and there is nothing to grep when what you have
is an export or an olean someone else built. The axiom closure follows both the
type and the value, so it catches both.

A worked example from this repository's history: `openai/math` states results
in `lean/ComparatorChallenges/*.lean`, and all 418 of those files contain a
`sorry` — by design, since they are challenge *statements* and each JSON names
a separate `solution_module` holding the proof. Reading only the challenge file
would have you report the opposite of the truth in either direction. Checking
the exported closure says which one you have.

## Checking a whole file

```bash
kolla --profile v4.35.0 export.ndjson          # 0 accepted, 1 rejected, 3 out of room
kolla --profile v4.35.0 --check My.Namespace export.ndjson
```

`--check <prefix>` admits everything outside the prefix unchecked and says how
many, so the verdict covers the selection rather than the file. Read the
counts: `carried over` is admitted-not-checked, which is not the same as
accepted.

The profile must match the release that produced the export. An export is
accepted under its own profile and generally rejected under the others, which
is what the profiles are for.

## When a check does not finish

```bash
kolla --profile v4.35.0 --max-time 2000 --trace export.ndjson
```

`--trace` names each declaration before it is attempted, so the one that never
returns is still named. `--max-time <ms>` and `--max-steps <n>` end a
declaration and report where the reduction went — the constants it kept
reaching for, with attempts against cache misses. Prefer `--max-time` when you
have a deadline; steps do not convert to seconds.

For many questions against one library, use the `kolla-serve` skill instead:
loading is the cost, and it is worth paying once.

See `docs/semantics.md` A1 and S3.
