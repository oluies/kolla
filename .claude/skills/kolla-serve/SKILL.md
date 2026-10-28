---
name: kolla-serve
description: Check Lean 4 proof candidates against a resident kernel instead of paying for the library once per question. Use when iterating on candidate proofs, when a check has to answer in bounded time, or when you need the type, the value, the dependants or the axiom closure of a constant without going back to Lean. Covers the request protocol, the deadline, and how to read a reply.
---

# kolla --serve

A resident Lean 4 kernel. It loads an export once and then answers requests on
stdin, one line each, replying with one JSON object per line.

Every other mode of kolla builds an environment, answers one question and
throws it away, and the environment is what costs: 90 seconds for `init`, 83
seconds to read and admit Mathlib. Loading once turns each later question into
the cost of its own declarations — milliseconds for most.

## Starting it

```bash
kolla --profile v4.35.0 --serve init.export      # preloads the file
kolla --profile v4.35.0 --serve                  # empty; use `load`
```

The profile has to match the Lean release the export came from, or the verdict
is about a kernel that did not produce it. `kolla --profiles` lists them.
`--serve` rejects `--cache` and `--check`; a resident environment carries no
digest cache, and a check request names its own file.

## Requests

| request | what it does |
|---|---|
| `load <file>` | check an export and keep what it built |
| `check <file>` | check an export against the base and keep nothing |
| `axioms <name>` | the axiom closure, with `sorryAx` and the unusual ones apart |
| `gate <name> <a,b,c>` | whether it rests on anything outside that set |
| `type <name>` | the type of a constant |
| `unfold <name>` | a definition's value |
| `names <prefix>` | what is declared under a prefix |
| `mentions <name>` | which declarations reach that constant |
| `eval <term>` | reduce a term against the environment |
| `deadline <ms>` | bound each declaration by the clock; `0` removes it |
| `status` | profile, declarations, deadline, requests served |
| `quit` | end the session |

## The loop this is for

Elaborate a candidate with Lean, export the closure of its new theorem, then
check it against the base:

```bash
lake env lean -o Candidate.olean Candidate.lean
lean4export Candidate -- My.New.Theorem > candidate.export
```

```
check candidate.export
{"op":"check","ok":true,"kept":false,"accepted":11,"rejected":0,"carriedOver":320,"declarations":59349,"reason":null,"ms":17}
```

`accepted` is what was new, `carriedOver` what the base already held and did
not need checking again. A candidate costs its own declarations, not the
library's.

## Reading a reply

- `ok` is the verdict for that request, not whether the request parsed.
- `reason` names the first declaration that did not pass, and why. A count says
  a candidate failed; the reason says whether it was ill-typed or ran out of
  time, and in which constant.
- `kept` says whether the session's environment changed. A `load` keeps what it
  built **only if every declaration passed** — a rejected one is still carried
  into the environment a replay returns, and keeping that would leave the base
  resting on something the kernel refused. A `check` never keeps anything.
- A failed request answers `"ok": false` with an `error` and the session
  continues. Unknown operations, missing arguments, unreadable files, unknown
  constants and unparseable terms are all answered, not fatal.

## Bounding the wait

`deadline 250` bounds each declaration by the clock. Reach for it rather than
`--max-steps`: there is no conversion from reduction steps to milliseconds, and
the step cost of a declaration is not known before checking it.

When a declaration runs out of budget, the reply's `reason` carries the report
the kernel builds for exactly this — the `is_def_eq` and delta counts and the
constants the reduction kept reaching for. "Diverging in `Set.ofPred`" is
something to act on; "timeout" is not.

The deadline is a floor, not a ceiling: the clock is read every 256 reduction
steps, so a declaration is stopped at the first step boundary after its budget.
It bounds one declaration, an inductive block included, and the largest value
it takes is 9,223,372,036,854 ms — above that the milliseconds would wrap, so
the request is refused.
Setting it also turns on the per-constant diagnosis that makes the report
useful, which costs about 28% on a library-scale run; the clock itself costs
about 4%.

## What it will not do

It is a kernel, not a prover: there is no elaborator, no tactics, no
surface-syntax parser. Candidates still have to be elaborated and exported by
Lean, and that is where the time goes — 145 seconds to elaborate one
Mathlib-importing file against 21 seconds to check its whole 17,669-declaration
closure. kolla's leverage is on the verify-and-interrogate side of the loop.

See `docs/semantics.md` S1, S2 and S3 for why each of these behaves as it does.
