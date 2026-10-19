# Where it fits

| | gdp-wired | Lean | Bend |
|---|---|---|---|
| What it proves | Laws about stateful rules | Anything you write the proof for | Programs that carry their proofs |
| Proof you write | None | The proof | The proof, in the program |
| Budget rule, `s ≤ b + m` | 1 line (`proveRule`), 25 ms | 8 proof lines, 488 ms | 84 proof lines, 137 ms |

Numbers: `compare/README.md` in the gdp-wired repo (one Modal run, median of 5, whole command).

## Use gdp-wired for

- Budgets, caps, quotas, rate limits, sliding windows, ledgers, escrows, workflows, approvals, access policies,
  entitlements: anything that is params + requests + state + a step.
- Invariants, per-key laws, one-step and k-step laws, histories, orderings at any distance (ghosts), liveness under
  fairness, refinement, decisions over a request, noninterference between two requests.
- Laws that must keep holding as the code changes: the proof reruns in milliseconds.

## Pair it with gdp-ts

gdp-ts holds every call site to a check; gdp-wired proves the check. Where a codebase demands gdp-ts proofs, mint them
from a proven `guard` or `gate` ([with gdp-ts](gdp-ts.md)): the policy is proven, and no caller can skip it.

## Hand off to Lean or Bend

- Induction the prover would have to invent (a recursive structure whose proof needs an unstated lemma). A
  recurrence on one natural whose lemma you can state stays here: `recur` proves the lemma by induction.
- Products of unknowns beyond multiplying two known facts. (Integer arithmetic with induction or products is
  undecidable; no automatic prover closes all of it.)
- Reals, and claims about a recursive structure that need a lemma nobody stated (or encoded as a number a Lean
  function decodes). Records and variants stay here, as values, in maps and in lists (`record`, `variant`, `.maps`,
  `.items`), and so do lists a request carries with folds over them (`.carriesList`), folds over a tree given as a
  value (`fold`, `proveFold`, any number of children with `.children`), and trees and lists of lists in a rule's state
  as tables of nodes (`.nodes`).
- Shipping an arbitrary algorithm as its proved source: Bend compiles the proved program itself; gdp-wired ships the
  rule as JavaScript.

Each "does not" has a route: a ghost (sums across a map's keys), a bound with
skips (spec steps that vary), an encoding (strings, datatypes as numbers), or
Lean itself ([Lean handoff](lean-handoff.md)).

## Trust

The kernel (`kernel/kernel.ts`, `core/check.ts`) is the only trusted code; the
prover, builders, runtimes and GPU searches are untrusted and checked against it.
The kernel's Lean twin is proven sound with the standard axioms only.
