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

## Hand off to Lean or Bend

- Induction the prover would have to invent (a recursive structure whose proof needs an unstated lemma).
- Products of unknowns beyond multiplying two known facts. (Integer arithmetic with induction or products is
  undecidable; no automatic prover closes all of it.)
- Reals, and datatypes beyond flags, choices, optional facts, bounded naturals, strings and sets (or encoded as a
  number a Lean function decodes).
- Shipping an arbitrary algorithm as its proved source: Bend compiles the proved program itself; gdp-wired ships the
  rule as JavaScript.

Each "does not" has a route: a ghost (sums across a map's keys), a bound with
skips (spec steps that vary), an encoding (strings, datatypes as numbers), or
Lean itself ([Lean handoff](lean-handoff.md)).

## Trust

The kernel (`kernel/kernel.ts`, `core/check.ts`) is the only trusted code; the
prover, builders, runtimes and GPU searches are untrusted and checked against it.
The kernel's Lean twin is proven sound with the standard axioms only.
