# Pinned historical baselines

## Paxos milestone 2

- Engine: `444ece6ebe42d202150bc583c0c55b626b4e32c9`, tree
  `517d8462ade04456254dc6db0e6132cc4bae94ce`.
- Complete six-law `published('paxos_epr')` context; each focus first in a fresh
  constructor invocation. `proveRule(...,{search:false})`, 25,000 ms cooperative
  outer wall, unchanged defaults. The serialized observer event, not a later
  `r.machine` getter, supplies the replay machine and ordered laws.
- `runs/astra-history-m2`: batch `20261104-095436-sb5v1k`, uploader tree
  `2eaae4c2abef`, worker exit 0. All four historical positives P1/P2/P4/P5 have
  fresh start AND step kernel replay, including source-witness freshness checks.
  Both expected opens remain open at step. This reproduces the per-focus baseline,
  not a proof of the full conjunction. Other clauses in a focus invocation can
  exhaust the remaining budget; their incidental statuses are not substituted for
  their own focus invocation.
- Accepted matcher enabled AND disabled reject both full failed goals at `if`.
  No hypotheses removed, no saved-model result promoted to a milestone flip.
- Full failure goal hashes: safety
  `58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca`;
  P3 `a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357`.
  Their complete serialized attempt inputs are retained in `inputs/m2/`.

## Q3 saved-model fixture (distinct from milestone 2)

- Exact instance: `paxos-P5-19`, original source
  `Astra gen/mldr-astra runs/ground-truth/snapshots/paxos-P5-19.json`.
- Wrapper SHA-256:
  `98bbf35993c89be329a58b31beb8f256cc68f14837007da1fd77792095a7363b`.
- Historical missing instance: Vote(1,7,0) implies Proposal(7,0), published P2.
  Q3 already reported blocking this model with its untrusted MBQI changes.
  Reblocking it cannot be claimed as a new historical whole-obligation success.

## TIP

- Exact instance `prod/lemma_09.smt2`: 612 bytes, SHA-256
  `225ccffbf1a98c7334f6be2d86e13efe07ce707e1fcaa8b3b5dd6b4869654888`.
  Full theorem: `rev(x ++ (y ++ [z])) = z :: rev(x ++ y)`.
- Actual archived experiment `local-laws-depth2`, original receipt
  `c8cc165be0fe6fae92475397840f335c7c7bf3fd28aa74b792d2d775528fd6a4`:
  both generated association and reverse-snoc helpers checked; root unknown after
  two attempts, 7836.286666666667 counted ms, 20,000 counted-ms enclosing budget.
  The original jobs requested 4 CPU / 14336 MiB / 120 s; this lane does NOT inherit
  or escalate to those resources. New 2 CPU / 4096 MiB diagnostics are not timing
  or resource-parity comparisons to that historical run.
- Original `local-laws-depth2.ts` edits `core/data.ts` to export private
  `bounded`, `dataRate`, `proveWith`, and injects `core/data-goals.ts`. It is retained
  but NOT executed: this lane forbids core/kernel edits. Exact reproduction of that
  dirty exploratory harness is therefore a stated limitation, not an invented
  successful baseline. Its original source/receipt hashes are in the extracted
  manifest under `runs/astra-history-selected/artifacts/`.
- Historical notes explicitly correct an earlier zero-use report: a BAD REGEX
  missed existing matching. Do not claim that e-matching itself is newly possible.
- Git objects for datatype/solver/kernel/TIP translator code are identical between
  main `9753cce0` and the accepted `662a1c07` experiment. The current same-engine
  paired adapter experiment uses the complete original TIP statement and the exact
  two helper formulas also preserved in `compare/tip/lemmas-sample30.json`.
  Helpers are re-proved, never installed as axioms. Hints remain explicit.

## Archives and evidence scope

The store manifest was inspected before retrieval. Only Q3 and RL archives were
read on boat, with full SHA-256 checks, and only selected small files materialized.
Metadata read v2 returned a short HTTP body and correctly failed its hash assertion;
v3 resumes ranges and rechecks. All original logs/runners remain. The owned store
server `bx_ex5negf7` was explicitly deleted after extraction; no shared VM stopped.
Raw candidate-member lists retain the exact archive member selected for each
fixture in `runs/astra-history-fixtures/archive-fixtures.log`.

All current runs are preliminary, untimed correctness diagnostics. Requested
resources and cooperative caps are not hard CPU/RAM guarantees. No native/full-gate
acceptance exists yet. Sol's native producer work and its pending outer-attempt
admission contract remain a separate prerequisite for final end-to-end acceptance.
