# D handoff: opt-in request quotient

## Pin and scope

Review **bfe647cfd3b81e10c497ca4d5911a8097a02586b**, parent
`4c1c05dc4c41003f0c2e4fc800c6f25cf8195a03` (D's scoped release GREEN).
Only the runtime/test change in `runtime.patch` is proposed:

- `core/exists.ts`: preserve logical trial accounting; cover a class only on success.
- `core/request-quotient.ts`: conservative selector-aware read sets and stable classes.
- `core/request-quotient.test.ts`: dependency, sample, refusal and endpoint controls.

No checker/Lean/interpreter/prover-price edits. The evidence scripts are not
runtime code. `GDP_REQUEST_QUOTIENT=1` enables the feature; default is unchanged.
Lane A was told these exact owned paths; this does not absorb A's rejection work.

## Completed gates

- Exact-pin 84-receipt census, 28 originals off/on/on: 10 checked / 18 unknown,
  all old checked verdicts retained, zero forbidden clocks.
- Eight completed original candidate families match ordered hashes; no assertion
  about families that the baseline did not reach.
- Maximum 15,001,010 within the inherited 15M+1,024 slack.
- All 28 off full-mode receipts match the release baseline exactly after timing
  and source-label normalization; all 28 repeated on receipts match.
- All 28 separate legacy controls match the release baseline including all 26
  counters, with the six full-work additions zero. No new use of the release's
  earlier nine-case counter exception. Legacy controls are not clock-tripwired.
- Independent audit, five rehashed mutation controls, source unit tests and
  standalone Lean proof pass. Proof boundary is stated in `SOUNDNESS.md`.
- Required exclusive **9950X xlarge** same-VM ABBA is independently audited:
  generation 6,243.38 → 4,320.58 ms mean, 43 candidates identical, zero proof
  queries. Raw units 36,731,970.10 → 32,913,227.00, including quotient setup.

Full raw logs and placement: `results/{census,legacy,audit,legacy-audit,
pilot-v4,timing-9950x,final-audit-initial}`. The `final-audit-initial` directory
contains the successful timing audit and a failed initial legacy-field check;
`legacy-audit` is its corrected strict comparison. No receipt was rewritten.

## Completed additional audit

Fable Q1 and its independent summary pass for **29 models / 49 parameter runs**:
**2,400,700 skipped requests** independently interpreted, **2,099,352** identical
successors, **301,348** refusals, zero distinct successors. All finite sample
digests match. Hooks exist only in disposable source copies and are bound to
the original sampler hash. This is not a timing or 15M-budget receipt.

Follow-up tests pass for **525 selector/target combinations**, **3,366 concrete
successors** and **180 bulk defaults**, including an unread map adding key 100.
Final whole-tree type/lint passes **1,853 files**. The earlier adapter syntax and
bounded-index type failures are retained; no production source changed.
See `results/{skipped,skipped-audit,selector-default-edges-initial,final-types}`.
All owned batches are terminal. Both source and evidence messages pass commitlint.

## Review boundaries

This is a gated integration source, not D approval or calibrated W performance.
The cap's maximum leaves only 14 provisional units before the 1,024 slack limit;
recheck it after any weight fitting. The full-generation timing is intentionally
unbounded in work and is not a 15M run. Fable reconciled its old 49-law lane-B
ledger with this different current 43-law prefix; no cross-tree timing equality
is asserted. No end-to-end 60-second MLDR proof is claimed.

Refusal caching (read sets extended by guards) and quotienting random walks are
not implemented. Those are separate changes with separate gates. No main
merge/push and no changes under `.reflex-saved/`.
