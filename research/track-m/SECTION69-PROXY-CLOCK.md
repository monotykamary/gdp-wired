# Section 69 — plain search policy / native work accounting

**Source implementation only; tests written, not run.** Base: `84b9b3850c7063d674dab172c8dda9ef6ce91eab`. Implements C section 69.8 and D `c5344d9ee` design approval. Neither approval is a source acceptance, gate result or launch authorization.

## Contract and scope

- `core/search-policy.ts` reads the twelve existing `legacyWeights` counters from the authoritative ledger, in declared order. It adds no counter, charge, weight, admission, grant or lease.
- The default proxy clock is that projection / 250. Existing `counted(rate, ..., full)` regions retain row (`work.n / rate`) versus model (projection / rate) selection and nested inheritance. No fitted factor and no wall-clock control fallback.
- `proveRule` is the sole new scope entry. Its existing actual-machine counts test is evaluated once, as before; the resulting boolean now also chooses policy. A counted parent locks all nested public calls to native policy. A counted public child temporarily suspends a proxy parent. `finally` restores the previous frame.
- Separate proxy state holds soft deadlines, EPR anchors, wall limits, rate and work cap; native/legacy globals are not reused. Standalone other public APIs are not newly opted in; helpers inherit their caller's scope and never select a policy themselves.
- This is a **new heuristic**, not an exact replay of legacy execution. Full accounting's FM progress differs from legacy bulk precharge, and legacy wall time is not reproducible. Early soft UNKNOWN remains possible; root expenditure or recovery of any original is not guaranteed.

## Source seams

- `kernel/prove.ts`: conditional proxy clock/counting/polling/soft-bound behavior. `searchWork` and `withSearchWork` name heuristic readers/caps explicitly. Ground-search, EPR/core fallback, wide-search, CDCL and model-search caps use those helpers.
- `core/dsl-deadline.ts`: the fourteen DSL deadline sites inherit polled proxy deadlines; allowance/wall wrappers create no ledger endpoints in proxy scope. No allowance constant or residual fraction changes.
- `core/infer.ts`: heuristic full-work terms, engine reset and join cap explicitly use `searchWork`/`withSearchWork`. Its diagnostic `full` still reports authoritative `fullWork`. Fixed subquery budgets remain unchanged.
- `withBudget`, including a quota opened while proxy state is active, still opens a native ledger budget and checks entry/completion. That nested native quota does not establish a heuristic counted region. `withWork`, `checkWorkEndpoint`, `checkWorkAdmission`, `remainingWork` and `fullWork` retain native admission/accounting behavior.
- No changes to the ledger, its 26-counter vector, weights, charge sites, leases, count allocations, caller/root conversion, proof checker, physical resource limits or instrumentation flags. Existing hard endpoints remain enforced by admission even though `budgetEnd()` in proxy scope does not expose them as proxy time.
- Native count code is excluded at public entry, including its shared inference calls and clock-to-grant conversions. No new opt-in flag.

## Focused validation to request

The existing ledger/refusal/deadline tests plus `core/search-policy.test.ts` cover projection, row/model inheritance, native-parent locking, exception restoration, soft expiry without ledger refusal, explicit native quota/cap refusal, and no wall-clock control. Fresh full and legacy processes; unmodified repository typecheck. Bounded counted fixtures compare old/new outcomes and exact ledger receipts. Repeated scoped runs use identical inputs/state. No additional full MLDR run. These are tests, not a formal proof.

MLDR declares counts. Its new-pin equality is **unconfirmed** until the authorized MLDR measurement is compared with the retained 84b9 baseline, including exact W. Do not promote the prior 288G-root measurement into a 24G-root result.

## Latest Main scheduling order

The next measurements are two separately sealed batches, started in parallel once D grants each exact seal:

1. The fifteen originals, **1200 seconds per-item outer guard**.
2. MLDR separately, with its existing root and guard unchanged.

MainScheduled=true under Main's current USER ORDER; no further Main round-trip after exact D GO. Do not launch before focused/source acceptance and exact packet GO. A guard hit is censored, not a proof failure or success. No retry, root/guard increase or extra full-MLDR control. Preserve all previous results. Calibration HOLD; G2 remains source-only.
