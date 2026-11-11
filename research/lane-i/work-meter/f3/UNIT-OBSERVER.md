# Weighted F3 observer — not yet full F3

`unit-snapshot.ts` and `unit-publisher.ts` mirror all 20 integer counters.
`unit-observer-worker.mjs` reads them every 100 ms, computes their weighted sum
in the production meter's summation order, and obtains an inspector stack for
observed silence longer than 250 ms. This is diagnostics only, not a budget.

## Why a new observer

Raw activity is insufficient: a zero-priced operation can keep raw counters
moving while the budget's units do not advance. The first fenced prototype
also starved under continuous zero-price writes: all 13 attempted snapshots
were invalid. Those failures are preserved in `runs/lane-i/unit-observer-controls/`
and `runs/lane-i/unit-observer-controls-diagnostic/`; they are not qualifications.

The corrected single-writer publisher stores each nonnegative safe integer
with `Atomics.store(BigUint64Array, ...)`. The reader performs monotone atomic
component scans. Two scans are not claimed to be simultaneous snapshots;
each component and the nonnegative weighted sum cannot decrease. No global
writer fence can prevent observing a zero-priced busy loop. Resets, unsafe
values and sequence rollover permanently invalidate that run.

Boat controls passed in `20261111-021349-fb0zo5`:
- Silent main thread: timestamp-valid named-loop capture.
- Continuously increasing zero-price counter: timestamp-valid named-loop capture.
- Priced counter: units advanced and no stable silent window was reported.
Full raw profiles are hash-bound and independently decoded/reselected by the
control audit. Only the later retained-evidence run embeds selected archives
in the job log; the first passing control audited temporary profiles in place.

## Lane D integration

Use `installUnitPublisher(coreMeter, costs, eprMeter)`, then pass its `buffer`
and an explicit 20-element `weights` array to the worker. The weights MUST be
`legacyWeights.map(([,w])=>w)` followed by the eight active extra weights in
`extraWorkKeys` order. Never substitute all-one fixtures for calibrated W.
Set `new Int32Array(buffer,0,4)[1]` using Atomics: 1 while the solver runs, 2 on
completion. Always stop/terminate the worker and call `restore()` in finally.
The final counter values and data property descriptors are preserved.

Run this as a separate F3 diagnostic, NOT inside the calibration timing fit:
publication and profiling have overhead. Require the same original input,
source, coefficients, raw totals, verdict and phase totals off/on. Profile
archives cap at 8 MiB raw each, 1 MiB gzip each, 2 MiB total; overflow is a
failure, never an excuse to drop evidence. Sixteen captures is an explicit
coverage cap; hitting it forbids a complete-coverage claim.

Current controls establish Node capability only. Original-model weighted
coverage, Bun main-thread capture and qualified-reference-host F3 remain open.
