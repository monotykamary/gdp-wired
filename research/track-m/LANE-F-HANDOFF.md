# Lane F handoff: unvalidated 15.6 prototype

Coordinator moved 15.6 to Lane F after this prototype and its check had already been submitted. Lane B will not continue row-scheduling work. This commit is an optional starting point, **not an adopted policy or a proof of a speedup**.

Files:
- `section15-row-probe.ts`: scoped capture of a validated numeric model, model-based choice among existing row pairs, counters.
- `section15-row-variant.ts`: disposable Linux-only patch. `before` records callback/cache/mirror counters. `after` tries an unsplit root, then model-selected existing equalities, depth <=2, both branches checked through the existing route, and the eager fallback. Models select a split; they add no logical assumption.
- `section15-row-probe.test.ts`: model-selection and nested-probe tests.
- `section15-row-check.sh`: applies 15.4, 15.5 and the row prototype in a disposable copy, then typecheck/lint and targeted tests. It changes root-provable callback-count expectations to one, and keeps the mirror test by making its callback decline the unsplit root. Proof acceptance/rejection checks remain.

Already running: `runs/track-m/lane-b-row-check-v1`, task `885371f9-bf41-4828-a5a0-0d9608158874`, submitted with `research/track-m/jobs-lane-b-row-check.json`. Do not duplicate it; result is pending at handoff. No row-policy measurement batch was submitted.

Later receipt: both jobs passed on snapshot `965b67b87d4e`. Default ran 31 tests / 310 assertions plus 7 / 33; the disposable row prototype ran 37 / 277, with typecheck/lint passing. Logs are in `runs/track-m/lane-b-row-check-v1`. This validates the handed-off prototype only, not Lane F's subsequent implementation or any speedup.

To use in another runner, apply `section15-row-variant.ts before|after` after the leaf/class variants, before importing the prover. Import `rowProbeStats` into that process and record its snapshot at the end. The original root-first prototype only handles callers that reach `proveRowCases`; write-free operations that bypass it still need F's own coverage analysis.

Review before using: the root probe is bounded by the existing leaf callback allowance; a model-free failure takes the existing eager fallback. Internal probes can add queries even when terminal depth is <=2. Compare **all uncached queries**, not just terminal leaves; reject a regression under the design's falsifier. No complete-family, real E-14, or gate claim is supported.

Follow repository/PR rules. Run all nontrivial work through `supercomputer`; read `supercomputer --skill` first. Use one waiter per job, exact PIDs for stopping, preserve raw failures, and never modify the kernel or allowances under this experimental flag. Only Lane D's exact-roster, pair-identity, both-SHA-bound, CPU-labelled final receipt can support GATE GREEN.

## Original-34 Inv1758 early-entry trace (2026-11-09)

Lane B's new direct `proveFocusedCounts` diagnostic bypasses the ordinary model-refinement loop without changing the model, laws, kernel, or your row scheduler. On the exact original-34 family, it reaches field/row cases but is still unknown. See `runs/track-m/lane-b-early-focus-v1/receipts/rows-classes/raw/run/rows/summary.json` and the retained source hashes.

The full 6,000-unit / 7-second call with 15.4 helper allocation plus 15.5 class ordering returns unknown at 6,002.553 units / 6,040.223 ms. It proposes case trees for op 0, 2 and 3; active field/row leaves for op 1, 4, 5 and 6 remain unresolved before their fallback queries/grows. These are proposals, not accepted independent branch proofs. There are **zero derivability-closure or derive-class events**: the 15.5 ordering does not run on this route. `deriveCountClosure` returns before class ordering when the live claim references fewer than two count reads (`core/count-recovery/derivability-closure.ts:42`); this target has a field-only claim. Lane B has not modified your row code.

The baseline early call is wall-limited at 2,679.971 units / 7,018.544 ms, so it is not a same-budget cost win. The one-third-unit early call also consumes its full wall; Lane B has queued a dual unit/wall bounded correction and exact-model replay. The protocol-level Inv1758 proof remains open.
