# Lane F handoff: unvalidated 15.6 prototype

Coordinator moved 15.6 to Lane F after this prototype and its check had already been submitted. Lane B will not continue row-scheduling work. This commit is an optional starting point, **not an adopted policy or a proof of a speedup**.

Files:
- `section15-row-probe.ts`: scoped capture of a validated numeric model, model-based choice among existing row pairs, counters.
- `section15-row-variant.ts`: disposable Linux-only patch. `before` records callback/cache/mirror counters. `after` tries an unsplit root, then model-selected existing equalities, depth <=2, both branches checked through the existing route, and the eager fallback. Models select a split; they add no logical assumption.
- `section15-row-probe.test.ts`: model-selection and nested-probe tests.
- `section15-row-check.sh`: applies 15.4, 15.5 and the row prototype in a disposable copy, then typecheck/lint and targeted tests. It changes root-provable callback-count expectations to one, and keeps the mirror test by making its callback decline the unsplit root. Proof acceptance/rejection checks remain.

Already running: `runs/track-m/lane-b-row-check-v1`, task `885371f9-bf41-4828-a5a0-0d9608158874`, submitted with `research/track-m/jobs-lane-b-row-check.json`. Do not duplicate it; result is pending at handoff. No row-policy measurement batch was submitted.

To use in another runner, apply `section15-row-variant.ts before|after` after the leaf/class variants, before importing the prover. Import `rowProbeStats` into that process and record its snapshot at the end. The original root-first prototype only handles callers that reach `proveRowCases`; write-free operations that bypass it still need F's own coverage analysis.

Review before using: the root probe is bounded by the existing leaf callback allowance; a model-free failure takes the existing eager fallback. Internal probes can add queries even when terminal depth is <=2. Compare **all uncached queries**, not just terminal leaves; reject a regression under the design's falsifier. No complete-family, real E-14, or gate claim is supported.

Follow repository/PR rules. Run all nontrivial work through `supercomputer`; read `supercomputer --skill` first. Use one waiter per job, exact PIDs for stopping, preserve raw failures, and never modify the kernel or allowances under this experimental flag. Only Lane D's exact-roster, pair-identity, both-SHA-bound, CPU-labelled final receipt can support GATE GREEN.
