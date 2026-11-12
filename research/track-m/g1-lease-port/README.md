# G1 and owned replay on A's lease base

This is a source-regression check, **not** a calibrated budget, a b_min sample, production qualification, or activation.

Base: `ab99a14d` (full identity and child commits are bound after the source gate). Existing 48d879fa/50432 plumbing is retained. The production delta only transports the existing composition-only G1 option through the fresh load rebase/replay fallback. The extracted untrusted helper allows a direct real-rebase-miss test. No kernel, owner-plan, controller, budget-ratio, or flag-default changes.

Two children: (1) G1 fix + explicit lease/negative/native tests; (2) existing owned-replay lease regression coverage + this paired harness. A's overlapping worktree is not edited.

## Gates

V1 `20261112-002903-3o1zlm` is retained as FAIL: 27 tests/127 assertions passed, but typecheck rejected the old ExactRaw comparison. `V1-RESULT.md` records the exact failure. V2 `20261112-003202-ivxcia` / submitted tree `bed0b22a07c8` PASS: 32 tests, 173 assertions; whole-tree typecheck (including this harness), narrow core lint, and both commit messages passed. Runtime pin verified; one attempt, zero starts charged, cleanup complete. See `V2-RESULT.md`. Native pairing remains unapproved.

## Proposed pair (approval still required)

`pair.jobs.json`: one strict-once attempt per arm, native Bun 1.4.3 executable pin, output/result/runtime worker capabilities, no timing claim and no CPU-model assertion. Same submitted source/data; only GDP_COUNT_DEFER_CHECKS and GDP_COUNT_C2_REPLAY differ (both 0 in control, both 1 in treatment). `run-pair.sh` clears inherited GDP switches and sets the exact base flags explicitly. C2 lemmas and frame-pool changes remain OFF to preserve the historical family.

Input: `runs/lane-f-g1-replay-lease-input/family.json`, supplied read-only as `--data ...:g1-input`, copied from original host-factor-01 output. Trimmed JSON SHA256 must equal `95321d6ef8303cdef66dbb376e1ba9639cbf9c8b2f7768324570ab2133968a8e`.

The builder rebinds the frozen family to a fresh original generator admission and calls `proveLiftedCountComposition` with an explicit `liftedWorkLeaseBudget`. The 3,000,000,000 raw grant is a **diagnostic-only fixed test grant**, divided through the unchanged exact W/30 and W/120 API. All emitted case/leaf identities and root restoration are recorded. The builder must return a checked whole composition and the same family hash.

A fresh process then uses the unchanged native checker for all 19 laws/38 packets, the joint checkCountedLaws entry, and four negative mutations (empty tree, missing witnesses, missing cuts, witness freshness). This independent validation gets its own explicit diagnostic grant; it is **not** represented as same-instance body work or added to a production allowance. Nothing here estimates/calibrates rho, H, b0, or b_min, changes the common 600-second bar, or exercises A's still-pending owner-plan controller.
