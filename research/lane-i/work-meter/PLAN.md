# Lane I — Section 18 complete-work implementation plan

Status: isolated raw-meter V2 `9f89363c` passes the selected kernel/refusal
matrix and its independent receipt audit. The current three-file patch is
`kernel-meter-v2.patch`, with exact identities in `source-v2.json`.
Rational row construction and standalone-checker coefficient visits are
included. Lane D's independent 28-certificate audit and operation-coverage
review remain mandatory before use. No kernel increments, new weights or W
are active in the integration branch, and I2/I3 are not implemented.
Generator intake continues independently; its isolated candidate is
`279c45b3` on `b11e1f65`. Section 18 was read in full on 2026-11-10;
its order explicitly permits I1–I3 alongside A1–A2.

## Isolation and handoff

- Prepare I1 on a separate qualification ref. Do not alter the active production
  branch while the existing generator preflight/pilot is running.
- First change: `kernel/meter.ts` containing raw integer fields `tableCells` and
  `checkSteps`, plus increments in `kernel/kernel.ts` and `core/check.ts`.
- The raw meter is not a budget and cannot change a checker decision. Nothing in
  either trusted checker may read it except the implicit read of `+=`.
- Send that increments-only change and receipts to Lane D before wiring it into
  `fullWork`. No provisional weights are treated as calibrated, and no change to
  what is accepted is permitted. Lean does not need an instrumentation twin.

## I1 insertion inventory and acceptance checks

- `kernel/kernel.ts`: `linearOf`/linear construction, `termRows`, `leafRows`,
  the cell-pair loop, `withProducts`; `check`, the `checkGoalLemmas` visitor,
  quantified/count-tree visitors and final machine-law checking paths.
- `core/check.ts`: every `checkRefutation` proof step and actual row-coefficient
  processing. Count failed/partial work too; counting only successful output
  rows would leave cancelled or rejected work understated.
- Avoid charging the same materialization at both a wrapper and its callee.
  Cache hits must be distinguished from fresh construction. Record the exact
  operation definition at every insertion; do not use a phase-name weight.
- Audit AST references: the meter object is imported normally, and each checker
  reference is solely the left-hand side of an additive assignment. Strip
  inserted instrumentation and verify the original checker AST is unchanged
  (including return expressions, branches, bounds and exception handling).
- Exercise valid certificates and refusals while meter values are left alone,
  zeroed, doubled and deterministically perturbed during checking. The exact
  acceptance bit vector must match. Lane D owns the 28-certificate audit.
- Run relevant kernel/refusal tests, full roster and type/lint remotely. Archive
  failed checks as evidence; do not fix a refusal by weakening a checker.

## I2–I5 after the raw-meter audit

- Add raw `astNodes`, `evals`, `cubeTests`, `ticks`; integrate existing CDCL/EPR
  counts and infer's private meter into the shared accounting model.
- The final checker work belongs to W. A proof over W after final checking is a
  deterministic budget failure, not an accepted proof with uncharged cleanup.
- Add an inert phase ledger and F3 silent-work detection. Test mldr, Lane B's
  seven-case strategy and Lane E's Inv1758; do not claim either P* helper proves
  the original model. Their earlier conditional artifacts remain quarantined.
- Keep all twelve old weights fixed. Lane D owns new-term fitting, k=3 testing,
  the reference host, W and their frozen hashes. No weight/W is chosen to hide
  a lost proof or to force 29/29.
- F4/F5 census: all 29, three repeats, at least three CPU models, one protocol
  per fresh process, two protocol orders, empty behavior-knob environment and
  trace-on/off variants. Demand exact verdict and unit equality, not averages.
- Retain the current qualified-host wall gates until D2 publishes W. A killed
  process is an infrastructure failure, never a fabricated `unknown` row.

All builds, tests, receipt processing and census work run on boat. At most one
subagent; none used so far. Reuse source archives; no new local whole-tree copy.
