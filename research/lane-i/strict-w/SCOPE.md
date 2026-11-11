# Scope of the reader-table repair

## Reproduced path

Both committed51ee and d4 produce unrounded225000050.62510002 at W225M,
with identical26-column raw vectors. The first crossing is tableCells in
Reader.dec's canon/canonFlip, reached through CDCL/model-sequence from the
ordinary count attempt. The protected reader's next value checkpoint notices
expiry only after the whole canonicalization charge. No new protected edit.

## Policy and accounting

- core/meter.ts still increments the same table count after each executed
  observation; no clipping, refund, reset, counter column or price change.
- Its three table observation entrypoints consult a dependency-free optional
  hook. The hook is absent by default; flags-off and unscoped calls retain the
  old behavior. Raw storage itself has no budget or clock state.
- Only count-premise-search's probe callbacks enter withTableAdmission. This
  is synchronous untrusted search policy, not a checker or a proof authority.
- Admit at most256 weighted units per ordinary block. Oversized atomic table
  charges are admitted at their actual size. Near an endpoint, admit only the
  next charge, rather than rejecting an otherwise affordable partial block.
- Reuse permission only while the active absolute endpoint, every other raw
  column and the expected table count remain unchanged. Any interleaving
  invalidates permission before the next table observation. Admission by any
  other runtime primitive invalidates it too, including a caught refusal.
- Nested entry and both normal/exceptional exit discard cached permission and
  restore the prior hook and runtime admission function. No allowance is minted.

For fixed prices: after admission S + b*w <= B. While the snapshot is valid,
only admitted table visits spend that block, and a next visit k <= remaining
credit cannot spend more than b*w. Snapshot/endpoint changes force readmission
against the current real endpoint. Unused permission is never charged.

No universal claim about new price vectors, arbitrary workload endpoints or
floating-point arithmetic follows. The required evidence is the actual strict
225M comparison on the pinned profiles, plus successful raw-identity and
interleaving controls. A future price vector requires fresh bound checks.

## Existing evidence and pending gates

Pilot core runtime d903ae40:224999999.62510002; exactly51 fewer tableCells,
allother25 raw buckets equal to the original failing run. Positive reader
results and all26 ample-budget raw deltas are covered by controls. Legacy,
full scope controls and19-law/38-goal native replay passed on032d92c2; the
latter includes four mutation refusals but is NOT Lean or family promotion.

The preliminary functional loop and final isolated --timing loop kept1M
table units and allother raw buckets identical, with3970 admissions versus
1000000 for per-node admission. The active clock tripwire did not fire. See
RESULT.md and results/benchmark/placement.json for the isolated measurements.
No numeric clock-read field was emitted; do not invent one.

Uninstrumented9/F12/F13 endpoints passed on71832531. Final340557e5 repeats
F12, stronger all25-interleaving controls, type/lint and commitlint. The only
production-file change from71832531 is a comment clarification in meter.ts;
no executable difference. Strict28 audited28/28 exact normalized pairs
(27proven,1unknown), not a28-model full-work W claim.
A's15-flag scheduler diagnostic is separate, owned by A, and excludes this fix.
