# Lane B running checkpoint (not a merge gate)

Code checkpoints: `33df6258` (active slice and initial observer), `60b8c37a`
(bounded count-law completion), `bd82e993` (Lane E `f6ec83db` inclusion selector).

## Validated work

- `lane-b-prepare-v1/check.log`: typecheck/lint; **15 tests, 263 assertions**.
- `lane-b-prepare-v2/check.log`: typecheck/lint; **18 tests, 275 assertions**, including
  complete-tuple provenance, deduplication, fuel/cap bounds and a kernel-checked instance.
- These validate their captured snapshots, not the later complete-coverage trace revision.
- Prepared Gp1 contains **35 laws**: the current 34 generated candidates plus the explicitly
  supplied p1. No finite-Houdini filtering has been applied. It is conditional, not E-14 output.
- Gp1 JSON SHA-256: `2e9905210ba46fceda95499e549075c76ef3cb8ae545e4cca90d02e950de50c8`.
- Shared archive SHA-256: `9d4ca07dd8614b40bd1ad794d3349dfb2b7c7a03745025824cb8c4586eb042f2`.

## First share pair: useful warning for Lane A, not a completed comparison

Both strict 60-second original-harness runs returned unknown. Recomputing shares did
not reach Inv1758 or safety before the wall in this pair. Some inner searches exceeded
their requested share; 15.4 is intended to address this. This is not a production change
in Lane B: its share patch remains under `research/track-m/` for Lane A.

| Attempt | Fixed share / used units | Per-attempt share / used units |
|---|---:|---:|
| no quorum canVote/3, pass 1 | 1,765 / 615 | 3,743 / 615 |
| stored guard reconfigs/inS, pass 1 | 1,765 / 1,943 | 4,083 / 12,942 |
| stored guard reconfigs/inS or disabled/0, pass 1 | 1,765 / 6,107 | 2,965 / 8,265 |

The numbers are the existing trace's requested `ms` and counted `took`, not a new
allowance. The remaining two pairs are pending. No timing improvement is claimed.

## Fast loop and pending jobs

The recovered production captures contained 457 JSON files, 271 distinct unproved roots.
Their kernel name is just `counted`, so law-name filtering was invalid and was removed.
The 96 slowest observed roots (by capture wall, deduplicated across arms) produce **288**
independent default/core/no-units replays in treadmill backlog `track-m-lane-b-roots-v1`.
No opaque-column captures were admitted. These are standalone root experiments, not
whole-law proofs or claims about a particular helper without provenance.

- `lane-b-completion-v1`: all five Gp1 targets before/after 15.2, Lane E held fixed,
  2,700 units and 4.8 s; pending.
- `lane-b-op-v1`: four stored production packets before/after active slicing, 5,000 units
  and 4.8 s; pending. Its earlier observer covers only scalar attempts; do not use it for
  a complete demand-saving total.
- `lane-b-leaf-v1`: research-only 15.4 policy versus current production leaf scheduling,
  same four packets and ceilings; pending. This snapshot includes expanded trace coverage
  (column domains, domains, aliases, field count witnesses and closure count witnesses),
  scope-matched demand attribution, and exception-safe exclusive costs.

Future op receipts also retain the branch tree, its exact nonempty path, conditional-cut contexts and column registry. `audit-lane-b-op.ts` replays those proofs and checks exclusive-cost/demand accounting without search; `audit-lane-b-cost.ts` independently checks retained per-law certificates. These additions cannot retroactively make older receipts portable.

The 15.4 policy is applied only to disposable replay sources. Production has not taken
this policy, 15.5, 15.6 or a kernel change. All current experiments use class submission,
VM-count overrides are absent, and the two completed preparation batches charged **zero
starts** to this client. The 288 variants go through `supercomputer queue add`.

## Failures retained

The first check caught an unknown-typed count entry; the first conditional workers caught
an incorrect generated helper name. Both were repaired. Remaining invalid workers and
an unplaced superseded check were intentionally cancelled by exact owned PID. A subsequent
preparer used filesystem-absolute data paths, but `--data` places files relative to the
repository tree; that failure and the passing sibling check are retained. Corrected input
preparation succeeded. None of these failures is counted as a prover outcome.

**No complete-law proof, 29/29 result, 28/29 recertification, or GATE GREEN is claimed.**
