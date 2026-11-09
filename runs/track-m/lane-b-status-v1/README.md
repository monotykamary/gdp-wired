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

## Recovery and integrated generator checkpoint

At 2026-11-09 12:45 +0700 the scheduler reported recovery ready, no missing batches and no recovery errors. The four clients were still live, with 5/8/11/9 jobs left and none running; no duplicate reruns were submitted. Infrastructure failures from the coordinator's 12:28–12:40 stall are not proof outcomes and will be rerun if any are reported.

Lane A's E-14/15.1 commit is integrated as `05338fee`; Lane E's raw inclusion pool is `3837bb36`. Earlier queued jobs keep their original snapshots. New `lane-b-generated-v1` captures actual generator output with `--generated-only` (no supplied p1) and validates the integrated tree. This is pending, not accepted evidence. The earlier share patch is now present through Lane A's integration, but the disposable 15.4 policy is still not a production change.

## Completed first wave (source snapshots above, not the real E-14 proof repeat)

All 28 jobs in share/op/conditional-completion/generated batches exited successfully after recovery; none is an infrastructure rerun. These batches charged zero VM starts. The share runs remain six **unknown** original-harness outcomes; all generated the old 34-law family, never reaching the row-agreement helper or safety attempt before the wall. Fixed-share total units were 37,099 / 37,190 / 37,039; recomputed-share units were 44,634 / 42,414 / 44,640. All strict exits were zero and in-harness walls were 59.075–59.384 seconds. Larger early draws and local overshoot consumed the pool sooner; no improvement is established. Arms ran exclusively with eight vCPUs but across differing CPU models, not same-VM pairs.

### Conditional Gp1: 15.2 before/after, 2,700 units and 4.8 s

| Target | Before units | After units | Checked before / after |
|---|---:|---:|---|
| Inv2973-half | 2,702.252 | 2,715.752 | no / no |
| Inv1758 | 2,700.415 | 2,700.415 | no / no |
| Inv* | 684.658 | 2,701.611 | no / no |
| Safety | 2,705.369 | 2,705.369 | no / no |
| Supplied p1 | 319.111 | 2,078.848 | no / **yes, worker check** |

The after arm completed 21 count-law tuples for p1 and 36 each for Inv* and Inv2973-half; safety and Inv1758 did not reach completion. The p1 certificate proves both start and step relative to the supplied 35-law family, **not** the whole family. Independent certificate replay is queued in `lane-b-audit-v1`. Reported unit overshoot is retained, not clipped. SAT exits are not claimed to be concrete protocol counterexamples.

### Captured op packets: active-slice before/after

| Law/op | Before units | After units | Before wall ms | After wall ms |
|---|---:|---:|---:|---:|
| Inv2973 / 0 | 1,114.885 | 501.047 | 5,527.746 | 4,851.941 |
| Inv2973 / 4 | 1,439.166 | 616.684 | 5,940.826 | 5,200.697 |
| Inv* / 3 | 1,200.844 | 1,535.985 | 5,245.230 | 5,056.335 |
| Inv* / 5 | 2,583.446 | 1,771.788 | 4,973.295 | 4,980.697 |

All eight remained unknown with 5,000-unit allowances and a 4.8-second cooperative clock. Active slicing reduces three observed prefixes but not Inv* op 3; that arm reached additional frame work. This is not the full 15.4 experiment. Every recorded field-demand status was unknown (40 scalar attempts total), so **no demand-driven saving is measurable** from this snapshot. Helper-query models exist, but are not an active root-leaf demand model. Complete-coverage/scope-aware instrumentation is in the still-pending 15.4 batch. Independent span-ledger audit is queued.

### Actual E-14 output and continuation

The real generator emitted **35 laws**, including the p1 cube, with `suppliedLaws: []` and no missing target. Family SHA-256: `5c9aa44bca08790afdf331b290f101b6ca5d177133e662f5f6f1e80aa6cebc6f`. Generation took 27.306 s. This is different input from the earlier supplied-p1 family, despite the same law count. Typecheck/lint and **66 tests / 5,417 assertions** passed on the captured integrated tree `4d442ca21342`.

`lane-b-real-v1` now repeats all five targets with/without completion against that actual family and runs one strict original-harness capture. The 15.4 leaf batch and 288-root treadmill backlog remain pending. Its first check worker failed lint on the attached generated `packets/runtime.js` (39 bundled-code diagnostics), not on the edited source. A separate no-data `lane-b-leaf-recheck-v1` runs the same leaf-policy transform and source/test checks without linting a generated packet runtime. This is a validation-fixture defect, not a scheduler-stall or proof result; valid measurement workers are not being repeated. Machine-readable observations and CPU/VM provenance are in [measurements.json](measurements.json); compressed, checksum-verified source receipts are retained in each batch's `receipts/` directory. No earlier validation is silently applied to later edits.

## Section 16.5 continuation

The target is now **≤6,000 units and ≤7 s total helper wall on actual E-14 output, followed by original-harness ×3 confirmation**. Old 2,700-unit controls retain their original meaning. `lane-b-section16-v1` calibrates the five real-family targets at the new research line and records search, check/finalization and total wall, plus F2/F3 cache counters. Its larger standalone limits do not alter production.

`lane-b-derive-v1` is the disposable 15.5 comparison with 15.4 held fixed: up to 24 class-fact attempts at each leaf, numeric query, existing model-selected batch, natural cases only on fallback; zero-claims last. Frames are selected by path-simplified count bodies, not protocol names. All facts and the final result are still checked. This prototype retains context-validated model reuse rather than sharing bare SAT exclusions across stronger scopes. The new class-order/frame-selector tests and proof-transport tests are pending. 15.6 follows the class-pass evidence; F1–F3 are explicitly back on the measurement list.

**No accepted complete family, 29/29 result, 28/29 recertification, or GATE GREEN is claimed.**
