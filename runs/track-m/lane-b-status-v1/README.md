# Lane B running checkpoint (not a merge gate)

**Authoritative merge evidence:** only Lane D's one-command final gate with the exact roster, pair identity, both SHAs bound and CPU labels. Any future `GATE GREEN` statement must cite that receipt. These lane-local experiments, checks and analyzers are iteration evidence only.

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

## Full 15.4 leaf-policy result (older op packets, not an E-14 pass)

All eight workers returned unknown. The baseline here already includes the initial active slice; this comparison adds the full disposable 15.4 policy. Exact source tree: `899fd3a9bcc8`. All eight archives were fetched and checksum-verified.

| Law/op | Before units | Full 15.4 units | Before wall ms | Full 15.4 wall ms |
|---|---:|---:|---:|---:|
| Inv2973 / 0 | 499.880 | 1,409.303 | 4,918.585 | 4,690.981 |
| Inv2973 / 4 | 612.965 | 2,329.604 | 5,106.173 | 5,190.996 |
| Inv* / 3 | 1,070.194 | 1,774.017 | 5,170.150 | 4,831.060 |
| Inv* / 5 | 1,873.990 | 876.490 | 4,879.970 | 4,882.502 |

These are 5,000-unit, 4.8-second clock-limited prefixes on exclusive eight-vCPU VMs. CPU models differ in two comparisons; there are no same-VM pairs. Cooperative wall overshoot is retained. The table does **not** establish a per-helper 6,000-unit/7-second pass.

The full policy did not reach field helper work on Inv2973 ops 0/4 or Inv* op 5. Their emitted guard-budget traces stop in inactive leaves; field units are zero, while frame work remains 227.133 / 313.756 / 151.865 units respectively. Therefore zero field units are not a successful cheap derivation. Inv* op 3 reaches two active attempts and two closure leaves (draws 13.816 and 7.470 units), but still does not close. Every available demand value remains unknown. No measurable demand-saving credit is assigned.

The check worker failed on the attached bundled `packets/runtime.js`; its 39 lint diagnostics are retained byte-for-byte in `lane-b-leaf-v1/check.log.gz` (compressed to preserve the raw linter formatting). The no-packet-data recheck remains pending. No measurement was repeated because of that fixture failure.

To test 15.5 itself rather than inactive-guard budget starvation, `lane-b-seeded-leaf-v1` directly replays the recorded Section 14 op-0/op-4 scopes with and without class-first ordering. It validates packet/root lineage and every imported seed before use. These are **legacy-fixture conditional leaf diagnostics**, not actual-family or whole-op proof claims. The actual-family 16.5 calibration and derive-first comparisons remain separately queued.

## Actual-family calibration and independent audits

The first-wave audit replayed the supplied-family p1 certificate and reconciled eight op ledgers (`lane-b-audit-v1`). The actual-generator audit then replayed **p1 at 2,459.750 recorded units / 2,165.207 ms** and reconciled all eight full-leaf-policy ledgers (`lane-b-audit-v2`). These are conditional per-law results, not acceptance of all 35 laws together.

The unmodified-policy 16.5 fast-loop calibration (`00d1e747bee8`) returned:

| Target | Recorded search units | Total wall ms, including final check | Worker checked |
|---|---:|---:|---|
| Inv2973-half | 5,159.553 | 7,007.253 | no |
| Inv1758 / row agreement | 5,972.174 | 7,000.962 | no |
| Inv* | 4,505.988 | 7,009.147 | no |
| Safety | 4,311.113 | 4,042.219 | yes |
| p1 | 2,459.750 | 4,723.752 | yes |

**Measurement-version caveat:** v2 recorded counted units before the final check, although its total wall includes that check. These historical numbers are therefore explicitly search units, not a fully accounted helper-unit pass. Future v3 records separate search/check units and their total; the independent auditor also reports replay-check work. Neither a fast-loop success nor its boolean `withinDiagnosticLine` is the required original-harness ×3 evidence. The calibration's independent certificate audit now confirms both p1 and safety (`lane-b-calibration-audit-v1/certificates.log`); the other three remain unresolved. Both obligations were checked for each positive certificate. This upgrades certificate validity, not the search-only unit accounting or whole-family acceptance.

With full 15.4 enabled in both 15.5 arms (`9f3d96925fd7`), p1 was checked in both at the same 2,459.750 search units; all other targets stayed unresolved. Safety no longer closed in these arms. This is not an improvement and does not isolate an effect of class ordering. **Coverage correction:** `countsDump` projects phase events, not the helper's local `stage` events; absence of `derive-class-attempt` in this projection cannot establish zero class attempts.

The standalone profiler (`1c10c1400c3a`) recorded final `checkMC` time of 228.195 ms for p1 and 840.068 ms for safety, with two calls each. Its conditional-check counters remained zero. The original-harness profile ended unknown at 59,004 ms and recorded no instrumented checker calls; without a validated coverage check this is not a saving estimate. Its archive fetch failed; the job stdout and placement are retained, but that archive is **not checksum-verified locally**.

Validation exposed and corrected three research-only issues: unused `events`, an implicit seed-array type, and a profiler throw in `finally` that could mask a checker exception. Corrected validation is being rerun, not counted as passed. The first direct-seed run hit its 20-second outer watchdog before producing a search record; a phase-logged retry isolated repeated full-root seed expansion as the blocker (seed 204/206). The next retry retains each checked original slice under byte-identical root lineage instead of expanding it, and keeps the helper's 6,000-unit/7-second allowance unchanged. These remain legacy diagnostics, never E-14 pass evidence.

## Complete-cost repeat, validation, and ownership update

`lane-b-final-cost-v1` (tree `060ae1061036`, EPYC 4585PX, eight pinned vCPUs per exclusive VM) now records the whole helper wall and reads the work meter after final checking:

| Target | Search units | Additional counted check units | Total wall ms | Final-check wall ms | Worker checked |
|---|---:|---:|---:|---:|---|
| p1 | 2,459.750 | 0 | 4,251.850 | 447.123 | yes |
| Safety | 4,311.113 | 0 | 3,402.988 | 728.053 | yes |

The zero is **a property of the current work meter**, not free checking: its wall cost is explicit. Archives are locally checksum-verified; checker-only replay of these exact new receipts passed for both targets (`lane-b-final-cost-audit-v1/certificates.log`, audit tree `677692b7a171`, exclusive Ryzen 9 9950X VM with four pinned vCPUs). Replay also records zero added counted units; final-check wall remains nonzero as shown. Both meet the standalone numerical line. Neither supplies original-harness ×3 evidence or accepts the other generated helpers.

The legacy direct-leaf run (`lane-b-seeded-leaf-v3`) produced no proof: op 0 baseline unknown at 992.332 units / 7,212.619 ms; op 4 baseline unknown at 996.961 / 7,001.256 ms; op 4 class-first unknown at 1,246.483 / 7,131.750 ms, with **52 recorded class attempts** across its scopes. Op 0 class-first raised `WallExpired` during frame classification before emitting a final search record. The supplied 31-seed array was reused by the search in this version: its later `seedCount` includes derived additions and is not an imported-seed count. Future runs copy it first. Setup took another 4–6.6 seconds outside the recorded helper clock. No real-family inference is made from these legacy fixtures.

Follow-up class work caches each canonical count body once within a **snapshotted branch ranking pass**, never across changed branch assumptions; the attempt cap and proof checks remain. Its two changed diagnostics are queued, with `WallExpired` retained as an explicit unresolved outcome.

Validation tree `d2745c25feee`: default typecheck/lint and **31 tests / 310 assertions**, then **5 tests / 19 assertions**, passed. The full leaf+class variant passed typecheck/lint and **52 tests / 541 assertions**. These counts are per configuration, not disjoint tests. The profile validation passed typecheck/lint but timed out after an incorrectly ordered Bun command launched the package test script rather than the intended filtered tests. Only that invocation is being retried with `bun test --preload ...`.

**Ownership:** the coordinator moved 15.6 to Lane F on `claude/mldr-leaves`. Prototype handoff: commit `b6fa0a50`, `research/track-m/LANE-F-HANDOFF.md`. One row-policy check was already in flight; no row measurement batch was submitted. Lane B removed row-policy hooks from its runners and keeps 15.4, 15.5 and 16.5. No further 15.6 development is planned here. F snapshot `6cb29e80` and its shared A/E prerequisites were imported in `c0a7f780`; fresh integrated validation and balanced same-VM Lane B policy pairs are pending. The corrected prior profile check passed 27 tests / 257 assertions with typecheck/lint, on its own pre-integration source snapshot.

## Integrated same-VM comparison: combined policy rejected

All ten jobs of `lane-b-integrated-pairs-v1` exited normally (source tree `e32037653323`), with each before/after pair on the same exclusive eight-vCPU VM and both execution orders represented. The combined full 15.4 + 15.5 policy loses safety in both orders:

| Order | Base safety units / wall ms | Combined units / wall ms | Worker outcome |
|---|---:|---:|---|
| base → combined | 4,488.589 / 3,237.475 | 6,000.500 / 4,203.236 | checked → unknown |
| combined → base | 4,488.589 / 3,445.907 | 6,000.500 / 4,729.846 | checked → unknown |

p1 remains checked in all four arms at 2,292.235 units. Inv2973-half, Inv1758 and Inv* remain unresolved. Local checker calls are not being promoted into joint-family acceptance; archive verification and independent paired-certificate replay are pending. This result rejects recommending the combined policy as a default.

The falsifiable next hypothesis is that 15.4's broader reconstruction allocation, not class ordering itself, causes the safety loss. `lane-b-safety-ablation-v1` runs base, leaf-only and class-only in opposite orders under the unchanged 6,000-unit/7-second search line. It is pending.

Integrated validation failed on type errors, not tests: an optional callback closure in `row-cases.ts`, the Lane F summary's optional array destructuring, and the new seeded auditor's inferred local type. Lane F had already published repairs; they were imported with snapshot `0b85516e` in `c6336bf8`. Only validation is being retried (`lane-b-integrated-validation-v2`); completed measurements are not rerun for these type-only fixes.

**No accepted complete family, 29/29 result, 28/29 recertification, or GATE GREEN is claimed.**
