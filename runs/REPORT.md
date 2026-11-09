# RESUME — ACTIVE (user explicitly resumed)

Lane I resumed from `cca59f0c` on `claude/mldr-integ`; clean worktree verified, handoff including PAUSED, COMMON, and Section 14 read. **NOT GATE GREEN.** Baseline stays `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`.

- First cancelled work rerun: all **140 upper-bound shards** submitted through the scheduler, fresh output `runs/lane-i/upper-bound/resumed/full`, task `cf1d3fc9-6a88-4e12-8403-974717b1ed42`. Every guest unpacks frozen production `15eff72f` and checks the retained source manifest; the current integration is not substituted. No supplied laws; original 34-law family; 30 minutes per operation; no share; independent verification still required. Pending, not a result.
- Repair: core-replay reconstruction now spreads the previous obligation before replacing its goal/decls/encoded goal, retaining `all`, certificate and pool. Added a focused range-demand test for a read omitted by the selected certificate. No budget, law, or kernel change.
- Current source/test candidate: `edd284913024a6566591d7ad1cba8059b8047a14`; all eight v9 validation jobs and all 87 generation pairs were launched with new pinned inputs. Later B/report/audit changes do not alter the tested engine. Results are still pending. Lane D's final gate is mandatory; the earlier `704efc27` request is superseded below.

## Admission recovered; one-subagent cap remains

Coordinator reports the shared blob-cache lock freed at 00:35 and normal wide boat submissions are open again. Verified **all four original Lane I batch IDs are now persisted in the scheduler queue**: `20261110-001227-5qxos1` (140 shards), `20261110-001619-awzeif` (validation), `20261110-001623-9q08uz` (generation census), `20261110-001947-ek072a` (receipt audits). Their existing controllers remain owners. Nothing was killed or resubmitted, and no duplicate run was created.

Integrated A `19ad4ab4`: the atom-readiness shortcut and two finite-domain equivalence tests remain confined to the experimental tiny backend; original generation still does not invoke it. New witness-replay diagnostics distinguish newly found from historical drops. Only the report conflicted; Lane I keeps pointers to A's report. V9 remains bound to its older source SHA; new mechanics are required for this source update.

## Coordinator memory-pressure guidance (historical; submission hold lifted, memory cap retained)

The coordinator confirmed that laptop memory pressure (7.5/8 GB swap and heavy paging) is stalling shared blob-cache admission while a client's per-file `utime` crawls. This supersedes the unconfirmed contention hypothesis below; it is not a proof-engine failure. All four existing Lane I controllers remain untouched: no resubmission, no cancellation, no scheduler/cache changes.

Until the coordinator lifts this instruction: at most one subagent, close idle/finished subagents, and no new parallel local work. Lane I has started no subagents and has none to close. Continue only lightweight sequential file review/edits and observation of the already-submitted jobs. Their receipts remain pending.

## Resumed integration ledger

All current committed heads integrated: A `bef4020f`, B `30537f70`, E `b3f8377e`, F `27ca886f`, Fable `a6ae4be9`. Lane-local evidence stays at each branch's `runs/REPORT.md`.

- A's optional finite-value domains, bounded compiled clauses, and round limits remain confined to the experimental tiny backend; production still uses the original finite path. Its source merge was clean.
- B/E/F have no new core/kernel/script deltas beyond already-integrated work. Their checkpoint/research receipts were retained.
- Fable's `a19a0713` import repair agrees with the integration's existing canonical `kernel/model-sequence.ts` import. Retained the unused-import repair and new narrowed-range test. Its only source conflict was a blank line between the existing recursive `lawReads` helper and A's tiny wrapper; preserved both implementations and the blank line. No side's behavior was dropped.
- All `runs/REPORT.md` conflicts keep this Lane I report with the branch pointers above; their text is not copied here.
- `e594a8f8` preserves core-replay `all`, certificates and pool metadata. The new v9 run, not old v7/v8 receipts, will validate the combined tree.

### Resumed validation submission and convergent B range merge

V9 is submitted on **`edd284913024a6566591d7ad1cba8059b8047a14`** versus baseline **`b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`**. Eight validation jobs: task `35d1dcd8-5feb-4788-b662-795cd19d2016`, output `runs/lane-i/v9/validation`. All 87 generation pairs: task `0f17f2ed-023e-46db-aaa5-01bde628c16d`, output `runs/lane-i/v9/census`. Both use fresh `runs/lane-i/v9/input` identities and retained baseline/vendor archives. All remain pending until audited.

B then advanced to `b056c3b4`. Reviewed every production hunk: its demand-driven range function, three full-read return sites, both model-loop rebuild triggers, and replay read preservation are already present here. Conflicts resolved to the existing equivalent implementation, retaining E's member premise/independence checks, I's replay spread, and I's additional narrowed-read regression. B's repeated range-demand assertions already exist here; no assertion was dropped. New B research comparison scripts are retained. This merge changes no core/kernel/test bytes relative to v9's candidate.

### For lane B

Your `b056c3b4` range port converges with v9's `edd28491`. I kept the integration's equivalent implementation plus E's member handling and the replay spread repair `e594a8f8`. Fresh combined v9 runs are in progress; no old gate result has been transferred.

### For lane D — superseding the historical candidate request

The current production/test candidate is **`edd284913024a6566591d7ad1cba8059b8047a14`** against **`b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`**. Please bind a fresh exact-roster, both-SHA-bound, CPU-labelled final gate to these SHAs when your cancelled first gate completes. It includes the core-replay metadata repair and all checkpoint lane tips. The later B merge is production/test-byte-identical. V9 local iteration checks are submitted, not yet green; only your complete receipt can authorize a gate claim.

### Receipt audit and admission observation

Added `research/lane-i/validation-audit.ts` and regressions: process exit zero without exactly one semantic result is not a pass; duplicate/malformed phases fail; original-harness unknown stays unknown; test-load errors cannot be called clean; measured pre-attempt wall is reconstructed from timestamps, never from the counted `candidates at` clock. Upper aggregation now refuses duplicate terminal records, unknown status labels and a `closed` label without both worker and independent checks.

Boat audit/check batch task `479c40a4-0c9e-4cea-af27-6dc356346d61` uses `research/lane-i/resume-audit.jobs.json`, output `runs/lane-i/resume-audit/results`. It also semantically audits the retained v8 logs, expecting the recorded failed check; a missing audit artifact cannot satisfy that expectation. New auditor tests/check are pending, not reported as passed.

Admission observation at 2026-11-09 17:22 UTC: all four owned controllers remain alive, but their output directories are empty and no corresponding persisted scheduler queue JSON exists yet. They have descriptors open on the shared `scheduler/blob-cache.lock`; scheduler PID `44811` also has three descriptors there. This is evidence of a shared admission stall, not evidence that the 140 searches or validation jobs ran. No other client's process, scheduler, cache, VM or lock was stopped, removed or changed. Keep the existing owners; do not duplicate-submit or silently transfer a result. The hypothesis is cache-lock contention before admission, not a measured code failure.

## Archived paused checkpoint (superseded by the explicit resume above)

**Branch:** `claude/mldr-integ`. **Last source/test SHA:** `a3930f448d4a7e447cb4d9470a4ec34a5d09e5b3`. **WIP/evidence checkpoint SHA:** `b5ed324525e8e88ad7386fa746f1ed41dad95536` (this RESUME is the subsequent documentation-only commit; obtain its final SHA with `git rev-parse HEAD`). Baseline remains `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`. No push. The pending merge of Fable `f8206bfc` was **aborted**, not completed. No merge is in progress.

## Proven/measured so far

- **NOT GATE GREEN.** No full MLDR proof and no Lane D final receipt. V7 is the last fully audited integration cycle: clean type/lint check; **621 tests / 19,688 assertions**; all **87 generation pairs** successful, with **84 non-MLDR pairs byte-identical**. Three strict MLDR runs are **unknown**, at **59.012 / 59.018 / 59.147 s**. These are generation comparisons, not a replacement for the full proof-verdict roster.
- V8's four changed-test shards completed with exit 0 before cancellation. The actual `core/count-ranges.test.ts` loaded and all four tests passed. All three new test-load propagation tests passed: a real missing-export error cannot be masked by a passing file, and the quick-suite driver propagates failure and stops. Their receipts are committed under `runs/lane-i/v8/validation/`.
- V8's check **failed**: `core/counts.ts(931,11) TS2322`, a rebuilt replay object lacks required `all: MapRead[]`. Three paired strict-MLDR commands produced logs and exit 0, but their verdicts have **not yet been semantically aggregated/audited**; process success is not proof.
- Upper-bound implementation/smoke receipts exist, but the requested **140-shard full census has no usable collected results**. Do not infer a closure or a counted-work bound from a cancelled job without a receipt.

## Cancelled / stopped owned work

All three active tasks were stopped by exact task ID and joined as `killed`. Final task inventory: **zero active owned tasks**. Shared scheduler/other clients were not stopped.

| Task ID | Batch; output directory | Purpose; partial usability / rerun |
|---|---|---|
| `c87cb42c-4236-4aec-af04-02ebf100a772` | `20261109-153811-6qofjx`; `runs/lane-i/upper-bound/full` | 140 original-34 upper-bound shards, frozen production `15eff72f`. Output directory empty. No usable partial result; rerun all 140 after explicit resume and source binding. |
| `381ed372-6c96-4727-9a1b-2a4ac8336fcf` | `20261109-155412-uekwu6`; `runs/lane-i/v8/validation` | Eight validation jobs. All individual logs/summary collected: four test passes, one check failure, three unaudited MLDR command results. Usable only as those individual receipts; rerun full validation after repairing the source. |
| `6a287b13-8a11-4483-87ac-88d5e5279fd8` | `20261109-155416-jnnc4s`; `runs/lane-i/v8/census` | 87 generation comparisons. Output directory empty; no usable partial results; rerun all 87. |
| `2092fac9-ec85-42a5-8f13-ffc3567c8625` | no boat batch | Lane-tip watcher already exited 0 before checkpoint. No active watcher remains. |

Cancellation metadata: `runs/lane-i/checkpoint/cancelled-tasks.json`. Small collected receipts are committed; large outputs, archives and tar snapshots stay out of git and remain local. Their paths/sizes are in `runs/lane-i/checkpoint/local-artifacts.txt`; preserve the workspace's `runs/lane-i/` (about 549 MiB before checkpoint). More detail: `runs/lane-i/checkpoint/README.md`.

## Open audit blockers and exact next steps — only after explicit resume

1. Read this RESUME and checkpoint README; verify branch/HEAD and a clean worktree. Re-read `supercomputer --skill`. Do not resurrect cancelled tasks or overwrite old output directories.
2. Repair `core/counts.ts` around line 931: preserve the required complete-read list (`all`) when the model-replay branch rebuilds certificate objects. Preserve the E member-witness independence checks, B completion retries, F compensated-frame cap, and Fable demand-driven range rebuilding. Add/check a focused regression; commit normally, never amend or reset history.
3. Reconcile Fable `f8206bfc` / canonical import fix `a19a0713` after resume permission. The integrated import is already correct (`../kernel/model-sequence.ts`, since `704efc27`); do not reintroduce the old import from `kernel/prove.ts`. The quick roster must continue explicitly including range/member tests. Fable's own 29/29 matching verdict report is not proof about the newer combined tree.
4. Create **new** `runs/lane-i/v9/input/` with the retained v8 baseline/vendor tarballs and checksums; repin `identity.json` to the newly committed candidate SHA, unchanged baseline and exact lane heads. Then run:
   - `supercomputer run --jobs research/lane-i/validate.jobs.json --out runs/lane-i/v9/validation --class gate --timing --vm-type large --data runs/lane-i/v9/input:integ-input`
   - `supercomputer run --jobs research/lane-i/census.jobs.json --out runs/lane-i/v9/census --class submission --timing --vm-type large --data runs/lane-i/v9/input:integ-input`
   Keep one owner/waiter per batch. Collect and audit every result, including test-load errors, MLDR verdicts and actual pre-attempt wall; do not accept only process exit status.
5. Resume the upper-bound request through `research/lane-i/upper-bound/README.md`. The retained jobs/input manifest is bound to frozen source `15eff72f`, **not** the current source. Reproduce that source in a disposable tree with retained tooling, or explicitly recapture/rebind the repaired source and label a new experiment. Never relabel old inputs. Submit all 140 helper/op/pass/ceiling-on/off shards in parallel with a fresh output directory. Require the original 34-law family, no supplied laws, independent verification, and conservative unknown/censored reporting.
6. Restart lane monitoring only when resumed. Refresh force-added `runs/REPORT.md` as lanes move. Request Lane D's exact-roster, both-SHA-bound, CPU-labelled final gate on the final candidate; no green claim or merge to main without it.

---

# Lane I — continuous MLDR integration

NOT GATE GREEN. Baseline `main` = `b788e195`; branch `claude/mldr-integ`.

Read COMMON.md, MLDR-DESIGN.md Sections 14–16 (including the answered 16.3 audit), and all MLDR-29.md rules, Speed, Gate evidence and Merging. Only Lane D's SHA-bound final receipt can authorize GATE GREEN. No push or merge into main is authorized here.

## Current status

V7 completed with clean check, 621 tests / 19,688 assertions, and all 87 generation pairs successful (84 non-MLDR pairs byte-identical); strict MLDR remains unknown 3/3. New E declaration-backed member premises and Fable demand-driven ranges are integrated and require v8 validation. Separately, the coordinator's 140-shard upper-bound research census is submitted on frozen production `15eff72f`, original 34-law family, no supplied laws; results are pending and will not be transferred to newer production. No Lane D final green receipt exists. The baseline is unchanged; no history was rewritten.

## Plan and falsifiable hypothesis

Combine every committed lane tip without dropping either side of conflicts. Hypothesis: preserving A's finite-model certification and attempt deadlines, B's completion/leaf budgets, E's lazy inclusions, Fable's generation-wall reductions, and F's demanded row splits produces a type-correct integrated engine without changing the other 28 generation lists. Falsifiers: failed checks/tests, changed unrelated candidate lists, missing helper attempts, uncapped attempts, or same-VM regressions. All substantive runs use `supercomputer`; strict verdicts use `--timing --vm-type large`, one job per repeat. No supplied laws count toward the finish line.

## Input ledger

- A: `claude/mldr-gen` at `00a0cbc1`.
- B: `claude/track-mldr` at `715ffd78` (advanced during initial inspection).
- E: `claude/mldr-incl` at `79d094f5`.
- Fable wall: `claude/mldr-wall` at `800b824f`.
- F: `claude/mldr-leaves` at `78eedf50`.

Lane-local reports remain in each lane's `runs/REPORT.md`; this report keeps pointers, not copies. Source histories and both sides of each conflict are reviewed before resolution. Raw logs and archives stay ignored.

## Execution ledger

- Initial worktree clean at baseline. Scheduler skill read; no local tests or builds.
- A `00a0cbc1`: source merged cleanly. Only `runs/REPORT.md` conflicted (add/add); retained Lane I report with the pointer above. No checked integrated result yet.

- B `715ffd78`: retained A's finite certification and shared `attemptEnd` deadlines, added B's count-law completion import and pre-SAT completion retry (both conflicting hunks were additions on B). Shard roster includes `count-completion.test.ts` and B's field-demand tests. Retained A's newer T16 audit repair evidence and T13 generation/census fixes (existential caller handling, exact 29-roster validation, optional repeat-2 receipt); B carried older copies without those fixes. Lane-local report remains a pointer.

- E `79d094f5`: production inclusion changes merged without a source conflict; B already contains its cherry-picked inclusion/upper-bound implementation. Retained Lane I report, pointing to E's original report and replay evidence.

- Fable wall advanced to `1dd0f1bb` during inspection (includes `800b824f`). Three `core/finite-houdini.ts` conflicts combined explicitly: retain A's 2 s local wall, targeting, cancellation and `onFinish` options; add Fable's recursive count dependencies and unchanged-read skip; sort the full family INCLUDING A's parameter precondition and declared facts; seed boundary/base/random states in round zero and record rejected boundary states for Fable's later-round revival. A's unsupported-sums guard survives. Faster runtime keys, own-property audit fix, lazy step-count calculation and hashed BFS merged cleanly. Report kept as pointer.

- F `78eedf50`: model-demanded rows and write-free activation changes were already inherited through B (`3779c750`, `4cf52e8d`, `1ecbfb15`). The remaining three frozen-probe portability fixes merged cleanly.

- Refreshed B to `5bf5b8da` and E to `70356696` (research/receipt changes; production unchanged). Added `research/lane-i/validate.sh` and exact single-protocol census receipt validation; 109 changed tests in four disjoint groups, one check job, three same-VM strict MLDR pairs, and 87 same-VM generation pairs. No lane-local analyzer is final gate evidence.
- Local submodule setup initially failed because the configured URLs are local paths; reran Git with command-scoped `protocol.file.allow=always`. Both pinned submodules are now present; no global config or other worktree changed.

## Live validation and interactions

Frozen candidate `5440a7b87ead19fcc02b9b8be86df382088d9cdf`, baseline `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`. Commands:

```
supercomputer run --jobs research/lane-i/validate.jobs.json --out runs/lane-i/v1/validation --class gate --timing --vm-type large --data runs/lane-i/v1/input:integ-input
supercomputer run --jobs research/lane-i/census.jobs.json --out runs/lane-i/v1/census --class gate --timing --vm-type large --data runs/lane-i/v1/input:integ-input
```

Both batches are running. Do not read scheduler launch success as validation success. Source archive/submodule hashes are recorded in `runs/lane-i/v1/input/identity.json`. Per-job CPU labels and placement accompany paired traces. A read-only filesystem watcher reports new committed lane tips; it never edits or merges on its own.

### For lane B / F

Your reported safety loss belongs to the disposable full 15.4+15.5 policy ablation, not automatically to current production: neither side of Lane F's ordinary-pipeline calibration lost safety. Lane I retains all production tips for measurement and does not install the rejected disposable policy. Lane F's current direct frontier increases work (about 667 to 885–1,075, no closure); keep that negative evidence visible. The integrated strict harness and census are running, not yet a promotion recommendation.

### For lane A / Fable wall

The integration retains A's parameter/fact checks and 2 s finite cap with Fable's sorted-family/unchanged-read optimization. Targeted boundary states must be recorded as rejected states so they can revive after a premise drops; the resolution does so. The integrated tests include declaration, cancellation, fixpoint, runtime-key ownership, and small-state tests.

## First frozen integration results

`5440a7b8`: all four changed-test groups passed; **check failed** in Lane B's `research/track-m/summarize-lane-b-pairs.ts` because `.sort()` lacked the required comparator. Fixed with explicit ordinal ordering in `0d9e1d3c`; no production change. Scheduler controller returned exit 0 despite the failed check job; the failure is retained and is not called green.

All three original MLDR candidate runs returned unknown under the strict wrapper. Initial trace: 34 generated/retained laws, Inv* and Inv2973-half are tried at about 3,050 units and return unknown; Inv1758 is tried at about 2,997 and remains unknown. Full per-repeat extraction follows when both batches are collected. `counts: candidates at 0 ms` is counted-clock output, **not generation wall**; no wall claim is inferred from that field.

Refreshed A to `26c04703` after the event-driven watcher notified its push: new strict audit/generation evidence only, no production delta. E/F report-only conflicts resolved by keeping this report and pointers. The newer source check remains pending; source-equivalent experiment receipts continue to bind the original `5440a7b8` engine.

## For lane B

The integrated `bun run check` caught `require-array-sort-compare` at `research/track-m/summarize-lane-b-pairs.ts:9`. `0d9e1d3c` supplies an explicit lexical comparator on both arrays without changing the roster assertion. Pull this fix or its equivalent; do not classify the failed check as infrastructure.

## Continued lane refresh

B advanced to `120b0787`: all changes are research/receipts, no core or kernel delta. Its new ablation links identify the safety loss with **reconstruction allocation caps**, not helper-only caps; keep that narrowed candidate research-only as the lane does. One source conflict in `summarize-lane-b-pairs.ts`: accepted B's extended explicit-comparator/optional-job-roster assertion in place of I's equivalent fixed-roster comparator, preserving both the lint repair and B's multi-arm/byte-verification audit. Report conflict resolved with this pointer.

I's first current-check rerun also caught one new research-only type error: optional `placement` access in `research/lane-i/summarize.ts`. Fixed conservatively with optional access (missing placements remain validation issues), committed separately. Both failures and all raw logs are retained. No production code has changed since the frozen `5440a7b8` experiment.

## Runtime audit refresh and census failures

Fable advanced to `671dc506`. The only new production change is the audited Uint32 `$unique` stamp rollover reset: zero the buffer and restart at one before a stale stamp can match. Kept A's independent runtime cancellation hook; source merge clean, report conflict kept as a pointer. Added rollover/growth test retained. This requires a fresh integrated run, not a silent transfer of the old SHA's results.

The first census completed 81/87 pairs successfully. Six generation-only `learning_switch{,_i4}` jobs exhausted the driver's 120 s process limit (one reached the scheduler's 210 s inner limit); neither a complete census nor a byte-identity claim for all 28 is supported. Those generation-only jobs now get the existing lane census allowance of 900 s per side with a 2,100 s job wrapper. **The original proof harness stays at strict 60 s; no proof budget changes.** All first-attempt failed receipts remain in `v1/census/`.

The first four changed-file groups total **584 tests, 19,569 assertions, zero failures** across 109 files. The own-summary type/lint failures were repaired separately; no clean full check is claimed until the new job returns.

## Measured pre-attempt wall (observation-only preload, v2)

Same-VM strict pairs against main, no supplied laws. `research/lane-i/timing.ts` timestamps candidate generation and the first completed attempt; pre-attempt wall subtracts that attempt's measured duration from its return timestamp, using the official result's elapsed time to establish proof start (millisecond rounding applies).

| repeat | CPU | main pre-attempt | integrated pre-attempt | integrated verdict / wall | safety tried |
|---|---|---:|---:|---|---|
| 1 | Ryzen 9 9950X | 24.819 s | 13.426 s | unknown / 59.009 s | no |
| 2 | EPYC 4585PX | 24.893 s | 11.778 s | unknown / 59.247 s | no |
| 3 | Ryzen 9 9950X | 37.985 s | 23.042 s | unknown / 59.020 s | no |

Receipts: `runs/lane-i/v2/validation/{mldr-r1,mldr-r2,mldr-r3}.log` and `placement.json`, candidate `e884f3af`. This confirms generation wall improved on the paired runs but does **not** solve the proof wall. Earlier uninstrumented v1: safety reached only repeat 1 (unknown); Inv1758 reached repeats 1/3 (unknown); Inv* and Inv2973-half were tried in all repeats (unknown, pass 1). No full family was kept. v1/v2 core bytes are identical; runtime rollover audit landed afterward and is being rerun as v3.

### For lane A / B / E / Fable

The integrated family is 34 laws (finite pass dropped 6 in the recorded v1 trace, including `CV at most 2`). The remaining unweakened overlap and disabled variants still consume attempts. Pass-1 Inv* about 3,071 units, overlap-half about 3,055 when it finishes its allowance, Inv1758 about 2,997: all unknown. Deadline overruns are now only atomic-query-scale in these traces; the finish line is not reached. This is combined-system evidence, not a request to adopt the rejected disposable leaf/class policy.

v3 now binds the current runtime-audit tip and repeats checks, all changed tests, MLDR ×3 and generation census. Prior type/lint failures in I's report script (optional placement; unused omitted-log binding) are recorded at `current-check/`, `fixed-check/`, and `after-b-check/` and fixed in separate commits. These do not change the engine.

## Runtime test repairs and final mechanics

Fable's `4b57a3b2` fixes its new rollover test: a sparse `[300,2]` call correctly takes the Set path and does not reset the stamp; an added dense call checks growth/reset instead. This test-only tip and F's complete stopping report `d5d14cc9` are merged. F's original full triple is also unknown and its 14 direct operation pairs showed no row-split gain; no promotion claimed.

The fresh v3 check exposed another inherited test issue: `new Function` violates `typescript(no-implied-eval)` in `core/runtime-keys.test.ts:55`. Replaced only the fixture execution with `node:vm.runInNewContext`; the generated source and all rollover assertions are unchanged. Both the original test assertion failure and lint failure remain in `v3/validation/`; corrected tests passed in `final-mechanics/` but its check still caught the lint issue. `final-mechanics-v2/` reruns all 109 changed test files and full check after this repair. No production behavior changed.

## Current lane ledger and commit policy blocker

All current committed tips are merged: A `f7894c43`, B `a778692e`, E `80f277d7`, Fable wall `4b57a3b2`, F `d5d14cc9`; main remains `b788e195`. The last A/B updates only strengthen their research checks/records; no production changes. Their report conflicts keep pointers, not copied prose. B's helper-only cap candidate remains research-only as intended.

**Commitlint is not green.** `runs/lane-i/commitlint/results/commitlint.log` checks 24 Lane I first-parent messages through `6dc0c8b0`; 14 earlier integration merges used `merge(research): ...`, which conventional commitlint rejects (`type-enum`). This is my integration-message error. They are not hidden, reclassified, or rewritten: history rewriting was not authorized. Subsequent merges use `chore(merge): ...` and subsequent ordinary commits use allowed conventional types. This remains an explicit acceptance blocker alongside MLDR; adding a new commit cannot change an old header.

The current production source remains byte-identical to v3 `1d7a276d` (excluding only the repaired runtime test). Later changes are tests, research evidence, and this report. All work is local; no branch push or merge into main occurred.

## Completed integration evidence, and next pushed runtime change

For production snapshot `1d7a276d` (v3): the **entire census is complete, 87/87 successful pairs, zero proof queries, all 84 non-MLDR lists byte-identical**. MLDR is 27 → 34 laws in all repeats; candidate canonical hash `dd495ab653ff4376b1c7b8c462c7dfafbcf9b3f5fc27949b8d61543ad5c69563`. Candidate generation walls: 12.260 / 14.834 / 11.886 s versus main 27.179 / 26.817 / 21.794 s. Six previous 120 s census timeouts are retained; the correctly allowed slow jobs returned successfully (261–482 s paired).

Post-repair mechanics: `final-mechanics-v2/` passes **585 tests, 19,580 assertions**, and full `bun run check` (zero errors/warnings). `current-tip-check/` independently passes full check after the latest research-only merges. No changes to `kernel/kernel.ts` or `lean-kernel/` relative to main. Neither result is a Lane D final gate.

V3 original MLDR remains **unknown in all three repeats**: 59.026 / 59.001 / 59.002 s. First-attempt walls 23.284 / 14.235 / 19.491 s; 34 laws each. Inv* pass 1: 3,071 units, unknown all three; Inv2973-half: 1,807 / 3,055 / 3,055, unknown. Inv1758 is not reached in r1, unknown at 2,997 in r2, then wall-cut immediately in r3. Safety not tried in any v3 repeat. This is the measured stop: helper/candidate cost still blocks the original harness.

New tips then arrived and were merged: E `e3adcdb3` (conditional lemma reduced to five checked premises, NOT a safety proof), F `3af7e73a` (diagonal source diagnostics), B `568fc570` (original-family audit capture), and wall `eb9aad68` (production per-step key-array cache). The cache's `$c` is allocated inside each compiled `step`; all writes remain after computed read expressions. Existing 2,400-step interpreter/compiled comparisons cover repeated steps; no assertion or budget was removed. Conflicts were only reports; the runtime patch merged cleanly with cancellation and overflow fixes. The wall patch is a real production delta, so v3 results are NOT promoted to this new SHA.

Fresh snapshot `d99480e80c1466cd97e8fe588646003f60c9dda6` is running the complete Lane I validation and 87-pair census in `runs/lane-i/v4/`. Its input identity was expanded from an abbreviated to full SHA immediately after submission; guest copies will be checked rather than presumed. All recent merge commits now use `chore(merge):`.

## V4 validation: current production, 2026-11-09

V4 validates the per-step key cache on `d99480e80c1466cd97e8fe588646003f60c9dda6` (guest identity prints unique abbreviation `d99480e8`; it is expanded here, not retroactively edited in raw logs). The latest E `30c4c889` and wall `21fee653` tips are also merged; neither merge changed the production source or the tested TypeScript files. V4's `bun run check` is clean and **585/585 tests, 19,580 assertions, zero failures** pass on boat.

All three original MLDR repeats still return **unknown**, 59.021 / 59.008 / 59.002 s, on AMD EPYC 4585PX. Candidate count remains 34. Wall before first attempt: **13.895 / 17.637 / 11.975 s**. Inv* pass 1 costs 3,071 units in each repeat, unknown; Inv2973-half costs 3,055 in each, unknown; Inv1758 costs 2,997 in r1/r3, unknown, and is not reached in r2. Safety is never attempted. The full fresh census is still running; its absence is not counted as a pass. A fresh check on the report-refreshed tree is also running.

## V4 census complete; new A/B/E/F/wall tips integrated

V4 is complete: **87/87 generation pairs pass, 84/84 non-MLDR pairs are byte-identical, and the Lane I analyzer has no missing/failed-job issues**. MLDR stays 27 → 34 laws with the same canonical hash in every repeat. Paired generation wall, candidate vs main: 21.123 vs 26.168 s; 16.432 vs 24.555 s; 14.088 vs 25.867 s. This is generation-only, not 29/29 proof. Refreshed full check also passes (`v4/current-tip-check/`).

While those jobs ran, all lanes pushed again. Integrated A `c21a6e54` (paired side exit propagation + regression test), B `539bde1b` (original-family audits), E `3f3a523c` (withdrawn exact-suite interpretation), F `36210941` (independent empty-count reconstruction), and wall `c775d8c1` (explicitly reverted per-step key cache). Only report conflicts occurred. The wall revert is preserved; integer stamp overflow and the test VM repair remain. F's syntactic emptiness hint drops premises and selects reconstruction; it does **not** admit a fact, bypass the checker, or raise the enclosing budget. Fresh explicit tests for both new files are added to Lane I validation.

These are new production changes, so completed v4 results are historical rather than final evidence for them. A complete v5 repeat is required and is being submitted next.

## V5 validation and latest range integration

V5 full check is clean (zero warnings/errors), and 599 tests / 19,620 assertions pass. Original MLDR verdicts: unknown at 59.006 / 59.010 / 59.049 s; candidate count 34; pre-attempt walls 13.897 / 12.809 / 11.256 s. CPUs are EPYC 4585PX / Ryzen 9950X / EPYC 4585PX. Inv* pass 1 takes 3,071 units, unknown all three; Inv2973-half 3,055 units, unknown all three. Inv1758 is not reached in r1, wall-cut at 0 units in r2, unknown at 2,997 in r3. Sixteen helpers are kept at deterministic units `[88,301,318,316,97,198,64,148,271,70,259,180,64,225,305,240]`; r3 additionally keeps one count-cube helper at 2,170 units. Its trace name is truncated, so no exact helper identity is inferred. Safety is never tried. The v5 census continues independently.

Wall `c21f301c` arrived during validation. Its range constructor is wired into counted passes through parent `d24a4196`; inspecting only the tip's two new files would have missed this. Resolved `core/counts.ts` by keeping B's completion retry and E's preferred member-inclusion selection, adding ordinary kernel-checked range instances at all three certificate construction sites, and retaining the existing shared `attemptEnd`. Resolved `core/finite-houdini.ts` by using the updated dropped-set revisit filter, preserving preconditions, certified drops, changed-read/no-op filtering and outer cancellation; removed only the duplicate relocated `lawReads`. F's independent-empty-source reconstruction stays intact. Removed the new range test's unused `Machine` import and added it to the validation jobs. No checker or Lean source changed. V6 is a new full validation/census snapshot, not a promotion of prior receipts.

## Range follow-ups and tiny-proposer merge

Merged wall `cc7bb326` (missing `CountDecl` type import) and B `803129c4` (the same range integration). Retained one range import, the earlier unused-test-import repair, B's completion and inclusion selection, and all three range insertion sites. The actual v6 check found an additional wrong `modelSequence` import in the range regression test; fixed it to `kernel/model-sequence.ts`. V6 failures remain in `v6/validation/`; they are not recast as passes.

V6 original MLDR is unknown at 59.017 / 59.004 / 59.003 s; pre-attempt walls 14.085 / 14.813 / 12.040 s. Sixteen helpers kept in each repeat. Inv* costs 3,071 units, Inv2973-half 3,056, Inv1758 2,997, all unknown in all three. Safety is not attempted.

Merged A `fdabeba4`: the new bounded tiny-instance proposal module and independent replay wrapper are experimental, not called by production generation. Resolved the added wrapper versus relocated `lawReads` by keeping both; the optimized ordinary finite path and outer cancellation remain. Added both new test files to Lane I's changed-file jobs. A tiny screen is never itself a proof or a certified drop: the wrapper requires the full family, facts/precondition and source interpreter replay. The complete v7 validation/census is the next snapshot.

### For lane A / B / Fable

The combined range+completion+preferred-inclusion path still exhausts the original helper limits in all three v6 repeats. Range seeding does not alone get safety scheduled. The import repairs above are integration-only, not weakened tests or changed budgets.

## V5 census closed

All **87/87 paired generation receipts** are successful, zero missing/failed-job issues; all **84 non-MLDR lists are byte-identical**. MLDR is 27 → 34 laws with unchanged canonical hash. Paired generation candidate vs main: 13.198 vs 20.237 s; 13.376 vs 22.356 s; 12.647 vs 24.950 s. This closes the historical v5 cycle (clean check, 599 tests, strict MLDR unknown 3/3), not the newer range-enabled candidate.

## V7 completion and coordinator upper-bound census

V7 (`704efc27694151cd4797707ebf5b8aea5b8df318`) completes with clean check, **621 tests / 19,688 assertions**, and **87/87 successful generation pairs**; all **84 non-MLDR candidate lists are byte-identical**. MLDR generation is 27 → 34 laws, same canonical hash. Candidate/main generation wall: 15.665/29.999 s, 12.576/20.434 s, 12.723/20.218 s. These are generation results, not a proof gate. F `15dc5ebc` subsequently merged with no production delta; the repaired range imports were retained.

For the coordinator's new upper-bound request, the unchanged original admission path captured **exactly 34 laws**, no supplied laws, at production SHA `15eff72f04f74351b622b02d08e47bfb9dfdb131`; family SHA-256 `5dbdbf766e9949b051d0764920f1bcc3707690cd6852fca6d0bcf18674fbdac4`. The actual dispatch has seven values (0..6), so the full roster is **140 shards** = five requested helpers/safety × seven ops × two passes × ceilings on/off. All jobs are submitted together, each exclusive large VM, 30-minute wall, effectively unlimited counted budget (`1e12`), no shared/subset pass allowance. See `research/lane-i/upper-bound/README.md` for the exact conditional STEP scope and ceiling-off changes. Both smoke variants executed real searches, source hash checks and CPU labels; they were deliberately censored at 2 seconds, not claimed as proofs. Full results are pending in `runs/lane-i/upper-bound/full/`. Integration continues separately.

## V7 original-harness stopping point and active research

The completed v7 strict runs are unknown at **59.012 / 59.018 / 59.147 s**; pre-attempt walls **11.746 / 15.935 / 14.778 s**. Inv* consumes 3,071 units and Inv2973-half 3,056 in every repeat, unknown. Inv1758 consumes 2,997 in r1 and is wall-cut at 0 in r2/r3. R1 keeps 18 helpers and reaches safety (still not proven); r2/r3 keep 16 and never try safety. No proof-gate claim follows from the clean mechanics and generation census.

Upper-bound implementation check is clean on boat. The 140-shard research batch is active; every shard is source-hash checked before disposable instrumentation. Source remains frozen at `15eff72f` for this census even as integration resumes. Results require independent certificate verification; missing records remain pending, and forced stops report counted work only as a lower bound. Aggregation tests explicitly cover those cases.

## Integration after the upper-bound snapshot

Merged E `36a278e9` (including B `6d69e094`, F `682c8dc6` and declaration-backed member premises), then Fable `5bf4535e` (demand-driven range repair). E adds ordinary member witnesses and only instances of existing declarations, under its 64-tuple / four-per-source limits; count-witness read-key independence remains enforced. Fable now adds a 0/1 count's range only when a model violates it, rather than eagerly burdening every goal. Its lane reported that eager ranges cost a non-MLDR verdict, which a generation-only census does not detect; Lane D's proof roster remains required.

Conflicts: retained `memberSources`, the guarded witness filtering, B's completion retries and E's preferred inclusion fallback; adopted `rangeWanted` with read lists on all certificate branches and range-triggered rebuilding in both model loops. Kept one import per symbol. The relocated finite `lawReads` and newer dropped-set replay logic survive unchanged. Added new member-premise and upper-bound aggregation tests to Lane I's jobs. The new source gets a complete v8 check/test/strict-MLDR/census batch. The already-running upper-bound shards are intentionally still bound to their earlier source manifest.

## B stopping-evidence refresh

Imported B `00a7d516` and its force-added raw archives. `research/track-m/LANE-F-HANDOFF.md` now records the original-34 Inv1758 early-entry limit: 6,002.553 counted units / 6,040.223 ms with field/row cases still open, not a proof. No derivability-closure/class-order events occur for its field-only claim. Baseline is wall-limited at 2,679.971 units / 7,018.544 ms, so this is not a same-budget cost win. These diagnostic results do not change the production settings, v8 source changes above, or the final gate status.

## Coordinator test-load alert and F refresh

Integrated F `53bf1264`: compensated directed-difference frame proposals retain the old difference under the existing cap and are checked by the original kernel. The coordinator flagged F's old `modelSequence` import. Integration already imports it from `../kernel/model-sequence.ts` (not `kernel/prove.ts`), but the quick-suite manual roster did omit this new test file. Added `core/count-ranges.test.ts`, `core/count-write-frames.test.ts` and `core/count-recovery/member-premises.test.ts` explicitly to `scripts/test-shards.ts`. No suite runner swallows a nonzero child status; its `--measure` route also fails if any file fails.

Added `research/lane-i/test-load-propagation.test.ts` to both the quick roster and Lane I validation. It creates an isolated real missing-export fixture beside a passing test, requires Bun to fail, then runs the actual quick-suite driver with that failing test group and requires failure/stop before the next group. It also asserts the explicit roster entries. Thus a passing file cannot mask a module-load error. These changes and the actual range test are pending boat validation below; they are not yet claimed green.

## For lane D

Please run the independent one-command final gate on **`704efc27694151cd4797707ebf5b8aea5b8df318`**, the current best combined A/B/E/Fable/F candidate (range insertion, preserved completion/preferred inclusions, F's independently reconstructed empty sources, tiny proposer present but NOT active in generation). Baseline is `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`. Lane I's full v7 checks and 87 generation pairs have been submitted on that exact SHA. This is a request, not an assertion they passed. V6 still had 3/3 original MLDR unknown and two now-fixed import failures, so a red gate remains expected until measured otherwise. Bind both SHAs, exact roster, paired identity, CPUs, DuoAI/broken/bar and full check/tests; only your complete receipt may authorize GATE GREEN. If a newer lane changes production, I will explicitly supersede this SHA, not silently transfer your result.
