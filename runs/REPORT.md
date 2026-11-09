# Lane I — continuous MLDR integration

NOT GATE GREEN. Baseline `main` = `b788e195`; branch `claude/mldr-integ`.

Read COMMON.md, MLDR-DESIGN.md Sections 14–16 (including the answered 16.3 audit), and all MLDR-29.md rules, Speed, Gate evidence and Merging. Only Lane D's SHA-bound final receipt can authorize GATE GREEN. No push or merge into main is authorized here.

## Current status

Current lane tips A `fdabeba4`, B `803129c4`, E `3f3a523c`, wall `cc7bb326`, F `36210941` are integrated. V6 exposes two import failures (missing `CountDecl`, range test importing `modelSequence` from the wrong module); both are fixed. V6 MLDR is still unknown 3/3, with 16 kept helpers and no safety attempt. The fresh v7 run includes the new tiny-proposer tests; tiny proposals remain unwired from production generation. Older v5/v6 censuses continue and will not be restarted or silently promoted. No Lane D final gate or 29/29 proof exists. Historical failures are retained; no history was rewritten.

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

## For lane D

Final gate request will name the integrated SHA after check, changed-file tests, strict MLDR ×3 and generation census. No green claim yet.
