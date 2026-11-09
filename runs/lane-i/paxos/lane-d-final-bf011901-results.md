# Final gate: bf011901 vs 4497c4b0 — RED / incomplete

Candidate: **`bf01190119f9409077a36e11a4a5b763fb6c1cad`**.

Baseline: **`4497c4b05c3111959a2b8d808c426a0e3cab3f01`**.

The unchanged requested gate finished with **exit 2**, **`green: false`**, **`complete: false`**. Its execution is terminal; “incomplete” is the acceptance result, not a still-running task. Neither the baseline, source, roster, budget nor deadline was changed. No replacement gate or selective proof retry was started.

## Strict proofs, checks and controls

- Candidate strict IC3Syn: **81/87**, versus baseline **84/87**. All three paired losses are `paxos_epr`; original MLDR is unknown **3/3 on both sides**.
- Both full TypeScript/lint checks exited zero. Full test totals: baseline **1,085 pass / 0 fail / 17 skip / 589,640 assertions**; candidate **1,472 pass / 0 fail / 17 skip / 596,291 assertions**. These are this exact run's totals, not earlier qualification results.
- Broken controls proven: **zero**, but coverage is incomplete. `sharded_kv_no_lost_keys` timed out with exit 137 on both sides. Broken `paxos_epr` timed out with exit 137 on baseline; candidate returned unknown with exit zero. Neither incomplete control is treated as a successful negative-control check.
- All 162 scheduler jobs exited zero. The batch/controller status is not a proof verdict: the official paired wrapper allows an unknown answer or recognized timeout to finish, and the final gate correctly rejects the incomplete proof/coverage outcomes.

### `paxos_epr`: the three actual proof regressions

Each is an exclusive, same-VM pair with 8/8 vCPUs pinned. Wall times are the gate's observed PAIR intervals, not model-normalized comparisons. The unchanged strict timeout is 60 seconds per side.

| Repeat | CPU | Baseline | Candidate | Baseline solver / full work | Candidate solver / full work |
| --- | --- | --- | --- | --- | --- |
| 1 | AMD EPYC 4585PX | proven, 23.085 s | unknown, 59.110 s | 8,719,080 / 1,135,224 | 96,539,295 / 9,528,883 |
| 2 | AMD EPYC 9455 | proven, 21.529 s | unknown, 59.119 s | 8,719,080 / 1,135,224 | 146,465,379 / 13,065,907 |
| 3 | AMD Ryzen 7 9700X | proven, 18.025 s | unknown, 54.896 s | 8,719,080 / 1,135,224 | 168,623,843 / 15,000,513 |

Both child processes exited zero in each pair: these are completed **unknown** answers, not three claimed crash/OOM diagnoses. These measurements locate the loss; they do not establish its code-level cause.

### `consensus_forall`: all three official pairs proved

The earlier qualification is not substituted for these results. Actual same-VM walls were 40.381→33.427 s (Ryzen 9 9950X), 27.109→17.474 s (EPYC 4585PX), and 44.552→34.380 s (Ryzen 9 9950X). Both sides proved in all three pairs. Candidate full work remains **3,256,350**, versus **2,665,853** baseline; candidate solver work is **11,093,727**, versus **14,498,189** baseline. Faster walls do not hide the increased full-work counter.

## Canonical bar: not a complete no-loss result

The bar controller exited zero, but the final receipt has **`bar.ok: false`**. Its errors include:

- CHC losses: `vmt-chc-benchmarks/ctigar/hsortprime.c_000.yml` and `vmt-chc-benchmarks/ctigar/up3.c_000_001.yml`. Aggregate CHC solved counts (candidate 518, baseline 517) do not erase those task-level losses.
- Candidate ITS errors: `bio.t2.ari` and `cover.t2.ari`; candidate ITS-SCC error: `bio.t2.ari`.
- Candidate TIP errors: `tip2015/tree_Flatten3.smt2` and `grammars/simp_expr_unambig2.smt2`; baseline TIP error: `tip2015/tree_Flatten3.smt2`.
- F2 `50-frontier` missing/failed on both sides; baseline one-CPU `base-infer-1` missing/failed, so its required six successful jobs and three-repeat test observations are not satisfied.

### All seven requested identities: actual first-pass records

These are the retained runner labels, **not** inferred zero exits. Full task names and original indices are preserved in `summary.json` and the raw selected JSONL files.

| Original index | View / task | Baseline record | Candidate record |
| --- | --- | --- | --- |
| 1 | CHC `ctigar/seesaw.c_000.yml` | sat, checked IMC, 46.95 s | sat, checked IMC, 46.53 s |
| 2 | CHC `lustre/DRAGON_4_000_001.yml` | unknown, 58.09 s | unknown, 58.65 s |
| 3 | CHC `lustre/DRAGON_4_e2_2799_000_001.yml` | unknown, 58.11 s | sat, checked IMC, 49.26 s |
| 6 | ITS-SCC `From_T2/bio.t2.ari` | unknown, 58.54 s | error, **exit -9**, 30.15 s |
| 8 | ITS `From_T2/bio.t2.ari` | timeout, 60.61 s | error, **exit -9**, 46.19 s |
| 9 | ITS `From_T2/cover.t2.ari` | timeout, 60.46 s | error, **exit -9**, 41.07 s |
| 10 | TIP `tip2015/list_weird_concat_map_bind.smt2` | timeout, 60.12 s | timeout, 60.66 s |

The unchanged bar additionally reran index 3 three times per side: baseline **sat, sat, unknown**; candidate **unknown, unknown, unknown**. Thus 14 first-pass observations plus six actual rerun observations are retained. Index 3 totals are baseline 2/4, candidate 1/4. No extra reruns were forced for identities outside the canonical differing-task selection. This is not a complete controlled seven-identity no-loss comparison; the historical 42-child experiment remains separate.

### Lifecycle and CPU limitations remain explicit

The CHC wrapper (`compare/chc/modal_chc.py`, also used for boat) obtains `p.returncode`, but chooses the result from the final JSON stage and does **not** save the raw exit code in the emitted row. Its exact source from both roots is retained. Consequently, a checked-IMC stage plus a `sat` answer row is not independent evidence of a zero parent exit; `rawExit: null` remains null. Five checked-IMC records occur among the selected CHC observations, and none is relabeled as a verified parent completion.

The three candidate ITS/ITS-SCC errors do preserve **-9**. That establishes SIGKILL, not its cause: no PID-correlated kernel OOM evidence is present in these bar rows. They are **not** labeled confirmed OOMs. Other timeout labels lack raw exit values; the missing values are not filled with 124 or 137.

CHC per-row CPU labels, two pinned vCPUs, observed VM-item counts and host identifiers are retained in `summary.json`. Those bar rows are not exclusive same-VM timing pairs. ITS/TIP rows lack equivalent CPU fields; no CPU model is borrowed from CHC or historical diagnostics.

## Independent source audit: independently blocking

The exact-source audit remains **blocked** by the public-path false source proof reproduced on both candidate and baseline: `decide(a: "red"): "green"` returns `"green"`, yet source law `result == a` is reported proven and checked. Optional comparison drops `strictOptional` and compares domain-local indices. This is an inherited source-law translation defect, not a new kernel-checker inference or an MLDR-only regression. See `final-audit-bf011901.md` and `final-audit-receipts/choice-law-source-bf011901/`.

## Retention and cleanup

- Original output: `runs/final-gate/integration-bf011901/`.
- Portable exact reports, placement/backend receipts, hash-verified losing/incomplete worker logs, selected raw bar observations and SHA256 manifest: **`research/verify-all/final-audit-receipts/bf011901-final/`**.
- Receipt-only collector: `research/verify-all/bf011901-final-collect.ts`. It validates exact paired source identities and worker-log hashes; it launches no solver and changes no gate verdict. Remote validation batch `20261110-045221-0vhwcf` verified all 35 archived file hashes, collector syntax and the commit message. Log: `final-audit-receipts/bf011901-completion-validation.log`. This is evidence validation, not a replacement gate.
- Gate controller PID 73431 and bar controller PID 73462 have exited. The owned read-only ref watcher PID 76679 was stopped after collection; no helper remains active.
- The separate effect-queue branch remains unqualified after the shared diagnostic failure/censoring. Its earlier small-gate pass is not a root-cause fix and is not substituted into this gate.

**Final result: RED / incomplete. No 29/29 claim, no no-loss-bar claim, and no clean-soundness claim.**
