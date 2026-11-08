# Section 10 — Gate 1 five-law replay

**Not passed: 3/5 in every repeat.** Thirty verdicts match A exactly. One primary,
Inv3915 and Inv1758 check; Inv2973 and Inv* remain unproved. No verdict regression.

A is exact **50109a36**; B's core is **192ebbe2**, including the prior F1/F2/F3 and
retarget-cache changes. This is not an isolated speed comparison of the new
proposer. A1/B1/A2/B2/A3/B3 ran in fresh processes on **bx_25xas5gt**, exclusive,
8 pinned vCPUs. `placement.json` confirms the same calibrated large VM.

The original `profile-family.ts` is byte-identical on both sides, including the
final `checkMC` calls. Kernel files, dependency pins and canonical fixture match.
There is no 60-second wall truncation of an individual law in this batch. Open
laws reach their existing counted allowance; small differences in cap-overrun
bookkeeping are not successful work savings.

## Counted units — primary cost

All values repeat identically except A Inv*, whose triple is shown.

| Law | A | B | Verdict in all six runs |
|---|---:|---:|---|
| one primary | 926.633492 | 947.543254 | checked |
| Inv3915 | 872.335254 | 874.116294 | checked |
| Inv1758 | 4310.475353 | 4312.612601 | checked |
| Inv2973 | 5002.653010 | 5001.811726 | unproved |
| Inv* | 5161.293823 / 5161.293823 / 5161.982847 | 5160.104960 | unproved |

Compared with A, B adds **20.909762**, **1.781040** and **2.137248** units to the
three checked laws; their counted work is **not** identical to baseline.

## Wall seconds — median / maximum of three

| Law | A | B |
|---|---:|---:|
| one primary | 2.129 / 2.317 | 1.661 / 1.667 |
| Inv3915 | 2.616 / 3.804 | 1.838 / 2.007 |
| Inv1758 | 13.519 / 13.527 | 8.962 / 9.194 |
| Inv2973 | 32.391 / 35.079 | 23.263 / 24.623 |
| Inv* | 34.456 / 36.587 | 27.479 / 29.589 |
| full five-law process | 86.313 / 87.222 | **63.009 / 67.076** |

B's family walls are **63.009 / 67.076 / 62.618 seconds**. All are above 60,
in addition to the two missing proofs. No original generated-family harness or
later gate was run. The replay's strict family pass condition is false.

The baseline's open-law walls are close to v7's 32.069 / 35.274 seconds, unlike
the previously degraded VM. The fresh calibration and these family controls
are different harness measurements; do not derive a slowdown factor from them.

## Cache observations

Inv* is the only law exercising these conditional caches. Each B repeat reports
retarget **33/42** hits, independent-check **90/102** hits, 80 sliced checks,
**39,160 full-goal hypotheses -> 98 sliced hypotheses**, and zero full fallbacks.
These are fewer traversed checks because recovery stops early, not evidence of
complete-law progress. F1/F2/F3 remain enabled and their kernel boundary is intact.

## Retained evidence and remaining obstruction

`measurements.json` contains all thirty law results; `summary.json` contains the
computed table. All six stdout/stderr pairs, manifest and validation output are
in `receipts.br` and decoded alongside it. The independent table audit and final
checks are in `../section10-final-validation-v2/`.

T-10A established and replay-checked the new guarded cut. The active full-pool
probes in `../section10-implementation-v2/` show why that is insufficient: the
first row's shared 1,500-unit deadline still expires with open work (one Inv*
scalar subbranch checks; its sibling does not obtain a numeric result in time;
Inv2973 also expires there). This is an **allowance-limited traversal result**,
not a protocol counterexample or a newly established generator gap. No cap,
total allowance, trusted rule or original family harness was changed to pass it.
