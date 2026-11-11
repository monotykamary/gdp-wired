# Admission overhead reduction — measured, source-bound

**Production patch:** `2eec34ce64b59c154d2d6042f26478ef23bfa19f`.
**Native tested source:** `3d0256f0ee6a578ad005b9169c4cff3cd2eaf602`.
**Baseline:** `00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7`.
These comparisons predate I6's new table/check/cube writers.

## Change

`core/work-meter.ts` computes the same 26-term weighted sum in exactly the old floating-point addition order, without dynamic-key loops. `core/work-observe.ts` specializes the overwhelmingly common single interpreted evaluation. Every evaluation still invokes the same admission function. No batching, budget credit, price change, scope change or checking-rule change. Flags-off keeps the historical sum loop.

## Native measurements (boat)

Batch `20261111-041759-v2imrf`, one VM per job, zero co-tenants, four pinned vCPUs, AMD Ryzen 7 9700X. ABBA order; two fresh-process measurements per source on each same VM. Times exclude source extraction and installation.

| Workload | Raw evaluations | Identical work units | Baseline mean ms | Candidate mean ms | Ratio |
|---|---:|---:|---:|---:|---:|
| Native finite evaluator, original MLDR T=1/V=2 | 249,229,203 | 5,246,726.0600000005 | 238,301.09343 | 14,491.007142 | 16.4448x |
| Native compiled-predicate path, same fixture | 305,501,358 | 6,372,169.16 | 374,287.0899705 | 14,999.5165225 | 24.9533x |

Finite samples: baseline 250,421.18 / 226,181.01 ms; candidate 13,383.96 / 15,598.05 ms. Compiled samples: baseline 321,226.10 / 427,348.08 ms; candidate 15,477.72 / 14,521.31 ms. These are paired workload measurements, not a fitted reference-host model.

Both sources retain 3,286 states, 75,118 steps, depth 12, 2,298 boundary states and broken set `[6,14,34,37]`. Each comparison requires exact raw vectors, weighted units, profile and full non-time native result equality. The finite unknown-evaluation set remains `[13]`; the compiled path's remains empty. The fixed 49-law capture/model hashes are enforced by the reused native probe.

## Microbenchmark and correctness

Pilot batch `20261111-041441-kni4ly`, AMD EPYC 4585PX, same-VM ABBA: 1.8M expression visits / 36,000 units; mean 1,618.1419315 -> 23.364436 ms (69.2566x). The harness explicitly verifies one admission per node. All raw columns match.

26 tests / 123 assertions pass on the admission-only pilot. Ordered-sum tests cover every column and 1,000 mixed vectors across flags on/off and three weight profiles. 134 protected identities and the prover tail remain exact. The first static failures were harness-only array typing and are retained. Corrected full static passes on `1066f267` with the subsequent I6 patch present (1,791 files).

## Limits

No claim that the entire proof engine speeds up by these ratios. No final W calibration, whole-integrated no-loss result, or I6 tail speedup is inferred. The new wall cost is source-specific; a fit measured on `00b58ee5` cannot be transferred silently. Native and pilot receipts are preserved under `results/`.
