# T-12 — production-budget policy experiment: stop

**The stopping rule is triggered.** With all three research flags enabled, Inv2973 op 4 remains unknown after **3,988.823212 counted units**, above the prescribed 2,500-unit line. Its checked source queries cost only **17.229798 units**. No further policy optimization or production integration was attempted after the corrected result.

Production and the kernel are unchanged. This is the frozen `5974b916` proposer, with trace hooks and the requested untrusted policies applied only in a disposable copy. Each captured op starts the ordinary count-case procedure with a **5,000-unit total law allowance**. Other ops are skipped, not charged as if proved. The existing action shares, row draws, 1,500-unit row ceiling, 250-unit field-source ceiling and source-query ceilings remain active. There are **no injected root facts** and no inflight columns dump.

## Results — corrected classifier, one VM

All three fresh processes used one prepared runtime sequentially on exclusive **`bx_25xas5gt`**, large AMD Ryzen 9 9950X, eight pinned vCPUs, no co-tenants. No repeated wall gate is claimed.

| Captured op | Closed / checked | Units | Replay seconds | Terminal leaf visits | New cuts | Source SAT / checked-refuted / unknown |
|---|---|---:|---:|---:|---:|---:|
| Inv2973 op 4 | no | 3,988.823212 | 10.320221 | 2 | 4 | 2 / 2 / 3 |
| Inv2973 op 0 | no | 2,709.565693 | 7.589855 | 1 | 1 | 0 / 0 / 1 |
| Inv* op 3 | no | 2,452.353619 | 4.801551 | 2 | 0 | 0 / 0 / 3 |

None meets its prediction (op 4 ≤1,500, op 0 ≤800, Inv* op 3 ≤1,000, each closed). Unlike the T-11.5 extractor, this probe lets an unfinished selected op receive its normal second-pass fallback before returning. The totals include both passes. The intervals include proof search and the final live kernel check, but exclude input loading, output serialization and archive creation.

| Op | Initial action pass | Retry pass | Outside closure | Inside closure | Checked source queries |
|---|---:|---:|---:|---:|---:|
| Inv2973 op 4 | 2,217.598432 | 1,771.138314 | 3,729.512722 | 259.310490 | 17.229798 |
| Inv2973 op 0 | 1,122.005782 | 1,587.473446 | 2,682.603815 | 26.961878 | 0 |
| Inv* op 3 | 1,414.785135 | 1,037.532006 | 1,229.314490 | 1,223.039129 | 0 |

Initial + retry omit a small global fallback precheck: 0.086466 units for Inv2973, 0.036478 for Inv*. Inside/outside closure partition the **entire** measured total. Checked source-query units are a subset, not another additive phase.

## The requested action-level split

**No six-round query-loop round ran in any of these three production-budget replays.** Neither `seq`, `coreGrow`, the first-pass grow nor the direct guard grow was reached. Each selected op reached the retry-pass `count-cases` grow once.

Exclusive units outside closure:

| Site / stage | Inv2973 op 4 | Inv2973 op 0 | Inv* op 3 |
|---|---:|---:|---:|
| `guard-cases` → `fieldBoundLemmas`, excluding nested closures | 2,183.805296 | 595.250050 | 832.072456 |
| `guard-cases` → `frameLemmas` | 994.374321 | 1,536.028532 | 236.799779 |
| retry-pass `count-cases` → `grow` | 551.246640 | 551.238768 | 160.405776 |
| global fallback `refuteFast` | 0.086466 | 0.086466 | 0.036478 |
| **Total outside closure** | **3,729.512722** | **2,682.603815** | **1,229.314490** |

Every configured action/guard call site is traced with a source site, count, inclusive units, exclusive units and maximum call size in [summary.json](summary.json). Nested units must not be added to their parents. The field-bound and frame helpers dominate this T-12 run; this is not a matched-budget attribution of the earlier 50,000-unit T-11.5 runs. In particular, 80–90% 'outside closure' did not identify a single universal hot site.

The preserved row draws were tiny:

- op 4: **116.660918**, then **22.009527** units;
- op 0: **23.787147** units;
- Inv* op 3: **41.267257**, then **22.145407** units.

The engine's counted ceilings are checked at operation boundaries, not hard preemption points: some calls/rows overrun their deadline. The 600 cap is an upper bound on the passed deadline, not a guarantee that an atomic preparation can never spend more work. Even excluding the final 551.247-unit grow, op 4 already spends **3,437.576572 units** without closing, above 2,500. No extra cap or allocator change was introduced to hide this.

## Exact flags and scope

- **Action cap:** a shared 600-unit horizon for the six-round model-query/core-grow/final-grow group, bounded by the existing case end; direct guard and retry grows also receive `min(original end, now + 600)`. Closures themselves are not capped to 600.
- **Class batches:** only the cheapest currently pending class is offered to the selector: same/proven-equal-key frames on unchanged support maps, decreasing written-map frames away from the written key, hinted guarded inclusions, syntactically equal bodies, remaining inclusions, partitions, ranges, zero claims. Class membership is a proposer heuristic, never a premise; all admitted cuts retain the unchanged checker.
- **Model first:** a numeric model query precedes natural-case splitting; a checked tree, a refuted core, or a validated SAT point suppresses the natural pre-pass. None of these runs executed a natural-case probe.

First recorded unfinished scopes (from the initial pass, not alleged whole-law counterexamples):

- op 4: `started=1, a$#=i, b$=i`, **133** violated instances;
- op 0: `started=0, a$#=0, b$=0`, **101** violated instances;
- Inv* op 3: `started=1, a$#=j, j$=j, CT[j]<CT[i]`, **31** violated instances.

The summary preserves every full numeric point, exact path and violated set. All three pass independent exact-integer path/violated-set auditing. Full source attempts, frames and traces are in the primary compressed receipt.

## Interpretation and stopping

The requested operational stopping rule fires on op 4's **observed spend without closure**, not on its checked source work. This rules out integrating these three policies as a demonstrated fit for the current allowance. It is **not a mathematical lower bound** on every possible proof of MLDR, nor a claim that the leaf's needed facts alone cost 3,988 units. The measured failure is dominated by existing guard/field/frame preparation and the preserved small draws.

Work stops here as requested. The constant 600 remains research-only; no derived production rule or new budget was landed, and no whole-law proof, nonregression gate or speedup is claimed.

## Evidence and validation

Research implementation: **`597c2867`**. Remote chunk and output directories were removed by exact path after checking all local archive hashes and both archived runtime-bundle hashes. All started jobs have exited.

- **Primary:** `../section15-t12-v3/` — checksum-verified `receipts.br`, source/kernel integrity census, prepared runtime and all three original results.
- **Independent audit:** `../section15-audit-v1/`, and this directory's audited summary/archive. All frame/ledger identities and three complete numeric points pass. Typecheck/lint and **3 policy tests / 8 assertions** pass.
- **Retained non-primary attempts:** `../section15-t12-v1/` stopped on a missing explicit return in the research driver. `../section15-t12-v2/` is an initial pilot whose frame class was too broad: it treated unequal keys as an unchanged frame. The classifier was corrected and a regression added before the primary run; the pilot is not used for the stopping verdict.

Reproduce with `research/track-m/jobs-section15.json`, `--class submission --timing --vm-type large --vms 1 --max-vms 1`, data `runs/track-m/section12-source-input:source-input` and `runs/track-m/section13-runtime-v1/ready:runs/track-m/section15-runtime`. One build and install serve all three processes. `jobs-section15-audit.json` audits extracted primary files under ignored `runs/track-m/t12-input`. No source file outside `research/track-m` is modified in this checkout.
