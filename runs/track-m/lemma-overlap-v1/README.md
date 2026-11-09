# Field/frame overlap: existing receipts only

## Finding

**The requested per-lemma cost and once-per-law saving are not recoverable from T-12's receipts.** This is an instrumentation gap, not evidence of zero overlap. No proof search, policy change or replay was run to fill it.

`research/track-m/section15-run.ts` passes `trace:()=>{}` to `proveCountCases`. The latter forwards the helpers' events through `options.trace`, so those events were discarded. The T-12 installer wraps complete helper calls; `Diagnostic.run` records their durations, not arguments or returned proofs. Each of the three T-12 receipts therefore has **zero retained field/frame lemma events**. Setup, selection, failed attempts and transport are included in the aggregate helper costs. These are not measured costs of identified reusable lemmas.

## Available T-12 accounting

| Law/op | Field-bound exclusive units | Frame exclusive units | Other units | Per-lemma inventory/cost/scope |
|---|---:|---:|---:|---|
| Inv2973 op 0 | 595.250050 | 1,536.028532 | 578.287112 | not recorded |
| Inv2973 op 4 | 2,183.805296 | 994.374321 | 810.643595 | not recorded |
| Inv* op 3 | 832.072456 | 236.799779 | 1,383.481384 | not recorded |

| Law | Covered ops only | Observed subtotal | Field + frame work | Remainder if **all** helper work were free | Actual once-per-law result |
|---|---|---:|---:|---:|---|
| Inv2973 | 0, 4 | 6,698.388905 | 5,309.458198 | 1,388.930707 | **unknown** |
| Inv* | 3 | 2,452.353619 | 1,068.872236 | 1,383.481384 | **unknown** |

The free-helper column is only subtraction on the fixed old trace, **not a caching estimate, attainable lower bound or whole-law cost**. It removes failed/setup work, charges no first proof, ignores changes to later search and omits other actions. No reusable savings are credited. `null` in [summary.json](summary.json) means unavailable, not zero.

## Recoverable historical statements

The offline census scanned **39 archives** plus existing logs, including Inv2973 op 0–6 and Inv* op 3–6 shard receipts. Twenty-eight archives had matching local SHA manifests; eleven lacked one and are marked unverified. No available manifest mismatched; no archive parse failed. Repeated files/tails are not independent measurements.

Seven distinct field/domain statements occur in positive historical records for the two requested laws. They are **not the T-12 inventory**. Define `B(g,k) := if(g=1 && k<size, CfgT[k], 0) <= CT[i]`:

| ID | Normalized statement | Literal op / guard flag / post-map reference | Old recorded `ms` range |
|---|---|---|---:|
| F1 | `B(?committedQuorum,j$)` | no / yes / no | 9–143 |
| F2 | `B(?canVote,j$)` | no / yes / no | 12–266 |
| F3 | `B(?committedQuorum,i)` | no / yes / no | 14–164 |
| F4 | `B(?canVote,i)` | no / yes / no | 12–440 |
| F5 | `j$ < size` | no / no / no | 0–50 |
| F6 | `i < size` | no / no / no | 0–50 |
| F7 | `B(?canVote,a$#)` | no / yes / no | 85–126 |

These are **rounded historical clock deltas**, not matched T-12 per-lemma counted costs. A rounded zero does not establish a free proof. `a$#` is a retained quantifier variable, not a post-state map read. Literal-reference flags do not describe missing proof dependencies or expanded guard definitions.

| Law | Recorded op | Recoverable positive-event statements |
|---|---|---|
| Inv2973 | 0, 2 | F4, F6 |
| Inv2973 | 3, 5, 6 | F6 |
| Inv2973 | 1, 4 | none recovered; actual set unknown |
| Inv* | 0, 1, 2, 4 | F1–F6 |
| Inv* | 3, 6 | F5, F6 |
| Inv* | 5 | F1, F2, F5, F6 |
| Inv* | op omitted | also F7; checked historical records occur here |

None of the explicitly op-tagged normalized field records for these laws has `checked:true`; many are marked proposed/deferred. Older checked field records omit the op. They cannot establish checked, root-valid facts for a particular T-12 action.

The historical corpus also has **4,323 positive indexed frame-event records**, including duplicate logs/tails, without a statement mapping in retained context. For example, `frame-lemma, index=26, ms=149, proved=true` does not identify a statement without its exact certificate. These stay unresolved rather than borrowing indices from another layout.

## Overlap and limits

- Historical **syntactic field-statement** intersection across the two laws is **two**: F4 and F6. Inv* has seven recovered forms, Inv2973 two.
- Inv* ops 0/1/2/4 share six recovered forms; 3/6 share two. Inv2973 ops 0/2 share two. Missing records do not mean empty proof sets.
- This is not overlap of checked op-independent lemmas. F4 explicitly uses `?canVote`; even F6 may have been proved only under a branch already assuming `i<size`. No literal `op` or post-map reference does not establish root independence.
- Actual reusable overlap and the units remaining after once-per-law proofs remain **unknown**.

A sufficient future receipt needs statement/read mapping; op/pass/row path; checked/deferred status; used proof premises including flags and prior cuts; and per-lemma `fullWork/fullRate` start/end counters with setup/failed/transport work separated. **None was recaptured here.** T-12 remains stopped.

## Evidence

[Summary](summary.json) contains full normalized expressions, per-law/op status and clock ranges, source hashes and examples. `../section16-census-v2/receipts.br` contains the complete extracted event catalogue, unresolved records and coverage. `../section16-census-v1/` is the preliminary tracked-only scan; `../section16-report-v1/` contains final validation.

The census, normalizer and report scripts under `research/track-m/section16-*` use no prover imports. Typecheck/lint and **3 tests / 6 assertions** pass. Tests preserve guards/post-state and keep unmapped frame indices unresolved. Production and kernel are unchanged. Audit tools: `bcc61801`. All jobs exited; owned remote temporary outputs/chunks were removed by exact path after local checksum verification.
