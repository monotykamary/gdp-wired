# Section 7 follow-up — T2/T3 measurements only

All measurements use the exclusive eight-vCPU VM `bx_3kjzmmhv`. Production code,
the proposal cap, and budgets are unchanged. No inversion or gate rerun.

## T2

The exact Section 7.5 indices plus the v7 failed leaf's active indices give 32
Inv* and 58 Inv2973 instances. Inv*'s 24 active cuts have 23 unique instance
indices and a non-instance cut. Original IDs are retained in `demand-results.json`.

Literal filtering alone fails. Discarded witnesses' flag/law hypotheses remain
in the source goal but are no longer recognized by its filtered witness set.
The extra hygiene control uses the existing `withoutCountWitnesses` and
`seedCountWitnessFlags` helpers in the research probe only, reducing source
obligations from 378 to 157 hypotheses (Inv*) and 1010 to 205 (Inv2973).

| Hygienic run | Complete conditional source checked? | Cuts | Closure counted units | Diagnostic wall |
|---|---|---:|---:|---:|
| Inv*, active traversal | No: projected SAT | 28 | 3603.309 | 9.266 s |
| Inv*, captured target | **Yes; fixed point** | **26** | **596.934** | **2.990 s** |
| Inv2973, active traversal | No: 13 arithmetic leaves check, next unknown | 67 | 5009.202 | 14.999 s |
| Inv2973, captured target | No: fixed point, projected SAT | 52 | 1062.136 | 8.039 s |

The important Inv* target leaf closes, but the predicted <=22 cuts and full
active completion do not hold. It is a conditional source proof, not a law.
Target scopes use fresh guard atoms plus captured explicit scalar/row atoms;
opaque column IDs are never imported across processes.

R1 (126) checks at 16.927–18.099 counted units. R2 (272/275) checks under
`CfgT[y] < CfgT[i]`, or `CfgT[y] <= CfgT[i]` plus `CV[y] < CV[i]`, at
22.045–25.029 counted units. Those are not wall milliseconds. Other scopes
remain projected SAT or model reuse; no protocol counterexample is claimed.

## T3

| Law | Base + actual pool goods | Query wall | Counted units | Pool core |
|---|---:|---:|---:|---|
| Inv* | 29 + 91 | 15.664 ms | 17.389 | 54, `range$1`, `r$0 <= 0` |
| Inv2973 | 38 + **289** | 26.290 ms | 46.582 | 190, `range$3`, `r$2 <= 0` |

Both refute well below the time limits, but using speculative zero-count
bounds against the negated target, not the anticipated R1/R2 core. Cheapness
is established; useful selection and source provability are not. These are
all-assumed numeric queries. The current `terms.length <= 5` pool actually
has 289 Inv2973 goods, not the design's 175. No cap was increased.

## Evidence and reproduction

- `t2-t3.log`: literal filtering and all-assumed queries.
- `t2-hygiene.log`: explicit hygiene controls.
- `demand-results.json`: reduced data with original IDs and all source attempts.
- `literal-placement.json`, `placement.json`: same VM, exclusive, eight CPUs.

Mount `canonical-capture-v1/fixtures` at `replay-input` and the v7 run at
`v7-input`. Run `jobs-section7-demand-measurements.json` with `--timing
--vm-type large --max-vms 1`; also export `LAB_SECTION7_CLEAN_WITNESSES=1`
for the hygienic variant. `jobs-section7-refined.json` contains its exact job.
Raw `closure-source.ms` / `closure-final.total` are counted work; `wallMs`
is elapsed time. Preliminary static setup failures are not scientific outcomes.

The failed T1 implementation condition remains in force.
