# I6 causal controls: accounting, not a persistent proof failure

**Exact source:** `1066f26766d6bfd628c8ef9de92bc626357b01c1`.
**Policy:** unchanged `raw-work-v1`; `core/work-profile.ts` blob `5aac97e8b1693fabf5b932d828f2020f0df67674`, identical to `00b58ee5`. New three prices remain 1. No quota, price or production source was changed for these controls.

## Experiment

Batch `20261111-043016-735zv7`, ten fresh native processes: each case with writers on/off at 15M and 1e12, plus a 1e12 shadow control. All controls use the same archived source, original model and flags (`GDP_WORK_FULL=1`, `GDP_WORK_STEPS=0`, count strategies/tiers/frames on). The writer switches are disposable property descriptors on only `tableCells`, `checkSteps`, `cubeTests`; no checker implementation is replaced. In shadow mode all actual new increments are retained separately while only the old projection drives the clock. This is a **diagnostic ablation, not a candidate configuration or calibration**.

All 10 receipts have exact hash/source checks and zero forbidden wall reads. Writer-on 15M exactly reproduces the strict census's search vectors, weighted units and verdicts. Corrected independent audit: `20261111-043754-faalze`, pass. Full old/new vectors, query snapshots, phase ledgers, bound crossings and compressed results remain under `results/ablation/`. The exact executed harnesses are saved as `.source` files under `results/ablation-inputs/`.

## Results (raw weighted units; prices still provisional)

| Case / mode | Allowance | Verdict | Old-column units | New-column units | Actual total |
|---|---:|---|---:|---:|---:|
| client_server_ae, on | 15M | unknown, outer preflight budget | 14,009,729.1800 | 990,319 | 15,000,048.1800 |
| client_server_ae, off | 15M | proved + checked | 2,355,979.8243 | 0 | 2,355,979.8243 |
| client_server_ae, on | 1e12 | proved + checked | 179,165,599.8638 | 75,704,316 | 254,869,915.8638 |
| client_server_ae, off | 1e12 | proved + checked | 2,355,979.8243 | 0 | 2,355,979.8243 |
| client_server_ae, shadow | 1e12 | proved + checked | 2,355,979.8243 | 17,594,587 | 19,950,566.8243 |
| simple_election, on | 15M | unknown, local focused budget | 3,571,101.1798 | 1,271,381 | 4,842,482.1798 |
| simple_election, off | 15M | proved + checked | 3,924,296.2794 | 0 | 3,924,296.2794 |
| simple_election, on | 1e12 | proved + checked | 3,761,609.1320 | 3,014,572 | 6,776,181.1320 |
| simple_election, off | 1e12 | proved + checked | 3,924,296.2794 | 0 | 3,924,296.2794 |
| simple_election, shadow | 1e12 | proved + checked | 3,924,296.2794 | 2,874,503 | 6,798,799.2794 |

For both cases, shadow and off have **identical old 23-column vectors and normalized returned results** at 1e12. Keeping every new increment while restoring the old stopping clock restores the old path. With the new clock at 1e12, both cases still prove and check. `simple_election` returns the same normalized result; `client_server_ae` takes a different, much more expensive successful route and returns additional found laws. We do not claim identical search traces after budget boundaries have changed.

## Which bound binds?

`simple_election`: the last captured local crossing has clock 19,369.5195592 against deadline 19,369.41106276, while the outer endpoint remains 60,000.052. At `fullRate=250` and after subtracting the fixed 13-unit initial offset, the local endpoint is **4,842,339.76569** search units. At that crossing the old projection is only **3,571,070.8898**, and newly observed work is **1,271,296**. Thus the old projection is still below the local endpoint. The final result stops at 4,842,482.1798; it has not exhausted 15M. The focus endpoint is formed in `core/counts.ts:708,979` by `min(attemptEnd, clock()+min(ms,5000))`; `core/count-focus-proof.ts` checks and propagates it. The same old path with new work recorded totals only 6.7988M, so the local share, not outer W, explains this case.

`client_server_ae`: two earlier local crossings also have old-only work below their endpoints (2,125,325.0137 < 2,600,033.94, and 3,736,717.0725 < 4,700,133.4704). Those failures change the route; the final result then hits the outer 15M preflight guard. Its old successful route now measures **19.9506M** with all new work included, above 15M. We do not describe the expensive lifted-cap route as a 15M success.

## Decision and limits

The tested evidence supports cause **(a), previously uncharged work consuming existing shares**, not cause **(b), a persistent checker/search failure independent of accounting**. This is not merely a decomposition argument: shadow equality, writer-off restoration, exact on-census reproduction and successful on/lifted proofs are the controls.

No charge has been suppressed in production; no subshare or price has been retuned. The 15M bounded verdict changes remain real. The separate `sharded_kv` 120,328.2561-unit overrun is still open, so the old 1,024-unit global slack is NOT claimed for I6. D remains the authority for observer admission, final source/weight binding and calibration.

Initial audit presentation used an incorrect clock-to-unit multiplier; its underlying receipt/equivalence assertions passed, but its derived endpoint display must not be cited. The corrected audit uses the exact `fullRate=250` source constant and initial offset, and is preserved separately. The current reusable monitor also guards pre-budget clock snapshots; that defensive guard is not in the saved executed harness and was not needed by these ten zero-read runs.
