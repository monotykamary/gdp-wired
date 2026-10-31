# The bar: gen/laneB (8a889b12b159) against ae36917 (ae369178e65d)

Quick mode (each benchmark's dev set, gates/bar-dev.json); backend modal; the base from the shared baseline (3 runs, runs/bar/base/ae369178e65d-modal-r1), except onecpu and g332 (always together); 3 rerun(s) a side of every task that differs. Started 2026-10-30T17:12:44.402Z.

## Frontier corpus, round 1 (dev set: 48 tasks)

| side | proven | laws | refused | broken | wrong | timeout |
| --- | --- | --- | --- | --- | --- | --- |
| candidate | 34 | 35 | 13 | 13 | 0 | 0 |
| base run 1 | 34 | 35 | 13 | 13 | 0 | 0 |
| base run 2 | 34 | 35 | 13 | 13 | 0 | 0 |
| base run 3 | 34 | 35 | 13 | 13 | 0 | 0 |
| base mean | 34 | 35 | 13 | 13 | 0 | 0 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 48 tasks; calibration in gates/README.md).

## Frontier corpus, round 2 (dev set: 64 tasks)

| side | proven | laws | refused | broken | wrong | timeout |
| --- | --- | --- | --- | --- | --- | --- |
| candidate | 24 | 33 | 31 | 31 | 0 | 1 |
| base run 1 | 24 | 33 | 31 | 31 | 0 | 1 |
| base run 2 | 24 | 33 | 31 | 31 | 0 | 1 |
| base run 3 | 24 | 33 | 31 | 31 | 0 | 1 |
| base mean | 24 | 33 | 31 | 31 | 0 | 1 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 64 tasks; calibration in gates/README.md).

## The real-world corpus (dev set: 91 tasks)

| side | proven | refuted | unknown | timeout | laws |
| --- | --- | --- | --- | --- | --- |
| candidate | 74 | 14 | 3 | 0 | 91 |
| base run 1 | 74 | 14 | 3 | 0 | 91 |
| base run 2 | 74 | 14 | 3 | 0 | 91 |
| base run 3 | 74 | 14 | 3 | 0 | 91 |
| base mean | 74 | 14 | 3 | 0 | 91 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 91 tasks; calibration in gates/README.md).

## research/dag's 332 step goals

| side | proven | goals | search_s |
| --- | --- | --- | --- |
| candidate | 332 | 332 | 283.2 |
| base run 1 | 332 | 332 | 283.4 |
| delta (candidate - base mean) | 0 | 0 | -0.2 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 55 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 41.25 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.

- The same search (outcome, leaves, splits, CDCL's decisions, conflicts and nodes) on 332 of 332 goals (8a889b12b159 against ae369178e65d); search ms summed 283,165 against 283,412; candidate/base per goal p10 0.727, p50 1.016, p90 1.354.

## The suite, by default

| side | passed | failed | jobs | job_s |
| --- | --- | --- | --- | --- |
| candidate | 235 | 0 | 235 | 6,271.7 |
| base run 1 | 235 | 0 | 235 | 6,431.3 |
| base run 2 | 235 | 0 | 235 | 6,113.5 |
| base run 3 | 235 | 0 | 235 | 6,165.4 |
| base mean | 235 | 0 | 235 | 6,236.73 |
| delta (candidate - base mean) | 0 | 0 | 0 | +34.97 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 900 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 675 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.

- Failed on the candidate: none.

## The 5 s-limited tests on 1 vCPU

Failed jobs: candidate none; base none. The ten slowest tests by their most on either side:

| test | candidate median ms | candidate most ms | base median ms | base most ms | runs |
| --- | --- | --- | --- | --- | --- |
| data | definitions that do not terminate, made to look as if they do (rings, a size law true of short lists only, a guard past the runs' values), are refused with the measures tried | 44,310.82 | 47,741.67 | 43,733.19 | 49,202.57 | 3 / 3 |
| infer | an invariant over four values (the join: the samples' hull, made inductive): one account within the total paid in | 5,884.37 | 6,676.31 | 6,634.7 | 6,820.12 | 3 / 3 |
| data | a ring of functions that is not structural recursion: a measure each (one length), each call within the ring proven to lower the callee's below the caller's | 4,732.27 | 5,908.23 | 4,479.62 | 5,670.47 | 3 / 3 |
| data | well-founded recursion: a measure found, and each call proven to lower it (every obligation checked by the kernel) | 3,925.11 | 5,050.14 | 4,451.02 | 4,535.71 | 3 / 3 |
| infer | a law that needs an invariant: not proven alone, proven with what the search finds, and the set checks | 3,273.4 | 3,959.01 | 3,328.67 | 3,693.04 | 3 / 3 |
| data | a function that agrees with + on small values only: its bridge is not proven, and nothing false is proven through it | 2,680.84 | 2,759.17 | 2,507.43 | 2,725.92 | 3 / 3 |
| infer | what was found reads as the builder call that states it, and that call, written out, proves the law again | 2,409.03 | 2,549.75 | 2,479.2 | 2,722.92 | 3 / 3 |
| data | a function of three naturals that computes their sum (add3acc, by well-founded recursion): its bridge proven by its own recursion, a law read through it; one that agrees with a sum on small values only is not proven to | 1,968.75 | 2,183.44 | 1,915.47 | 2,016.49 | 3 / 3 |
| data | a function that agrees with x + 1 on small values only, read inside a larger law: its bridge is tried and not proven, and nothing false is proven through it | 2,033.57 | 2,036.83 | 1,970.21 | 2,114.82 | 3 / 3 |
| data | laws with no lemma: proven, and checked by the kernel | 1,359.32 | 1,837.55 | 1,343.06 | 1,415.4 | 3 / 3 |

## Size

core/ and kernel/ (.ts, tests excluded): 3,132,255 bytes and 41,677 lines, against 3,108,310 and 41,366 (+23,945 bytes, +311 lines).

## Wall time and spend

- Wall: 532 s.
- Modal, billed for this bar's own 12 apps: $0 (`modal billing report --start 2026-10-30 --resolution h --json`, complete hours only: the last reported starts 2026-10-30T16:00:00Z); estimated from the task seconds: $0.59. `bun gates/bar.ts spend runs/bar/runs/8a889b12b159-vs-ae369178e65d-quick-2026-10-301712` reads the bill again once the hours are over.
- Where the jobs ran (each launch's backends.json): {"modal":93}; {"modal":128}; {"modal":91}; {"modal":235}; {"modal":6}.

