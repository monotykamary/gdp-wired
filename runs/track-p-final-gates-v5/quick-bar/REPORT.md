# The bar: 699b5160938737deb7776a65858617e19a1fc13f (699b51609387) against 40693c7a2e9adcae77c6558dedb8278bd5704ce7 (40693c7a2e9a)

Quick mode (each benchmark's dev set, gates/bar-dev.json); backend boat; the base from the shared baseline (3 runs, /Users/monotykamary/VCS/working-remote/open-source/gdp-wired/runs/bar/base/40693c7a2e9a-boat-r1), except onecpu and g332 (always together); 3 rerun(s) a side of every task that differs. Started 2026-11-07T21:47:56.958Z.

## CHC-COMP LIA-Lin (dev set: 662 tasks)

| side | solved | sat | unsat | wrong | disputed | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 521 | 373 | 148 | 0 | 1 | 140 | 0 | 0 | 662 |
| base run 1 | 520 | 373 | 147 | 0 | 1 | 140 | 1 | 0 | 662 |
| base run 2 | 519 | 371 | 148 | 0 | 1 | 142 | 0 | 0 | 662 |
| base run 3 | 519 | 370 | 149 | 0 | 1 | 142 | 0 | 0 | 662 |
| base mean | 519.33 | 371.33 | 148 | 0 | 1 | 141.33 | 0.33 | 0 | 662 |
| delta (candidate - base mean) | +1.67 | +1.67 | 0 | 0 | 0 | -1.33 | -0.33 | 0 | 0 |

- 13 differ in the first pass (6 solved by the candidate only, 7 by the base only; 2 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 3** (0 in every run against none), **lost 4** (0 solid), noise 6, wrong 0; answered only past 45 s in some run (a flip at the time limit): 3 of the gained, 3 of the lost.
- Predicted full-set delta from the dev set: -1.9 (raw -1 on 662 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| vmt-chc-benchmarks/lustre/DRAGON_5_e7_2017_e8_4841_000.yml | gained | 3/4 | 3/6 | yes | sat 39.3, sat 43.8, unknown 59.1, sat 57.6 / sat 37, unknown 58.7, unknown 58.2, sat 57.1, sat 58, unknown 58.6 |
| vmt-chc-benchmarks/lustre/durationThm_3_e3_442_e6_113_000.yml | gained | 3/4 | 3/6 | yes | unknown 58.6, sat 11.2, sat 53.1, sat 58.5 / sat 56.7, sat 14, unknown 58.6, unknown 58.6, unknown 58.6, sat 49.7 |
| vmt-chc-benchmarks/lustre/MESI_i3_e1_447_e1_1292_000_001.yml | gained | 3/4 | 3/6 | yes | sat 34, sat 57.6, sat 42.3, unknown 58.1 / unknown 58.1, unknown 58.1, sat 50.7, unknown 58.1, sat 46.4, sat 57.5 |
| vmt-chc-benchmarks/ctigar/dillig05.c_000.yml | lost | 2/4 | 6/6 | yes | unknown 58.1, sat 48.3, unknown 58.1, sat 54.9 / sat 54.7, sat 53.8, sat 44.8, sat 55.7, sat 55.2, sat 39.8 |
| vmt-chc-benchmarks/ctigar/dillig17.c_000.yml | lost | 2/4 | 4/6 |  | sat 29.8, unknown 58.1, sat 26.4, unknown 58.1 / sat 34.5, unknown 58.1, unknown 58.1, sat 16, sat 24, sat 42.3 |
| vmt-chc-benchmarks/lustre/DRAGON_13_e7_2336_e8_1940_000.yml | lost | 2/4 | 5/6 | yes | unknown 58.1, unknown 58.7, sat 58.2, sat 58.5 / unknown 58.6, sat 51.8, sat 49.3, sat 58.2, sat 57, sat 56.1 |
| vmt-chc-benchmarks/lustre/FIREFLY_rt_e3_1770_e2_637_000_001.yml | lost | 2/4 | 5/6 | yes | unknown 58.1, sat 41.8, unknown 59.1, sat 52 / unknown 58.1, sat 37.2, sat 57.5, sat 55.1, sat 56.9, sat 41.4 |

## TermComp ITS, the task's statement (gdp) (dev set: 398 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 365 | 260 | 105 | 0 | 28 | 4 | 1 | 398 |
| base run 1 | 366 | 260 | 106 | 0 | 25 | 6 | 1 | 398 |
| base run 2 | 366 | 260 | 106 | 0 | 25 | 6 | 1 | 398 |
| base run 3 | 365 | 261 | 104 | 0 | 27 | 4 | 2 | 398 |
| base mean | 365.67 | 260.33 | 105.33 | 0 | 25.67 | 5.33 | 1.33 | 398 |
| delta (candidate - base mean) | -0.67 | -0.33 | -0.33 | 0 | +2.33 | -1.33 | -0.33 | 0 |

- 2 differ in the first pass (0 solved by the candidate only, 2 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 0** (0 in every run against none), **lost 1** (0 solid), noise 1, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: -5.1 (raw -2 on 398 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| Integer_Transition_Systems/From_T2/hqr.c.i.hqr.pl.t2.nor.t2.rlgfixed.t2_fixed.ari | lost | 2/4 | 4/6 |  | unknown 58.1, unknown 58.1, nonterminating 41.7, nonterminating 41 / nonterminating 41.4, nonterminating 41.6, unknown 58.1, nonterminating 39.6, unknown 58.5, nonterminating 40.8 |

## TermComp ITS, per component (gdp-scc) (dev set: 398 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 362 | 257 | 105 | 0 | 33 | 3 | 0 | 398 |
| base run 1 | 362 | 257 | 105 | 0 | 33 | 2 | 1 | 398 |
| base run 2 | 362 | 257 | 105 | 0 | 33 | 2 | 1 | 398 |
| base run 3 | 363 | 258 | 105 | 0 | 31 | 3 | 1 | 398 |
| base mean | 362.33 | 257.33 | 105 | 0 | 32.33 | 2.33 | 1 | 398 |
| delta (candidate - base mean) | -0.33 | -0.33 | 0 | 0 | +0.67 | +0.67 | -1 | 0 |

- 2 differ in the first pass (1 solved by the candidate only, 1 by the base only; 2 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 2, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 122 tasks; calibration in gates/README.md).

## SV-COMP termination (gdp) (dev set: 129 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 111 | 92 | 19 | 0 | 15 | 0 | 0 | 129 |
| base run 1 | 110 | 91 | 19 | 0 | 16 | 0 | 0 | 129 |
| base run 2 | 111 | 92 | 19 | 0 | 15 | 0 | 0 | 129 |
| base run 3 | 111 | 92 | 19 | 0 | 15 | 0 | 0 | 129 |
| base mean | 110.67 | 91.67 | 19 | 0 | 15.33 | 0 | 0 | 129 |
| delta (candidate - base mean) | +0.33 | +0.33 | 0 | 0 | -0.33 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 129 tasks; calibration in gates/README.md).

## SV-COMP termination, per component (gdp-scc) (dev set: 129 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 97 | 78 | 19 | 0 | 27 | 2 | 0 | 129 |
| base run 1 | 97 | 78 | 19 | 0 | 28 | 1 | 0 | 129 |
| base run 2 | 97 | 78 | 19 | 0 | 28 | 1 | 0 | 129 |
| base run 3 | 97 | 78 | 19 | 0 | 27 | 2 | 0 | 129 |
| base mean | 97 | 78 | 19 | 0 | 27.67 | 1.33 | 0 | 129 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | -0.67 | +0.67 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 43 tasks; calibration in gates/README.md).

## TIP 2015 (gdp) (dev set: 239 tasks)

| side | proven | refuted | wrong | unknown | timeout | unsupported | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 105 | 6 | 0 | 79 | 41 | 7 | 1 | 239 |
| base run 1 | 105 | 6 | 0 | 75 | 45 | 7 | 1 | 239 |
| base run 2 | 105 | 6 | 0 | 80 | 40 | 7 | 1 | 239 |
| base run 3 | 105 | 6 | 0 | 78 | 42 | 7 | 1 | 239 |
| base mean | 105 | 6 | 0 | 77.67 | 42.33 | 7 | 1 | 239 |
| delta (candidate - base mean) | 0 | 0 | 0 | +1.33 | -1.33 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 239 tasks; calibration in gates/README.md).

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
| candidate | 25 | 33 | 31 | 31 | 0 | 1 |
| base run 1 | 25 | 33 | 31 | 31 | 0 | 1 |
| base run 2 | 25 | 33 | 31 | 31 | 0 | 1 |
| base run 3 | 25 | 33 | 31 | 31 | 0 | 2 |
| base mean | 25 | 33 | 31 | 31 | 0 | 1.33 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | -0.33 |

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
| candidate | 332 | 332 | 216.3 |
| base run 1 | 332 | 332 | 243.9 |
| delta (candidate - base mean) | 0 | 0 | -27.6 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 55 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 41.25 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.

- The same search (outcome, leaves, splits, CDCL's decisions, conflicts and nodes) on 332 of 332 goals (699b51609387 against 40693c7a2e9a); search ms summed 216,260 against 243,946; candidate/base per goal p10 0.545, p50 0.945, p90 1.562.

## The 5 s-limited tests on 1 vCPU

Failed jobs: candidate none; base none. The ten slowest tests by their most on either side:

| test | candidate median ms | candidate most ms | base median ms | base most ms | runs |
| --- | --- | --- | --- | --- | --- |
| data | definitions that do not terminate, made to look as if they do (rings, a size law true of short lists only, a guard past the runs' values), are refused with the measures tried | 45,918.44 | 61,816.96 | 41,415.7 | 95,387.76 | 3 / 3 |
| data | nested recursion (well-founded, a call in another's argument): taken with an invariant of the function, proven with each decrease; its obligations as Nested.lean states them | 12,923.26 | 20,432.64 | 10,596.7 | 26,425.45 | 3 / 3 |
| data | a ring of functions that is not structural recursion: a measure each (one length), each call within the ring proven to lower the callee's below the caller's | 9,776.94 | 15,913.97 | 7,038.37 | 21,513.59 | 3 / 3 |
| data | halves and a merge over the user's ≤: taken by size laws proven by induction on both halves at once, and by cases on the user's ≤ | 6,823.67 | 8,081.11 | 4,797.96 | 8,908.62 | 3 / 3 |
| infer | an invariant over four values (the join: the samples' hull, made inductive): one account within the total paid in | 4,314.24 | 4,832.7 | 4,394.57 | 4,972.88 | 3 / 3 |
| data | a function that agrees with + on small values only: its bridge is not proven, and nothing false is proven through it | 2,152.2 | 3,119.3 | 2,067.15 | 4,814.84 | 3 / 3 |
| infer | a law that needs an invariant: not proven alone, proven with what the search finds, and the set checks | 3,278.54 | 3,866.17 | 3,090.9 | 4,174.32 | 3 / 3 |
| data | well-founded recursion: a measure found, and each call proven to lower it (every obligation checked by the kernel) | 2,001.49 | 2,159.12 | 959.52 | 3,670.57 | 3 / 3 |
| data | a function of three naturals that computes their sum (add3acc, by well-founded recursion): its bridge proven by its own recursion, a law read through it; one that agrees with a sum on small values only is not proven to | 1,540.49 | 1,881.79 | 1,222.26 | 3,216.95 | 3 / 3 |
| infer | what was found reads as the builder call that states it, and that call, written out, proves the law again | 2,001.99 | 2,293.79 | 2,260.35 | 3,060.43 | 3 / 3 |

## Lean: recurrent sets of the ITS run checked again

| side | checked | sampled | max_s |
| --- | --- | --- | --- |
| candidate | 6 | 6 | 69.92 |

- 6 of 6 checked by Lean, at most 69.92 s a file.

## Size

core/ and kernel/ (.ts, tests excluded): 4,432,252 bytes and 56,956 lines, against 4,281,925 and 55,036 (+150,327 bytes, +1,920 lines).

## Wall time and spend

- Wall: 4,093 s.
- Modal, billed for this bar's own 0 apps: $0 (`modal billing report --start 2026-11-07 --resolution h --json`, complete hours only: the last reported starts 2026-11-07T11:00:00Z); estimated from the task seconds: $2.67. `bun gates/bar.ts spend /Users/monotykamary/VCS/working-remote/open-source/gdp-wired/runs/bar/runs/track-p-final-699b5160` reads the bill again once the hours are over.
- Where the jobs ran (each launch's backends.json): {"boat":663}; {"boat":14}; {"boat":798}; {"boat":6}; {"boat":260}; {"boat":240}; {"boat":93}; {"boat":128}; {"boat":91}; {"boat":332}.

