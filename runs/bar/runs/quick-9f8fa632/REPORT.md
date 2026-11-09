# The bar: 9f8fa6328041646f7353dc4817ea5d06b604f15f (9f8fa6328041) against b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c (b788e1959bba)

Quick mode (each benchmark's dev set, gates/bar-dev.json); backend boat; the base launched together, except onecpu and g332 (always together); 3 rerun(s) a side of every task that differs. Started 2026-11-09T19:40:55.511Z.

## CHC-COMP LIA-Lin (dev set: 662 tasks)

| side | solved | sat | unsat | wrong | disputed | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 525 | 377 | 148 | 0 | 1 | 136 | 0 | 0 | 662 |
| base run 1 | 523 | 375 | 148 | 0 | 1 | 138 | 0 | 0 | 662 |
| delta (candidate - base mean) | +2 | +2 | 0 | 0 | 0 | -2 | 0 | 0 | 0 |

- 18 differ in the first pass (10 solved by the candidate only, 8 by the base only; 13 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 2** (0 in every run against none), **lost 5** (0 solid), noise 11, wrong 0; answered only past 45 s in some run (a flip at the time limit): 2 of the gained, 5 of the lost.
- Predicted full-set delta from the dev set: +6.1 (raw +2 on 662 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| vmt-chc-benchmarks/lustre/cd_000_001.yml | gained | 3/4 | 2/4 | yes | sat 50.7, sat 51.1, sat 48.5, unknown 58.1 / unknown 58.1, sat 39.3, unknown 58.2, sat 46.5 |
| vmt-chc-benchmarks/lustre/FIREFLY_luke_2_000_001.yml | gained | 3/4 | 2/4 | yes | sat 36.1, unknown 58.1, sat 26.3, sat 40.8 / unknown 58.2, sat 51.7, unknown 58.6, sat 40 |
| eldarica-misc/LIA/HOLA/12.c_000.yml | lost | 1/4 | 4/4 | yes | unknown 58.6, unknown 58.6, sat 44, unknown 58.6 / sat 46.7, sat 49.7, sat 46.8, sat 44.8 |
| vmt-chc-benchmarks/lustre/DRAGON_13_e3_1418_e3_2761_000_001.yml | lost | 1/4 | 3/4 | yes | unknown 58.1, sat 57.2, unknown 58.7, unknown 58.6 / sat 56.9, unknown 58.6, sat 57.5, sat 58.2 |
| vmt-chc-benchmarks/lustre/DRAGON_13_e7_2336_e8_1940_000.yml | lost | 0/4 | 3/4 | yes | unknown 58.1, unknown 58.1, unknown 58.2, unknown 58.1 / sat 57.3, sat 45.4, sat 50.8, unknown 58.1 |
| vmt-chc-benchmarks/lustre/DRAGON_5_e2_3018_e2_936_000_001.yml | lost | 2/4 | 3/4 | yes | sat 45.8, sat 49.5, unknown 58.7, unknown 58.7 / unknown 58.9, sat 36.5, sat 55.6, sat 43.4 |
| vmt-chc-benchmarks/lustre/DRAGON_5_e7_2017_e8_4841_000.yml | lost | 2/4 | 3/4 | yes | sat 51.2, unknown 58.1, sat 31.3, unknown 58.1 / unknown 58.6, sat 37.9, sat 54.4, sat 55 |

## TermComp ITS, the task's statement (gdp) (dev set: 398 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 364 | 259 | 105 | 0 | 28 | 6 | 0 | 398 |
| base run 1 | 364 | 259 | 105 | 0 | 29 | 5 | 0 | 398 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | -1 | +1 | 0 | 0 |

- 6 differ in the first pass (4 solved by the candidate only, 2 by the base only; 5 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 0** (0 in every run against none), **lost 1** (0 solid), noise 5, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 1 of the lost.
- Predicted full-set delta from the dev set: -0 (raw 0 on 398 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| Integer_Transition_Systems/From_T2/slayer-3.t2_fixed.ari | lost | 2/4 | 3/4 | yes | unknown 58.2, nonterminating 44.6, nonterminating 47.5, unknown 58.1 / nonterminating 47.7, nonterminating 50.5, nonterminating 46, unknown 58.1 |

## TermComp ITS, per component (gdp-scc) (dev set: 398 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 361 | 255 | 106 | 0 | 34 | 2 | 1 | 398 |
| base run 1 | 362 | 257 | 105 | 0 | 34 | 1 | 1 | 398 |
| delta (candidate - base mean) | -1 | -2 | +1 | 0 | 0 | +1 | 0 | 0 |

- 6 differ in the first pass (4 solved by the candidate only, 2 by the base only; 4 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 1** (0 in every run against none), **lost 1** (0 solid), noise 4, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: -3.3 (raw -1 on 122 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| Integer_Transition_Systems/From_T2/hqr.c.i.hqr.pl.t2.nor.t2.rlgfixed.t2_fixed.ari | gained | 3/4 | 2/4 |  | nonterminating 26.5, nonterminating 26.7, unknown 58.1, nonterminating 25.9 / unknown 58.1, nonterminating 25.5, unknown 58.1, nonterminating 25.8 |
| Integer_Transition_Systems/From_T2/slayer-n3-filtered.t2.ari | lost | 1/4 | 3/4 |  | unknown 58.1, unknown 58.1, unknown 58.1, terminates 9.1 / terminates 10.5, terminates 9.7, unknown 58.1, terminates 11 |

## SV-COMP termination (gdp) (dev set: 129 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 111 | 92 | 19 | 0 | 15 | 0 | 0 | 129 |
| base run 1 | 110 | 91 | 19 | 0 | 16 | 0 | 0 | 129 |
| delta (candidate - base mean) | +1 | +1 | 0 | 0 | -1 | 0 | 0 | 0 |

- 1 differ in the first pass (1 solved by the candidate only, 0 by the base only; 1 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 1, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: +1 (raw +1 on 129 tasks; calibration in gates/README.md).

## SV-COMP termination, per component (gdp-scc) (dev set: 129 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 97 | 78 | 19 | 0 | 27 | 2 | 0 | 129 |
| base run 1 | 97 | 78 | 19 | 0 | 27 | 2 | 0 | 129 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

- 1 differ in the first pass (1 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 1, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 43 tasks; calibration in gates/README.md).

## TIP 2015 (gdp) (dev set: 239 tasks)

| side | proven | refuted | wrong | unknown | timeout | unsupported | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 105 | 6 | 0 | 85 | 35 | 7 | 1 | 239 |
| base run 1 | 105 | 6 | 0 | 79 | 41 | 7 | 1 | 239 |
| delta (candidate - base mean) | 0 | 0 | 0 | +6 | -6 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 239 tasks; calibration in gates/README.md).

## Frontier corpus, round 1 (dev set: 48 tasks)

| side | proven | laws | refused | broken | wrong | timeout |
| --- | --- | --- | --- | --- | --- | --- |
| candidate | 34 | 35 | 13 | 13 | 0 | 0 |
| base run 1 | 34 | 35 | 13 | 13 | 0 | 0 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 48 tasks; calibration in gates/README.md).

## Frontier corpus, round 2 (dev set: 64 tasks)

| side | proven | laws | refused | broken | wrong | timeout |
| --- | --- | --- | --- | --- | --- | --- |
| candidate | 25 | 33 | 31 | 31 | 0 | 1 |
| base run 1 | 25 | 33 | 31 | 31 | 0 | 1 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 64 tasks; calibration in gates/README.md).

## The real-world corpus (dev set: 91 tasks)

| side | proven | refuted | unknown | timeout | laws |
| --- | --- | --- | --- | --- | --- |
| candidate | 74 | 14 | 3 | 0 | 91 |
| base run 1 | 74 | 14 | 3 | 0 | 91 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 91 tasks; calibration in gates/README.md).

## research/dag's 332 step goals

| side | proven | goals | search_s |
| --- | --- | --- | --- |
| candidate | 332 | 332 | 249.4 |
| base run 1 | 332 | 332 | 222.4 |
| delta (candidate - base mean) | 0 | 0 | +27 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 55 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 41.25 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.

- The same search (outcome, leaves, splits, CDCL's decisions, conflicts and nodes) on 332 of 332 goals (9f8fa6328041 against b788e1959bba); search ms summed 249,361 against 222,446; candidate/base per goal p10 0.606, p50 1.123, p90 2.250.

## The 5 s-limited tests on 1 vCPU

Failed jobs: candidate none; base none. The ten slowest tests by their most on either side:

| test | candidate median ms | candidate most ms | base median ms | base most ms | runs |
| --- | --- | --- | --- | --- | --- |
| data | definitions that do not terminate, made to look as if they do (rings, a size law true of short lists only, a guard past the runs' values), are refused with the measures tried | 31,708.68 | 39,364.64 | 38,326.15 | 41,012.74 | 3 / 3 |
| data | nested recursion (well-founded, a call in another's argument): taken with an invariant of the function, proven with each decrease; its obligations as Nested.lean states them | 8,181.51 | 8,214.8 | 8,054.65 | 10,301.46 | 3 / 3 |
| data | a ring of functions that is not structural recursion: a measure each (one length), each call within the ring proven to lower the callee's below the caller's | 5,497.17 | 6,119.92 | 6,233.5 | 7,245.11 | 3 / 3 |
| infer | an invariant over four values (the join: the samples' hull, made inductive): one account within the total paid in | 2,739.46 | 2,832.14 | 3,012.47 | 4,616.54 | 3 / 3 |
| data | halves and a merge over the user's ≤: taken by size laws proven by induction on both halves at once, and by cases on the user's ≤ | 3,230.5 | 3,350.01 | 2,973.31 | 3,761.73 | 3 / 3 |
| infer | a law that needs an invariant: not proven alone, proven with what the search finds, and the set checks | 2,362.31 | 2,506.11 | 2,320.98 | 2,721.66 | 3 / 3 |
| data | a function that agrees with + on small values only: its bridge is not proven, and nothing false is proven through it | 1,777.5 | 2,558.5 | 1,870 | 1,964 | 3 / 3 |
| infer | what was found reads as the builder call that states it, and that call, written out, proves the law again | 1,322.39 | 1,702.68 | 1,466.86 | 2,215.8 | 3 / 3 |
| infer | a machine with no rule: the in-flight bound needs s + 50·p <= b + 150 or tighter | 1,115.89 | 1,164.85 | 1,473.58 | 1,838.39 | 3 / 3 |
| data | a function of three naturals that computes their sum (add3acc, by well-founded recursion): its bridge proven by its own recursion, a law read through it; one that agrees with a sum on small values only is not proven to | 1,025.19 | 1,475.25 | 1,107.62 | 1,178.43 | 3 / 3 |

## Lean: recurrent sets of the ITS run checked again

| side | checked | sampled | max_s |
| --- | --- | --- | --- |
| candidate | 6 | 6 | 7.75 |

- 6 of 6 checked by Lean, at most 7.75 s a file.

## Size

core/ and kernel/ (.ts, tests excluded): 4,495,441 bytes and 57,888 lines, against 4,454,642 and 57,314 (+40,799 bytes, +574 lines).

## Wall time and spend

- Wall: 2,141 s.
- Modal, billed for this bar's own 0 apps: $0 (`modal billing report --start 2026-11-09 --resolution h --json`, complete hours only: the last reported starts 2026-11-09T16:00:00Z); estimated from the task seconds: $5.06. `bun gates/bar.ts spend /Users/monotykamary/VCS/working-remote/open-source/gdp-wired-ci/runs/bar/runs/quick-9f8fa632` reads the bill again once the hours are over.
- Where the jobs ran (each launch's backends.json): {"boat":663}; {"boat":19}; {"boat":798}; {"boat":14}; {"boat":260}; {"boat":4}; {"boat":240}; {"boat":93}; {"boat":128}; {"boat":91}; {"boat":332}; {"boat":6}.

