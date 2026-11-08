# The bar: 0e9afc3d (0e9afc3db231) against 8610af26 (8610af26c16c)

Quick mode (each benchmark's dev set, gates/bar-dev.json); backend boat; the base launched together, except onecpu and g332 (always together); 3 rerun(s) a side of every task that differs. Started 2026-11-08T06:54:00.763Z.

## CHC-COMP LIA-Lin (dev set: 662 tasks)

| side | solved | sat | unsat | wrong | disputed | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 524 | 375 | 149 | 0 | 1 | 136 | 1 | 0 | 662 |
| base run 1 | 523 | 375 | 148 | 0 | 1 | 138 | 0 | 0 | 662 |
| delta (candidate - base mean) | +1 | 0 | +1 | 0 | 0 | -2 | +1 | 0 | 0 |

- 23 differ in the first pass (12 solved by the candidate only, 11 by the base only; 14 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 4** (0 in every run against none), **lost 5** (0 solid), noise 14, wrong 0; answered only past 45 s in some run (a flip at the time limit): 2 of the gained, 5 of the lost.
- Predicted full-set delta from the dev set: +3.8 (raw +1 on 662 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| vmt-chc-benchmarks/lustre/FIREFLY_11_000_001.yml | gained | 4/4 | 2/4 | yes | sat 39.7, sat 25.2, sat 43.4, sat 49.4 / unknown 58.7, unknown 58.1, sat 33.2, sat 49.9 |
| vmt-chc-benchmarks/lustre/FIREFLY_luke_2_000_001.yml | gained | 3/4 | 0/4 |  | sat 39.8, sat 35.3, sat 42.4, unknown 58.2 / unknown 58.7, unknown 58.7, unknown 58.7, unknown 58.2 |
| vmt-chc-benchmarks/lustre/MESI_i3_e1_447_e1_1292_000_001.yml | gained | 3/4 | 1/4 |  | sat 39.7, sat 44.4, sat 38.3, unknown 58.1 / unknown 58.1, unknown 58.1, sat 40.3, unknown 58.1 |
| vmt-chc-benchmarks/lustre/metros_3_e3_1275_e1_1350_000_001.yml | gained | 3/4 | 0/4 | yes | unsat 45.4, unsat 36.3, unsat 56.1, unknown 58.2 / unknown 58.1, unknown 58.1, unknown 58.1, unknown 58.1 |
| vmt-chc-benchmarks/ctigar/nest-len.c_000_001.yml | lost | 1/4 | 3/4 | yes | sat 38.3, unknown 58.1, unknown 58.2, unknown 58.2 / unknown 58.1, sat 53.8, sat 45.7, sat 51.6 |
| vmt-chc-benchmarks/ctigar/nested8.c_000_001.yml | lost | 2/4 | 3/4 | yes | sat 23.8, sat 32.1, unknown 58.1, unknown 58.1 / unknown 58.1, sat 23.9, sat 37.1, sat 57.6 |
| vmt-chc-benchmarks/ctigar/seesaw.c_000.yml | lost | 1/4 | 3/4 | yes | unknown 58.7, unknown 58.2, unknown 58.2, sat 53.1 / sat 47.4, sat 45.9, unknown 58.2, sat 54.3 |
| vmt-chc-benchmarks/lustre/DRAGON_13_e7_2336_e8_1940_000.yml | lost | 0/4 | 3/4 | yes | unknown 58.7, unknown 58.1, unknown 58.1, unknown 58.5 / sat 52, unknown 58.5, sat 46.3, sat 57.8 |
| vmt-chc-benchmarks/lustre/FIREFLY_luke_2_e7_1826_e8_126_000_001.yml | lost | 2/4 | 3/4 | yes | unknown 58.1, unknown 58.7, sat 37.9, sat 34.5 / sat 50.4, sat 35.6, sat 29.8, unknown 58.2 |

## TermComp ITS, the task's statement (gdp) (dev set: 398 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 363 | 258 | 105 | 0 | 27 | 6 | 2 | 398 |
| base run 1 | 360 | 258 | 102 | 0 | 32 | 5 | 1 | 398 |
| delta (candidate - base mean) | +3 | 0 | +3 | 0 | -5 | +1 | +1 | 0 |

- 10 differ in the first pass (7 solved by the candidate only, 3 by the base only; 8 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 3** (0 in every run against none), **lost 0** (0 solid), noise 7, wrong 0; answered only past 45 s in some run (a flip at the time limit): 1 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: +11.3 (raw +3 on 398 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| Integer_Transition_Systems/From_AProVE_2014/juLinkedListCreateRemoveFirstOccurrence.jar-obl-16.ari | gained | 4/4 | 2/4 | yes | terminates 47.3, terminates 38.3, terminates 34, terminates 58.1 / timeout 60.1, terminates 60.1, unknown 58.1, terminates 36.1 |
| Integer_Transition_Systems/From_T2/hqr.c.i.hqr.pl.t2.nor.t2.rlgfixed.t2_fixed.ari | gained | 3/4 | 2/4 |  | nonterminating 41.5, unknown 58.1, nonterminating 40, nonterminating 42.3 / unknown 58.1, nonterminating 41.4, nonterminating 41.2, unknown 58.1 |
| Integer_Transition_Systems/From_T2/slayer-3-new.t2.ari | gained | 3/4 | 1/4 |  | nonterminating 14.8, unknown 59, nonterminating 14.2, nonterminating 12.5 / unknown 58.2, nonterminating 15.1, unknown 58.3, unknown 58.1 |

## TermComp ITS, per component (gdp-scc) (dev set: 398 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 362 | 256 | 106 | 0 | 33 | 2 | 1 | 398 |
| base run 1 | 362 | 257 | 105 | 0 | 31 | 3 | 2 | 398 |
| delta (candidate - base mean) | 0 | -1 | +1 | 0 | +2 | -1 | -1 | 0 |

- 10 differ in the first pass (8 solved by the candidate only, 2 by the base only; 7 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 0** (0 in every run against none), **lost 2** (0 solid), noise 8, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 1 of the lost.
- Predicted full-set delta from the dev set: +0.1 (raw 0 on 122 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| Integer_Transition_Systems/From_AProVE_2014/RSA.jar-obl-17.ari | lost | 1/4 | 3/4 | yes | unknown 58.2, unknown 58.1, terminates 58.2, unknown 58.1 / terminates 58.1, terminates 59.2, unknown 58.1, terminates 60 |
| Integer_Transition_Systems/From_T2/slayer-n3-filtered.t2.ari | lost | 2/4 | 3/4 |  | unknown 58.1, terminates 8.7, terminates 9.8, unknown 58.1 / terminates 10.9, unknown 58.1, terminates 9, terminates 8.9 |

## SV-COMP termination (gdp) (dev set: 129 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 111 | 92 | 19 | 0 | 15 | 0 | 0 | 129 |
| base run 1 | 111 | 92 | 19 | 0 | 15 | 0 | 0 | 129 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 129 tasks; calibration in gates/README.md).

## SV-COMP termination, per component (gdp-scc) (dev set: 129 tasks)

| side | solved | terminates | nonterminating | wrong | unknown | timeout | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 97 | 78 | 19 | 0 | 27 | 2 | 0 | 129 |
| base run 1 | 97 | 78 | 19 | 0 | 27 | 2 | 0 | 129 |
| delta (candidate - base mean) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: 0 (raw 0 on 43 tasks; calibration in gates/README.md).

## TIP 2015 (gdp) (dev set: 239 tasks)

| side | proven | refuted | wrong | unknown | timeout | unsupported | error | tasks |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| candidate | 105 | 6 | 0 | 77 | 43 | 7 | 1 | 239 |
| base run 1 | 103 | 6 | 0 | 76 | 45 | 7 | 2 | 239 |
| delta (candidate - base mean) | +2 | 0 | 0 | +1 | -2 | 0 | -1 | 0 |

- 2 differ in the first pass (2 solved by the candidate only, 0 by the base only; 2 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 1** (0 in every run against none), **lost 0** (0 solid), noise 1, wrong 0; answered only past 45 s in some run (a flip at the time limit): 1 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: +2.3 (raw +2 on 239 tasks; calibration in gates/README.md).

| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |
| --- | --- | --- | --- | --- | --- |
| prod/prop_02.smt2 | gained | 4/4 | 2/4 | yes | proven 34.3, proven 51, proven 38.3, proven 18.8 / timeout 60.2, proven 15.7, timeout 60.2, proven 24 |

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
| candidate | 24 | 33 | 31 | 31 | 0 | 1 |
| base run 1 | 25 | 33 | 31 | 31 | 0 | 1 |
| delta (candidate - base mean) | -1 | 0 | 0 | 0 | 0 | 0 |

- 1 differ in the first pass (0 solved by the candidate only, 1 by the base only; 1 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 60 s limit); after 3 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 1, wrong 0; answered only past 45 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.
- Predicted full-set delta from the dev set: -1 (raw -1 on 64 tasks; calibration in gates/README.md).

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
| candidate | 332 | 332 | 202.9 |
| base run 1 | 332 | 332 | 223.5 |
| delta (candidate - base mean) | 0 | 0 | -20.6 |

- 0 differ in the first pass (0 solved by the candidate only, 0 by the base only; 0 outside the base's noise band: its runs agreeing and no answer in the last quarter of the 55 s limit); after 0 rerun(s) a side: **gained 0** (0 in every run against none), **lost 0** (0 solid), noise 0, wrong 0; answered only past 41.25 s in some run (a flip at the time limit): 0 of the gained, 0 of the lost.

- The same search (outcome, leaves, splits, CDCL's decisions, conflicts and nodes) on 332 of 332 goals (0e9afc3db231 against 8610af26c16c); search ms summed 202,884 against 223,520; candidate/base per goal p10 0.516, p50 0.872, p90 1.559.

## The 5 s-limited tests on 1 vCPU

Failed jobs: candidate none; base none. The ten slowest tests by their most on either side:

| test | candidate median ms | candidate most ms | base median ms | base most ms | runs |
| --- | --- | --- | --- | --- | --- |
| data | definitions that do not terminate, made to look as if they do (rings, a size law true of short lists only, a guard past the runs' values), are refused with the measures tried | 51,043.77 | 52,015.35 | 36,634.82 | 44,475.44 | 3 / 3 |
| data | nested recursion (well-founded, a call in another's argument): taken with an invariant of the function, proven with each decrease; its obligations as Nested.lean states them | 12,836.23 | 16,331.22 | 9,660.52 | 10,071.33 | 3 / 3 |
| data | a ring of functions that is not structural recursion: a measure each (one length), each call within the ring proven to lower the callee's below the caller's | 8,424.24 | 11,058.53 | 6,783.16 | 7,876.07 | 3 / 3 |
| data | halves and a merge over the user's ≤: taken by size laws proven by induction on both halves at once, and by cases on the user's ≤ | 4,654.67 | 6,036.72 | 3,550.77 | 3,949.36 | 3 / 3 |
| infer | a law that needs an invariant: not proven alone, proven with what the search finds, and the set checks | 2,826.91 | 3,610.36 | 2,378.5 | 2,893.01 | 3 / 3 |
| infer | an invariant over four values (the join: the samples' hull, made inductive): one account within the total paid in | 3,574.5 | 3,585.01 | 3,014.52 | 3,529.98 | 3 / 3 |
| data | a function that agrees with + on small values only: its bridge is not proven, and nothing false is proven through it | 2,746.64 | 3,159.03 | 2,374.04 | 2,775.14 | 3 / 3 |
| data | a function of three naturals that computes their sum (add3acc, by well-founded recursion): its bridge proven by its own recursion, a law read through it; one that agrees with a sum on small values only is not proven to | 1,800.83 | 1,964.89 | 1,083.8 | 1,351.46 | 3 / 3 |
| infer | a machine with no rule: the in-flight bound needs s + 50·p <= b + 150 or tighter | 1,555.82 | 1,614.53 | 1,263.17 | 1,912.02 | 3 / 3 |
| infer | what was found reads as the builder call that states it, and that call, written out, proves the law again | 1,748.96 | 1,822.79 | 1,524.07 | 1,900.64 | 3 / 3 |

## Lean: recurrent sets of the ITS run checked again

| side | checked | sampled | max_s |
| --- | --- | --- | --- |
| candidate | 6 | 6 | 5.42 |

- 6 of 6 checked by Lean, at most 5.42 s a file.

## Size

core/ and kernel/ (.ts, tests excluded): 4,454,098 bytes and 57,308 lines, against 4,432,252 and 56,956 (+21,846 bytes, +352 lines).

## Wall time and spend

- Wall: 2,325 s.
- Modal, billed for this bar's own 0 apps: $0 (`modal billing report --start 2026-11-08 --resolution h --json`, complete hours only: the last reported starts noneZ); estimated from the task seconds: $5.4. `bun gates/bar.ts spend /Users/monotykamary/VCS/working-remote/open-source/gdp-wired-trackK/runs/track-k-bar/runs/track-k-v1` reads the bill again once the hours are over.
- Where the jobs ran (each launch's backends.json): {"boat":663}; {"boat":24}; {"boat":798}; {"boat":22}; {"boat":260}; {"boat":240}; {"boat":3}; {"boat":93}; {"boat":128}; {"boat":2}; {"boat":91}; {"boat":332}; {"boat":6}.

