# Termination candidates for the next frontier corpus

Tasks from TermComp's integer transition systems (TPDB-ARI at `183f29d`) and SV-COMP's termination tasks
(sv-benchmarks at `c5cc603`) that gdp-wired expresses (each translates, `compare/term/`) and doesn't prove, where
another tool answered within the same 60 s on the same container (2 vCPU, 4 GB). Each is written as the loop it is
(locations that only pass values along left out), with what it needs, what the other tools did and where gdp-wired's
search stopped. gdp is the translation that is the task's statement (one rank over the whole program, the location a
number in it); gdp-scc is each cycle of locations on its own, chained, from any state (a stronger statement). Figures
are from `runs/modal/term/full1` (LoAT, KoAT2), `koat-fix1` (KoAT2's reruns), `gdp2` (gdp-wired), `diag-koat`
(KoAT2's proofs), `sv2` (Ultimate Automizer) and `sv3` (gdp-wired, LoAT and KoAT2 on gdp-wired's C translation).

## Terminating

| Task | The loop | Needs | Others | gdp-wired stopped at |
| --- | --- | --- | --- | --- |
| ITS `From_AProVE_2014/Continue1.jar-obl-8` | `x := 0; while x < 20: x := x + 1` (two rules, split at 10) | a rank that reads no param: 20 − x | KoAT2 0.18 s (rank 20 − x); LoAT abmc 0.19 s | gdp-scc: rank 25 + 2·x⁻ − (a0⁻ + x⁺) from the runs, reading the start value a0 (constant along a run); the kernel refused it |
| ITS `From_T2/p-60.t2_fixed` | `while i <= 100 and x >= 1: i := i + 1` | 101 − i, reading no param | KoAT2 0.26 s (101 − i); LoAT abmc 0.15 s | gdp-scc: 102 + a3⁻ + i⁻ − (a3 + a4⁻ + i), refused. The same loop written by hand with 3 or more params nothing reads fails the same way, with 2 or fewer it is proven (`runs/modal/term/probes1`) |
| ITS `From_AProVE_2014/AckR.jar-obl-8` | at x = 0: x := 1, y := y − 1; at x > 0: x := x − 1, or x := any v >= 1 and y := y − 1 (an iterative Ackermann) | (y, x) in order | KoAT2 0.26 s (time bounds 1 + y, 1 + y and 1 + x + y on the three rules) | gdp-scc: the linear x + 2·y fits the runs and the kernel refused it; no tuple is tried after a linear rank is refused. The same reset written by hand is proven, rank (y, x) (`probes1`) |
| ITS `From_T2/polyrank1.t2` | `while x >= 1: x := x − y; y := y + 1` | a multiphase rank: y climbs until it is positive, then x drops | LoAT abmc 0.1 s; KoAT2 unknown | gdp-scc: a0 + a1 + a1⁻ + x + 4·y⁻ − y, refused |
| ITS `Britikov_26/toy3.t2` | `x := 0; while y > 1 or y < 0: x := x + 1, and y := 0 once x >= 100` | x < 100 first (100 − x), then y's sign (y, −y) | KoAT2 0.42 s (100 − x, y, −y on its rules); LoAT abmc 0.14 s | gdp-scc: rank y⁻ from the runs, refused |
| ITS `From_AProVE_2014/AProVEMath.jar-obl-8` | halving: `while x > 0`: x even (x = 2·q, q fresh) or odd (x = 2·q + 1), then x := x' with 0 <= x − 2·x' < 2 | runs whose inputs meet an equation: q with x = 2·q | KoAT2 0.24 s (1 + x, 2·x − 1) | gdp-scc: no turn of the loop sampled: findRank draws each input at random, and one an equation pins is almost never drawn |
| ITS `From_AProVE_2014/ListReverseCyclicList.jar-obl-10` | a list built then reversed; each turn's new values are fresh, bounded by the old (one rule bounds its two fresh values with ten inequalities) | runs that meet several bounds on fresh values at once | KoAT2 0.37 s | gdp-scc: no turn sampled (the inputs drawn alone, the guard rarely holds of all of them) |
| ITS `From_AProVE_2014/Alternate.jar-obl-10` | three loops of two locations each, after chaining | a rank per location (the cycle keeps two cut points) | KoAT2 3.81 s (x1 + x2, x0 + x2 − 2, ...) | gdp-scc: rank x0 from the runs, refused |
| SV `termination-crafted/2Nested-1` | `while x >= 0: x := x + y; y := y − 1` (x, y bounded by 65534 first) | a 2-nested (multiphase) rank: y + 1, then x | Ultimate Automizer 7.82 s; LoAT abmc 0.28 s; KoAT2 unknown | gdp-scc: 21 + a0 + y − (a1 + a1⁻ + y⁻), refused |
| SV `termination-crafted/Toulouse-BranchesToLoop-2` | `x := 1 or −1; while y < 100 and z < 100: y := y + x; z := z − x` | a rank by x's sign (100 − y where x = 1, 100 − z where x = −1): two products with x, or a guard in the rank | Ultimate Automizer 9.69 s; LoAT abmc 0.26 s | no rank of the searched shapes fits the 989 sampled turns |
| SV `termination-crafted/Piecewise` | `while q > 0 and p > 0 and p != q: if q < p: q := q − 1, p := any; else if p < q: p := p − 1, q := any` | min(p, q), a rank the search doesn't build (the kernel takes min) | Ultimate Automizer 12.33 s | gdp-scc: pc + p + q from the runs, refused |
| SV `termination-crafted/McCarthy91_Iteration` | `c := 1; while c > 0: if n > 100: n := n − 10, c := c − 1 else n := n + 11, c := c + 1` | a rank with the region n <= 111 as an invariant | KoAT2 0.7 s; Ultimate Automizer 26.3 s | gdp-scc: rank n⁻ from the runs, refused |
| SV `termination-crafted/WhileFalse` | `while false: skip` | any constant rank: the loop takes no turn | KoAT2 0.2 s; LoAT abmc 0.18 s; Ultimate Automizer 8.05 s | gdp-scc: no turn sampled, and with none findRank tries no rank; gdp: 33 − (a0⁻ + pc), reading a param, refused |

## Nonterminating

gdp-wired answers nonterminating only with a lasso (a run that comes back to a state, replayed by ari.ts's evaluator);
its prover has no claim about runs that never end.

| Task | The loop | Needs | Others | gdp-wired |
| --- | --- | --- | --- | --- |
| ITS `Britikov_26/toy2.t2` | `while x >= 100: x := x + 1` | a recurrent set (x >= 100 is kept forever); no state repeats | LoAT 0.07 s; LoAT abmc 0.05 s | runs from values up to 64 never reach x >= 100 |
| ITS `From_AProVE_2014/Velroyen08-trueDiv.jar-obl-8` | `while x > 0: x := x + 1` (and `x < 1: x := x − 1`) | a recurrent set | LoAT 7.92 s; LoAT abmc 0.13 s | long runs, no state repeated |
| ITS `From_AProVE_2014/ex04_rec.jar-obl-8` | `while b < a: (a, b) := (b, b − 1)` | a recurrent set (b − 1 < b forever) | LoAT 0.05 s; LoAT abmc 0.07 s | long runs, no state repeated |
| ITS `From_AProVE_2014/DivTernary2.jar-obl-9` | five values, each a fresh value bounded by the others every turn | a lasso whose fresh values equal the current ones: a run that chooses them, not draws them | LoAT 0.22 s (a recurrent set with a model of small values); LoAT abmc 5.2 s | no lasso found |

## Not expressible, grouped

TermComp's integer transition systems: every one of the 1,239 translates (`runs/modal/term/gdp2`: 0 refused); the
translation is the task's statement (integers as pairs of naturals, a rule's free values as inputs). SV-COMP's 282
termination tasks of the ControlFlow-Termination set: 226 translate, 56 are refused (`runs/modal/term/sv3`):

| Reason | Tasks |
| --- | --- |
| recursion (a cycle of calls from main) | 28 |
| pointers and the heap (malloc) | 10 |
| unsigned types (arithmetic modulo 2^n) | 10 |
| arrays | 6 |
| a call inside a larger expression (only `f(...);`, `x = f(...);` and `return f(...);` are inlined) | 2 |

The 226 translated C tasks are read with unbounded arithmetic: the same as C on every run where no signed operation
overflows (undefined behavior, which SV-COMP's verdicts assume away); no task here uses long.
