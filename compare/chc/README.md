# CHC-COMP's LIA-Lin track through gdp-wired

Every rule and law elsewhere in this repo was written here. This directory runs gdp-wired on problems it didn't write:
the 1,406 tasks of CHC-COMP 2026's LIA-Lin track (linear constrained Horn clauses over integers and booleans,
`chc-comp/chc-comp26-benchmarks` at `b4fa7a7`), beside three solvers built for them: Z3's Spacer (5.3.1), Golem (0.9.0)
and Eldarica (2.3).

| File | What |
| --- | --- |
| `chc.ts` | The CHC-COMP format read (S-expressions, predicates, clauses), and an evaluator of a clause on values that uses no gdp-wired code |
| `translate.ts` | A linear CHC system as a rule: the state is where a derivation is (start, a predicate, error) and the predicate's arguments; a request names a clause that fires where the run is (the rule's assumption) and the values it leaves free, so each update reads the clause named alone. The law: error is never reached. `checkDerivation` checks a run against the CHC itself |
| `houdini.ts` | The first Houdini (`--old-houdini`): candidate laws per predicate (bounds, differences, sums, booleans, unreachable), those a run's state breaks dropped, then rounds of `proveRule` until the rest are inductive together |
| `solve.ts` | One task: import, `proveRule` on the law, random runs of the compiled rule, runs the prover guides (each request a model of its clause's condition where the run is, the clauses that derive false tried first), then the library's invariant search (`inferLaws`, core/infer.ts) from the states the runs reached. Answers sat (a proof the kernel checked), unsat (a run reaching error that `checkDerivation` confirms), unknown or unsupported |
| `modal_chc.py` | The track on Modal: every task in its own container (2 vCPU, 4 GB), each tool under the same 60 s wall-clock limit, all at once (`starmap`) |
| `summary.ts` | The table below from a run's `results.jsonl`, with wrong answers counted against each task's expected verdict where some tool decided it at CHC-COMP'26 |
| `prof/` | A Modal profiler for one task's `proveRule`; `spacer_models.py`, the invariants Spacer finds for given tasks |

    modal run compare/chc/modal_chc.py --out runs/modal/chc/<name> [--tools gdp,z3,golem,eldarica] [--limit 60]
    bun compare/chc/summary.ts runs/modal/chc/<name>

## Results

Spacer, Golem and Eldarica from `runs/modal/chc/full1`, gdp-wired from `runs/modal/chc/eng5-gdp` (every task in its own
container), together in `runs/modal/chc/combined-eng5`. A task is solved when the answer is sat or unsat and, where
CHC-COMP'26 decided the task, the same as its verdict.

| tool | sat | unsat | wrong | solved of 1,406 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| Spacer (Z3 5.3.1) | 733 | 430 | 0 | 1,163 | 0.08 |
| Golem 0.9.0 | 728 | 426 | 0 | 1,154 | 0.04 |
| Eldarica 2.3 | 501 | 267 | 0 | 768 | 0.43 |
| gdp-wired | 223 | 143 | 0 | 366 | 14.71 |

- With the prover's deadline (every proof the search makes bounded by the stage's time, the stage ending 2 s before
  the limit): 365 solved (223 sat, 142 unsat), none wrongly, 12 out of time, against 315 out of time before
  (`runs/modal/chc/perf4-gdp`).
- Every task imports (none refused). Of gdp-wired's answers, 223 sat are the law proven with the invariants `inferLaws`
  found, checked by the kernel; 63 unsat are runs the prover guided reaching error, 43 random runs, 37 `proveRule`'s
  own refutation; every unsat run is checked against the CHC clauses by `checkDerivation`.
- Nine tasks are solved by gdp-wired and none of the others within 60 s; the others solve 908 that gdp-wired doesn't.
- The same track at 0.15.0's code (`runs/modal/chc/eng0-gdp`): 199 solved (119 sat, 80 unsat). What moved it:
  - A request names a clause that fires (the rule's assumption) instead of a step leaving the state as it was when the
    clause doesn't: each update then reads the clause named alone, where it read each clause's whole constraint. On 461
    tasks the first proof had stopped on `loc`'s kind law (stays a location), splitting every clause's constraint;
    none does now, and the tasks that ran out of time went from 339 to 95 (`eng2-gdp`: 259 solved).
  - Runs the prover guides: each request a model of its clause's condition where the run is (the prover's witness on a
    goal it doesn't refute), the clauses that derive false tried first: 63 unsat no random run had reached (on a
    hand-written task, a derivation of 702 steps).
  - In `inferLaws`, a counterexample to induction no candidate rules out makes candidates of its own, false at it and
    met by every sample under a condition it meets (a value, or a sum or difference of two, at most a threshold), the
    choice at its value as the guard; and a choice is no term among others. Of the 148 tasks that had ended so,
    Spacer (30 s, `spacer-models-cti`, `prof/spacer_models.py`) answered 80 sat, 70 of those with a disjunction in the
    invariant (24 with a coefficient of 2 or more) and 9 reading a remainder; 21 unsat; 47 ran out of time.
- Where it stops: 706 tasks end on a candidate the search chose whose own counterexample nothing rules out, 19 on the
  law's; 315 run out of the 60 s, 282 of them Lustre models. Three tasks the folder's first Houdini answered aren't
  answered (`dillig05_m`, `s_split_28`, `reve/026b`), nor three that 0.15.0's code answered (`s_split_20`,
  `s_multipl_18`, `loop__loop3`). Unsat Lustre models (274 that another tool answers) need deeper runs than these: the
  prover-guided runs take 40.5 steps a task there (the median), each request a model of a large constraint.
- What it found in the library: on the 766 Lustre tasks (one predicate over up to 80 integers and 33 booleans),
  `proveRule` spent 20–45 s proving that a yes/no state stays 0 or 1, case-splitting the whole step guard. 0.14.1's
  kernel row (an if is at most the sum of its branches; 0.14.2 keeps it to constant branches) closes that: the median
  prove stage over the track went from 20.8 s (`full2-gdp`, 1,358 tasks) to 0.35 s (`full4-gdp`, 1,392 tasks).
- Not covered: nonlinear clauses (none in this track), arrays, bit vectors and algebraic datatypes (other tracks).
