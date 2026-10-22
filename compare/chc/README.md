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
| `prof/` | A Modal profiler for one task's `proveRule`; `spacer_models.py`, the invariants Spacer finds for given tasks (or, with `--engine golem`, Golem's derivations of false); `template.ts` (`--tools tmpl`), what `inferLaws` would search on a task (its atoms, coefficient magnitudes and shape limits); `given.ts` (`--tools given`), `proveRule` given Spacer's invariant as laws; `gap.py`, the gap to Spacer by the shape of its invariant and what gdp-wired did |

    modal run compare/chc/modal_chc.py --out runs/modal/chc/<name> [--tools gdp,z3,golem,eldarica] [--limit 60]
    bun compare/chc/summary.ts runs/modal/chc/<name>
    modal run compare/chc/prof/spacer_models.py --out <dir> --tasks-json <file> [--engine golem]
    modal run compare/chc/modal_chc.py --out <dir> --tools tmpl            # then --tools given --tasks-json <file>
    python3 compare/chc/prof/gap.py --gdp <run> --others <run> --models <dir> --template <run> [--cex <dir>] [--given <run>] --out <file.json>

## 0.20.0

Spacer, Golem and Eldarica from `runs/modal/chc/full1` again: the image pins the same releases (Z3 5.3.1, Golem 0.9.0,
Eldarica 2.3) and the benchmarks at `b4fa7a7`, and their command, container (2 vCPU, 4 GB) and 60 s limit are as
they were; since that run, only the packing changed (one task per container, where full1 ran 12 a container one after
another). gdp-wired at bf42c65 (0.20.0, the cyclic certificate the default) from `runs/modal/chc2/v020-gdp`, together
in `runs/modal/chc2/combined-v020`.

| tool | sat | unsat | wrong | solved of 1,406 | out of time | median s of those solved |
| --- | --- | --- | --- | --- | --- | --- |
| Spacer (Z3 5.3.1) | 733 | 430 | 0 | 1,163 | 242 | 0.08 |
| Golem 0.9.0 | 728 | 426 | 0 | 1,154 | 252 | 0.04 |
| Eldarica 2.3 | 501 | 267 | 0 | 768 | 638 | 0.43 |
| gdp-wired 0.20.0 | 224 | 144 | 0 | 368 | 5 | 14.77 |

- Against `eng5-gdp` (366: 223 sat, 143 unsat, 315 out of time): 7 more, 5 fewer. Against `perf4-gdp` (365: 223 sat,
  142 unsat, 12 out of time): 5 more (`s_split_42`, `O3_trex03`, Lustre `MESI_i1_e3_2145_e7_1847`,
  `car_1_e7_184_e3_299`, `fast_2_e7_1871`), 2 fewer (`reve/014b`, `gj2007_m_3`). Each of the 5 tasks lost (against either run) ends unknown
  at the deadline (58.09 s to 58.37 s here); eng5 had solved them in 15.3 s to 52.22 s, perf4 the two in 58.06 s and
  58.1 s.
- Answered by: 224 sat with the invariants `inferLaws` found, 64 unsat by runs the prover guided, 43 by random runs, 37
  by `proveRule`'s refutation. Of the 1,033 unknown, every one ends after the invariant search; the 5 out of time are
  Lustre models.
- The certificate doesn't dominate: with `GDP_CERT=usual` (`runs/modal/chc2/v020-usual-gdp`), 369 solved (225 sat, 144
  unsat, none wrongly, 7 out of time); on the 223 sat tasks both runs solve, the median is 21.66 s (cyclic) and 21.71 s
  (usual), and the time after the guided runs adds to 2,752,243 ms and 2,783,451 ms; on the 144 unsat, 0.28 s and
  0.265 s. Of the three tasks that differ, each ends unknown at the deadline in the run that misses it (58.11 s to
  58.27 s), solved in the other at 58.09 s to 58.64 s.
- Nine solved by gdp-wired alone, the same nine as eng5; 906 solved by another tool and not by gdp-wired: 536 Spacer
  answers sat, 67 only Golem or Eldarica answer sat, 303 some tool answers unsat.

### What gdp-wired lacks, by Spacer's invariants

`prof/gap.py` reads Spacer's model of each of the 536 (`runs/modal/chc2/spacer-models-sat`, 60 s each; 531 came
back, 5 ran out of time), puts each predicate's interpretation in CNF over linear atoms, and checks each clause
against what `inferLaws` builds for that task (`prof/template.ts`, `runs/modal/chc2/template`: its atoms, its
coefficient magnitudes 1, 2, 3 and the first four of the machine's constants up to 1,000, and which shapes of two and
three values its limits leave). Then `prof/given.ts` states Spacer's invariant as gdp-wired laws (one per top-level
conjunct, `loc is p → conjunct`) and runs `proveRule` with them, no search (`runs/modal/chc2/given-spacer3`). A task's
class is its most demanding clause. Spacer's invariant isn't the only one, nor the simplest: a task whose Spacer
invariant is outside the templates may have another inside them.

| Spacer's invariant (sat, 536) | tasks | Lustre | given it, proven | given it, step goal undecided | can't be stated |
| --- | --- | --- | --- | --- | --- |
| within the templates: bounds of one value (204), a yes/no guard (23), two values (15), a disjunction of two as a counterexample's form (11) | 253 | 237 | 54 | 197 | 0 |
| a disjunction of three or more literals | 154 | 72 | 58 | 87 | 3 |
| more than three values in one atom | 71 | 32 | 22 | 41 | 0 |
| an existential (Spacer's projection) | 19 | 0 | 0 | 0 | 18 |
| a remainder (16) or a quotient (2) | 18 | 5 | 0 | 0 | 18 |
| a boolean structure past 4,000 CNF clauses | 13 | 0 | 0 | 6 | 6 |
| a disjunction of two outside the counterexample's forms (2), three values with a coefficient past the template (1) | 3 | 0 | 1 | 1 | 0 |
| no Spacer model in 60 s | 5 | 0 | | | |

The rest of each row: out of the 60 s given the invariant (16 in all), and 3 where the kernel refutes a conjunct of
Spacer's printed model itself (HOLA `05`, `17`, `39`; on `39` the printed model makes `CHC_COMP_FALSE` true while a
query reads it alone, so it isn't a model of the clauses).

- **The step goal over a wide transition (332 tasks, 287 of them Lustre).** Given Spacer's own invariant, the kernel
  leaves one of its conjuncts' step goals undecided at the prover's per-goal time budget (20 s, or 1 s a hypothesis
  past 20; 20,271 ms to 59,360 ms, median 38,623.5 ms). 195 of these are Lustre tasks whose invariant is within the
  templates, most often one yes/no value (`DRAGON_10`: `b19` alone, the time budget out at 37 hypotheses, 2 case
  splits deep); on 73 of the 195 the goal gdp-wired's search stopped on is one of Spacer's conjuncts. On `DRAGON_10`,
  of the 17 candidates it chose against the law's counterexamples, it dropped the other 16 one by one, and the proof
  of `b19`'s step then ran 22,166 ms into the deadline. The runs give the search little there: 39 reachable states,
  60,000 candidates alive after Houdini.
- **The search, the shape in reach (135 tasks proven given Spacer's invariant).** 54 within the templates (41 Lustre),
  81 outside them: a disjunction of three or more (58; 33 of them guards of two or more yes/no values beside at most
  one linear literal, a program counter in bits: 24 `ctigar`, 8 Lustre, 1 `conc`), more than three values (22), and one
  other.
- **Shapes outside the templates (278 tasks).** A disjunction of three or more literals (154: 73 of three or more
  linear literals, 43 of two beside yes/no values, 38 of yes/no values beside at most one linear literal of at most two
  values); more than three values in one atom (71: 39 of four values with coefficients ±1, 25 of those Lustre; of the
  39 not Lustre, 30 are the relational `reve` and `llreve` tasks, two programs side by side, x₁ + y₂ ≤ x₂ + y₁ and the
  like); the rest above. 84 tasks' invariants are nontrivial at two predicates or more; Spacer's invariants have 1–3
  clauses on 219 tasks, 4–10 on 143, 11–30 on 88, more on 81 (within the templates: one clause on 155 of 253).
- **What a gdp-wired law can't state here (45 given Spacer's invariant).** Laws state any linear sum, any coefficient,
  any disjunction (`or`, `any`) and products (`Term.mul`), so every class above is expressible but two: an existential
  (27, Spacer's projection leaving a variable; a quantifier-free equivalent exists in linear integer arithmetic, possibly
  with divisibility), and a remainder or quotient (18): the rule reads no `modBy(c)`/`divBy(c)` (translate.ts takes a
  CHC `mod` as a request value q with c·q ≤ e ≤ c·q + c − 1), and a CHC integer is a pair of naturals, so `x mod 2 = 0`
  needs a quotient in the state or the remainders of both parts.

Unsat (303 some tool answers and gdp-wired doesn't; Golem's derivations of false, `runs/modal/chc2/golem-cex-unsat`,
287 of them within 60 s), against how deep gdp-wired's runs the prover guided went (their steps a trial):

| | Lustre | other |
| --- | --- | --- |
| Golem's derivation longer than the guided runs go | 169 | 23 |
| within that depth, the values not found | 89 | 4 |
| past 2,000 steps (a guided run's cap) | 0 | 2 |
| no Golem derivation in 60 s | 15 | 1 |

- **Short derivations whose requests no run finds (Lustre, 273).** 225 of Golem's derivations are 5 steps or fewer
  (13 of 6–10, 17 of 11–20, 3 of 21–50); on the 258 with one, gdp-wired's guided runs make a median 47 steps in 18
  trials. Each step's
  request is a model of one clause's wide condition at the state, chosen without the query in view: the trials die after
  a few steps or wander (`car_4_e3_57_e5_999`: a derivation of 3 steps, 628 steps a trial). What's missing is a model of
  k steps at once with the query at the end (a bounded model check over the rule).
- **The others (30).** Mostly `hcai-bench/svcomp` (19): 15 derivations of 4 to 14 steps, and `O3_id_o20`, `o100`,
  `o200`, `o1000` of 23, 103, 203 and 1,003; the guided runs went 1.8 to 8.7 steps a trial there. `s_split_01` and
  `s_split_48` need 10,002 (a loop run to 10,000), past any run: a derivation that summarizes a loop (acceleration).
- The candidates for the next corpus, by class: `research/frontier2/candidates-chc.md`.

## Results before 0.20.0

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
