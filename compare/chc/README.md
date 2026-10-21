# CHC-COMP's LIA-Lin track through gdp-wired

Every rule and law elsewhere in this repo was written here. This directory runs gdp-wired on problems it didn't write:
the 1,406 tasks of CHC-COMP 2026's LIA-Lin track (linear constrained Horn clauses over integers and booleans,
`chc-comp/chc-comp26-benchmarks` at `b4fa7a7`), beside three solvers built for them: Z3's Spacer (5.3.1), Golem (0.9.0)
and Eldarica (2.3).

| File | What |
| --- | --- |
| `chc.ts` | The CHC-COMP format read (S-expressions, predicates, clauses), and an evaluator of a clause on values that uses no gdp-wired code |
| `translate.ts` | A linear CHC system as a rule: the state is where a derivation is (start, a predicate, error) and the predicate's arguments; a request names a clause and the values it leaves free. The law: error is never reached. `checkDerivation` checks a run against the CHC itself |
| `houdini.ts` | Candidate laws per predicate (bounds, differences, sums, booleans, unreachable), those a run's state breaks dropped, then rounds of `proveRule` until the rest are inductive together |
| `solve.ts` | One task: import, `proveRule` on the law, random runs of the compiled rule, Houdini. Answers sat (a proof the kernel checked), unsat (a run reaching error that `checkDerivation` confirms), unknown or unsupported |
| `modal_chc.py` | The track on Modal: every task in its own container (2 vCPU, 4 GB), each tool under the same 60 s wall-clock limit, all at once (`starmap`) |
| `summary.ts` | The table below from a run's `results.jsonl`, with wrong answers counted against each task's expected verdict where some tool decided it at CHC-COMP'26 |
| `prof/` | A Modal profiler for one task's `proveRule` |

    modal run compare/chc/modal_chc.py --out runs/modal/chc/<name> [--tools gdp,z3,golem,eldarica] [--limit 60]
    bun compare/chc/summary.ts runs/modal/chc/<name>

## Results

Spacer, Golem and Eldarica from `runs/modal/chc/full1`, gdp-wired from `runs/modal/chc/full4-gdp` (0.14.2; every task in
its own container, the whole track in a few minutes of wall time), together in `runs/modal/chc/combined4`. A task is solved when the answer is sat
or unsat and, where CHC-COMP'26 decided the task, the same as its verdict.

| tool | sat | unsat | wrong | solved of 1,406 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| Spacer (Z3 5.3.1) | 733 | 430 | 0 | 1,163 | 0.08 |
| Golem 0.9.0 | 728 | 426 | 0 | 1,154 | 0.04 |
| Eldarica 2.3 | 501 | 267 | 0 | 768 | 0.43 |
| gdp-wired | 48 | 80 | 0 | 128 | 1 |

- Every task imports (none refused). Of gdp-wired's answers, 48 sat are Houdini's candidates proven together and
  checked by the kernel, 76 unsat are random runs reaching error and 4 unsat come from `proveRule`'s own refutation;
  every unsat run is checked against the CHC clauses by `checkDerivation`.
- One task is solved by gdp-wired and none of the others within 60 s: `extra-small-lia/dillig05_m` (sat, 96 invariants,
  55.9 s; CHC-COMP's own limit is longer). The others solve 1,138 that gdp-wired doesn't.
- What this measures is invariant inference, which gdp-wired doesn't do: its prover checks the laws you write, and a CHC
  task gives none but the safety property. Houdini's templates find the invariants of 48 tasks; on most of the rest the
  templates over many variables are too many to try, or the inductive set found doesn't imply the law.
- What it found in the library: on the 766 Lustre tasks (one predicate over up to 80 integers and 33 booleans),
  `proveRule` spent 20–45 s proving that a yes/no state stays 0 or 1, case-splitting the whole step guard. 0.14.1's
  kernel row (an if is at most the sum of its branches; 0.14.2 keeps it to constant branches) closes that: the median
  prove stage over the track went from 20.8 s (`full2-gdp`, 1,358 tasks) to 0.35 s (`full4-gdp`, 1,392 tasks).
- Not covered: nonlinear clauses (none in this track), arrays, bit vectors and algebraic datatypes (other tracks).
