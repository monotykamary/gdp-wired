# Termination benchmarks through gdp-wired

gdp-wired proves a loop halts with `proveLoop` and no rank stated: core/cycles.ts's `findRank` takes the rank from the
loop's runs (linear by LP, the exact LP past coefficient 4, degree 2 one product at a time, tuples in order), with the
invariants `inferLaws` finds, and the kernel checks the halting goals. This directory runs it on termination problems
it didn't write, beside tools built for them, every task in its own Modal container (2 vCPU, 4 GB) under the same 60 s
wall-clock limit for every tool:

- TermComp's integer transition systems: TPDB-ARI (`TermCOMP/TPDB-ARI` at `183f29d`), `Integer_Transition_Systems`,
  all 1,239 `.ari` files (From_AProVE_2014 416, From_T2 806, Britikov_26 6, Lommen_26 6, Monma_26 5). No verdicts
  come with them.
- SV-COMP's termination tasks: sv-benchmarks (`sosy-lab/benchmarking/sv-benchmarks` at `c5cc603`), the
  ControlFlow-Termination set's directories (termination-crafted, -crafted-lit, -numeric, -restricted-15, -nla): the
  282 tasks with `termination.prp`, each with its expected verdict (221 true, 61 false).

| File | What |
| --- | --- |
| `ari.ts` | The ARI format read (`(format LCTRS)`, `(theory Ints)`: locations, an entrypoint, rules with guards), and an evaluator of a rule on integer values (BigInt) that uses no gdp-wired code; `checkLasso` replays a nontermination witness on it |
| `translate.ts` | A task as a kernel `Loop`, the same statement (below); `stepOf` turns a turn of the loop back into the task's step for the witness |
| `scc.ts` | The second translation, a stronger statement counted apart: each strongly connected component of the locations, chained (the paths between cut points composed into one rule each), from any state at its cut points |
| `solve.ts` | One task: lassos from the loop's runs (2 s), a recurrent set (core/nonterm.ts, 4 s), `findRank` with all but 9 s of the limit, the kernel's check again on the loop as translated, a recurrent set again (3/5 of what is left) and lassos with the rest; `--scc` for the second translation |
| `recur-lean.ts` | The recurrent sets of a run's answers (each printed in its `recur`) as Lean theorems `NeverEnds <task>_loop` by Kern.never_ends_of; `--shard i/n` |
| `c2ari.py` | An SV-COMP C program as an ARI system (pycparser): main and the functions it calls inlined, signed integers, the C subset in its header; refusals with their reason |
| `modal_term.py` | The ITS track on Modal: gdp-wired (`gdp`, `gdp-scc`), LoAT, LoAT with `--engine abmc`, KoAT2; `koat2-proof` and `loat-proof`, the same runs with their proofs kept |
| `modal_sv.py` | The SV-COMP tasks on Modal: gdp-wired on its translation, Ultimate Automizer on the C program, LoAT and KoAT2 on gdp-wired's translation |
| `summary.ts` | The tables below from run directories (later rows replacing earlier ones) |
| `failures.ts` | The tasks another tool answered and gdp-wired didn't, by where gdp-wired stopped and what KoAT2's proof used |
| `probes.ts`, `probes.json` | Two of the failure classes on loops written by hand (`modal run modal/run.py --jobs compare/term/probes.json`) |

    modal run compare/term/modal_term.py --out runs/modal/term/<name> [--tools gdp,gdp-scc,loat,loat-abmc,koat2] [--limit 60] [--tasks-file <names>]
    modal run compare/term/modal_sv.py --out runs/modal/term/<name> [--tools gdp,gdp-scc,uautomizer,loat-abmc,koat2]
    bun compare/term/summary.ts runs/modal/term/full1 runs/modal/term/koat-fix1 runs/modal/term/gdp2
    bun compare/term/failures.ts runs/modal/term/diag-koat runs/modal/term/full1 runs/modal/term/koat-fix1 runs/modal/term/gdp2 --bench <TPDB-ARI checkout>

## The translation

The state of the loop is `pc` (the location's number) and each argument slot as a pair of naturals (s, s$n), the
integer s − s$n, at most one of them nonzero: every step writes P ∸ N and N ∸ P for a value P − N, so a comparison
a ≤ b is a⁺ + b⁻ ≤ b⁺ + a⁻ and a product is the four products of the parts. The params are the entrypoint's integers
as pairs (every integer is one, so the loop starts wherever the task does). A turn's inputs are `t`, which rule leaving
the location fires (its index among them), and the values the rule leaves free (pairs again); the assumption is that
the rule named is at the location and its guard holds. An equation that gives a free value as a term of known ones is
a definition (x' = x + 1, or solved where the variable's coefficient is ±1), so most post values are terms, not
inputs; `exists` binds inputs; div and mod by a constant take one input each, with their range in the guard. A slot
no rule changes is a param. The loop runs while the location has a rule leaving it, and a state where no rule's guard
holds has no turn, so a run of the loop is a run of the task, value for value, and back: the loop halts from every
start exactly when the task terminates. Nothing is refused: all 1,239 tasks translate, 1,027 with nondeterministic
values, 527 with `exists`, 21 with products of variables, 5 with disjunctions, 3 with div or mod.

`gdp-scc` proves a stronger statement and is counted apart: every infinite run stays in one component from some step
on, so if no run inside a component is infinite from any values, the task terminates; that last step is scc.ts's
argument, not the kernel's (the kernel checks each component's halting). A component's slots that no guard reads
(directly or through the slots and definitions a guard's slots come from) are left out. From any values, a component
can run forever where the task never reaches those values (a loop whose bound an earlier assignment fixes); there it
proves nothing.

Nonterminating means a lasso: a run of the translated loop (gdp-wired's interpreter, random turns, inputs small or
values the state holds) that comes back to a state it was in, turned back into the task's steps (the rule and the
value of each of its free variables) and replayed by ari.ts's evaluator from the start to the repeat. gdp-wired's
prover made no claim about runs that never end until NonTerm.lean's `NeverEnds`: now a nonterminating answer is also
a closed recurrent set with its turn given by terms (core/nonterm.ts's findNeverEnds: a lasso's states, or a set of
linear facts fitted to a run whose inputs are terms over the state), a start and a stem into it, its closure goal
checked by the kernel (kernel.ts's checkRecur) and printed (`recur`) for Lean (`recur-lean.ts`); a lasso among those is
replayed by ari.ts's evaluator too.

For C, `c2ari.py` reads main and the functions it calls (each call inlined), over signed integer variables, with
`__VERIFIER_nondet_*` a fresh value in its type's range, `__VERIFIER_assume` a guard, and `/` and `%` by a positive
constant as C's truncation toward zero (a fresh quotient q with x − k·q in [0, k) for x >= 0 and k·q − x in [0, k)
for x < 0). Arithmetic is on unbounded integers: the same as C on every run where no signed operation overflows
(undefined behavior, which the tasks' verdicts assume away); no task here uses long, whose values would be left
unbounded. 226 of the 282 tasks translate (24 with products of variables, 15 with division by a constant); refused:
recursion 28, pointers and the heap 10, unsigned types 10, arrays 6, a call inside a larger expression 2
(`runs/modal/term/sv3`).

## Results

Integer transition systems (1,239). LoAT and KoAT2 from `runs/modal/term/full1`, KoAT2's 64 tasks that errored
there again from `koat-fix1` (KoAT2's readers refused the AProVE tasks' quoted names until renamed; 6 still error),
gdp-wired from `gdp2` (commit `327d9d6`); `bun compare/term/summary.ts` over the three gives
`runs/modal/term/its-summary.txt`. No task comes with a verdict, so an answer counts as wrong where another tool's
opposite answer is certified (gdp-wired's: the kernel's proof, or a lasso the evaluator replayed); no two tools
disagreed anywhere, certified or not.

| tool | terminates | nonterminating | wrong | solved of 1,239 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| gdp-wired (the task's statement) | 59 | 318 | 0 | 377 | 0.1 |
| gdp-wired, per component (stronger statement, counted apart) | 162 | 326 | 0 | 488 | 0.15 |
| LoAT v0.9.10 (`--mode termination`) | 2 | 532 | 0 | 534 | 0.17 |
| LoAT v0.9.10 (`--mode termination --engine abmc`) | 284 | 492 | 0 | 776 | 0.2 |
| KoAT2 v2.7.0 (`analyse --termination`) | 601 | 0 | 0 | 601 | 0.4 |

SV-COMP's termination tasks (282). Ultimate Automizer from `runs/modal/term/sv2`; gdp-wired, and LoAT and KoAT2 on
gdp-wired's translation, from `sv3` (commit `da30a0a`); `runs/modal/term/sv-summary.txt`. Wrong is an answer against
the task's expected verdict.

| tool | terminates | nonterminating | wrong | solved of 282 | median s of those solved |
| --- | --- | --- | --- | --- | --- |
| gdp-wired (the task's statement) | 0 | 47 | 0 | 47 | 0.17 |
| gdp-wired, per component (stronger statement, counted apart) | 40 | 47 | 0 | 87 | 0.2 |
| Ultimate Automizer v0.3.1 (the C program) | 171 | 53 | 0 | 224 | 7.78 |
| LoAT v0.9.10 abmc (gdp-wired's translation) | 107 | 41 | 0 | 148 | 0.26 |
| KoAT2 v2.7.0 (gdp-wired's translation) | 123 | 0 | 0 | 123 | 0.5 |

- Versions: LoAT `b41690b` (Yices 2.6.5, SwInE `141d022`, Z3 4.15.4.0, printed with its proofs in `diag-loat`),
  KoAT2 v2.7.0 (Z3 4.15.2.0), Ultimate Automizer's v0.3.1 release (OpenJDK 21.0.12.1), bun 1.4.4, pycparser 3.00.
  KoAT2 reads ARI through its own `ari-to-koat` (`^` and the quoted names renamed first); on the C translations 27 of
  its runs stop on `Z.Overflow` (the int range's constants). Ultimate Automizer refuses two tasks (`knuth-both-t`, `knuth-both-nt`: an operation its non-bitprecise translation lacks).
- Either gdp-wired translation solves 498 ITS tasks; any tool, 1,159. Eight ITS tasks are solved by gdp-wired and
  none of the others: `java_PlusSwap.c.t2` terminating (rank s7 + s8 on its one component), and seven nonterminating
  by lasso (`Velroyen08-moduloUp`, `complxStruc_rec`, `db2`, `db3` and their `_fixed` twins, `bio`), five of them
  where every other tool ran out of the 60 s. None of the SV tasks.
- The two translations' lasso counts differ (318 and 326) though their lassos are the same search: the runs are
  seeded but bounded by time, and the two rank searches between them take different times.
- Monma_26's README calls `reverse_lexicographic.ari` terminating. gdp-wired's lasso, replayed by the evaluator: from
  m = 6, l1 at (m, x, y, s, t, p) = (6, 6, 0, 0, 6, 0) goes l5 (y + 1, t − 1), l1, l2, l4 (y − 1, t + 1) and is back at
  (6, 6, 0, 0, 6, 0); LoAT abmc answers nonterminating too.
- The ranks found, over the 261 proofs of termination (ITS: gdp 59, gdp-scc 162; SV: gdp-scc 40), each component's
  counted: 320 ranks, 308 of one term and 12 tuples of two in order; 9 read a product of two variables, one a
  coefficient past 4.
- Not run: the Lean twin on the ranks found (every proof here is the kernel's, checked twice: in `findRank`, and again
  in solve.ts on the obligations of the loop as translated).

### Runs that never end, after 0.22.0

The ITS track again, `gdp` alone, on Modal (the boat pool had no VM to spare): 0.22.0 (`c215ded`,
`runs/nonterm/base-its`) against this branch (`runs/nonterm/after2-its`); SV-COMP the same way (`runs/nonterm/base-sv`,
`runs/nonterm/after2-sv`).

| | terminates | nonterminating | unknown | timeout |
| --- | --- | --- | --- | --- |
| ITS, 0.22.0 | 56 | 320 | 837 | 26 |
| ITS, this branch | 56 | 450 | 703 | 30 |
| SV, 0.22.0 | 0 | 47 | 179 (56 unsupported) | 0 |
| SV, this branch | 0 | 47 | 179 (56 unsupported) | 0 |

- The 450: 319 lassos of solve.ts's own stage, as before, and 131 recurrent sets (106 sets of linear facts, 19 lassos
  of a policy run, 6 of a random run). 133 tasks are answered that 0.22.0 left (131 unknown, 2 timeouts); 3 that it
  answered by a lasso are not (2.t2 and bio.t2 unknown, afagp-fail.t2_fixed a timeout: the lasso stages' runs are
  bounded by time, and here the import took 2.9 s of the first stage's 2 s). The 56 proofs of termination are the same
  tasks.
- No answer contradicts another: none of the 450 is a task LoAT, LoAT abmc or KoAT2 proves terminating
  (`runs/modal/term/full1`, `koat-fix1`), none of the 56 one they prove nonterminating, and no task changed its answer
  between the two runs. Of the 133 new ones, 105 are LoAT's NO too and 24 are lassos replayed by ari.ts's evaluator;
  db2 and db3 had a replayed lasso in an earlier run (`runs/modal/term/gdp2`, gdp-scc); Velroyen08-fib and
  NonPeriodicNonterm2, which no other tool answers, were read by hand (a Fibonacci pair past a fixed bound never meets
  it again; a counter that doubles each time it meets the other).
- Lean: every recurrent set of the first run of this branch, 127 (`runs/nonterm/after-its`), is a theorem
  `NeverEnds <task>_loop` that Lean 4.34.0 checks (`decide +kernel`, on `propext`, `Classical.choice`, `Quot.sound`;
  `runs/nonterm/bench-lean`, the 22 of two shards that ran out of memory or time one at a time, `bench-lean2`; up to
  30.4 min for a shard of 11, 8.4 min for one certificate alone).
- SV-COMP: unchanged; every nonterminating task another tool answers and gdp-wired doesn't is one the C translation
  refuses.

## Where gdp-wired stops

The tasks another tool answered and gdp-wired didn't (`failures.ts`; `runs/modal/term/failures-its.txt`,
`failures-sv.txt`). The location-free translation alone misses 113 ITS tasks and 40 SV tasks that the per-component
one proves: one rank for the whole program, the location a number in it, is what fails there (KoAT2's proofs give each
location its own). Past that, each terminating task is put where gdp-scc stopped:

| class | ITS | SV |
| --- | --- | --- |
| the rank the runs gave reads a param (a start value, constant along each run) and the kernel refused it | 217 | 95 |
| no turn of the component sampled: findRank's runs draw each input alone and keep a turn only where the guard holds | 158 | 4 |
| a rank the runs gave the kernel refused, reading no param (wrong off the runs, or needing an invariant not found) | 61 | 24 |
| no rank of the searched shapes fits the sampled turns | 9 | 6 |
| out of time | 2 | 0 |
| total, terminating by another tool | 447 | 129 |

- Params: the same loop written by hand (`while i <= 100 and X >= 1: i := i + 1`, rank 101 − i) beside params nothing
  reads is proven with 0, 1 or 2 of them and refused with 3, 4, 6 or 8, the rank found reading them
  (`(101 + P1 + P2 + X − (P0 + i))` with 3; `runs/modal/term/probes1`). Both translations make every start value a
  param, and every slot no rule changes.
- No turn sampled (ITS, the 154 where KoAT2's proof was read, split by what the component's guards ask, `--bench`):
  an input an equation pins (x = 2·q) 46, a constant past the runs' 64 in a guard 6, both 3, and 99 where several
  fresh values are bounded together (each drawn alone, the guard rarely holds of all of them). On SV it includes
  `WhileFalse`: a loop that takes no turn, where with no sampled turn findRank tries no rank at all.
- Of the 431 ITS tasks KoAT2 proved and gdp-wired didn't, its proof bounds every transition by a multiphase ranking
  function of depth 1 (354) or needs none (77): no proof read needs a multiphase rank; KoAT2 ranks each location
  separately and bounds transitions one at a time (an iterative Ackermann, `AckR`: 1 + y, 1 + y, 1 + x + y on its
  three rules). gdp-scc's rank there is x + 2·y, which the kernel refused; findRank tries no tuple after a linear rank
  the kernel refuses (the same reset written by hand is proven, rank (y, x): `probes1`).
- The multiphase and piecewise ones show up on SV, proven by Ultimate Automizer: `2Nested-1` (x := x + y; y := y − 1:
  y + 1, then x), `Toulouse-BranchesToLoop-2` (a rank by the sign of x), `Piecewise` (min(p, q)).
- Nonterminating by another tool and no lasso: 214 ITS tasks (LoAT's proofs are recurrent sets; they don't say whether
  a state repeats). gdp-wired's runs there: 129 long runs where no state came back, 85 runs that stop within 5 turns on
  average. Of 16 read by hand (every fourteenth of the 214 by name; a sample), in 9 the infinite run LoAT found grows
  or shrinks a value forever, so none of its states repeats (`toy2`, `Velroyen08-ex01`, `Velroyen08-trueDiv`,
  `ex04_rec`, `eric3`, `n-37`, `p-46`, `ruslan-benchmarks_misc_n-38`, `slayer-n2-filtered`); in 2 one turn takes the
  state LoAT's proof reaches back to itself when the turn's fresh values are chosen equal to the current ones, which
  the random draws never did (`DivTernary2`, `Samefringe`); 5 weren't decided by reading (`MainCopy`, `compress`,
  `fun10b`, `hqr.c.i.hqr.pl.t2.nor.t2.rlgfixed.t2_fixed`, `tqli`). On SV, every nonterminating task another tool
  answered and gdp-wired didn't is one it refuses to translate.

Bugs and limits found in the library, recorded here and not changed (this is a measurement):

- `findRank`'s LP reads params no guard reads, and the kernel refuses what it gives (above; `probes1`).
- With no sampled turn, `findRank` tries no rank (a loop whose guard is never met is proven by any constant).
- After the kernel refuses the linear rank the runs gave, `findRank` tries invariants and degree 2, never a tuple.
- `findRank` threw `Maximum call stack size exceeded` on 4 ITS tasks (`tqli.t2`: 29 locations, 47 rules, 22 slots;
  `pgarch.t2_fixed`: 203 locations), and on 30 ITS tasks it outran its deadline (the search given 49 s and still
  running at 60 s, `gdp2`'s timeouts).
- A loop's runs draw each input on its own and keep a turn where the assumption holds: an input the guard pins, or
  several bounded together, is almost never drawn (the 158 above).
