# The observation table: one search for the frontier

**Hypothesis.** Every frontier search in gdp-wired is one structure: evaluate a grammar of terms on samples to get a
table (rows: reachable states, transition pairs, argument tuples; columns: terms), then answer one of five queries over
it:

| Query | What it answers | The search it would stand for today |
| --- | --- | --- |
| Q1 equalities | the affine relations every row meets (the null space of [columns · 1], exact over ℚ) | discover's closed forms (Newton differences), inferLaws' equalities |
| Q2 bounds | lo ≤ t ≤ hi per column | inferLaws' templates (d = the samples' maximum), discover's bounds, cycleLemmas' bounds |
| Q3 rank | a combination that drops by 1 on the strict transition rows, doesn't rise on the others, ≥ 0 (an LP) | findRank, findLeadsTo, findCycles' ranks |
| Q4 equal columns | groups of columns equal on every row (equations between terms) | proveData's conjectures (data.ts), bridges to built-ins |
| Q5 split | the rows split by an atom column (depth 1) or two (depth 2), Q1/Q2 per part | inferLaws' guards and counterexample forms; disjunctive invariants nobody searches today |

This directory tests it: whether queries over tables of modest size recover what a strong external tool found
(Spacer's invariants for CHC-COMP, KoAT2's ranking functions for TermComp, the hand-written TIP lemmas) and what
gdp-wired's own searches find (the frontier corpus). It is a measurement: nothing in `core/`, `kernel/` or
`lean-kernel/` changed. Every figure below is from a run directory under `runs/modal/table/` (named beside it).

**What came out** (details and run directories below):

- *Within the templates the hypothesis holds.* Q1 + Q2 over tables of median 196 columns recover Spacer's invariant
  inductively on 213 of the 536 CHC tasks (187 of 204 single-bound tasks); with Q5, 237. The relations kept solve 252
  tasks under Z3's check; gdp-wired's kernel, given them, proves 25 (its step goals run out of budget on most).
- *Q3 recovers checked ranks* on 200 of the 576 termination tasks KoAT2 or another tool proves (KoAT2: 508), KoAT2's own
  function on 537 of its 3,652 MPRFs; the frontier corpus's 27 cycle and lemma items all agree with findRank, findCycles,
  cycleLemmas and discover, once Q3 carries findRank's choices.
- *Q4 finds the hand-written TIP lemmas*: 47 of 50, at up to 7 symbols a side.
- *Q5 doesn't make disjunctive invariants*: 8 of Spacer's 154 (1 by one atom, 5 by two); on the samples it looks like
  131, which is the false-positive problem in one number: Houdini drops 90 % of what the tables propose.
- *The GPU pays only for the termination box* (1.4 billion guard evaluations: 5.3 s against 232–303 s on the CPU twin);
  on the CHC and TIP tables, compile and the CPU work around it (interning) cost more than the pass. No GPU result
  disagreed with its CPU twin or the exact check.

## Method

| File | What |
| --- | --- |
| `table.ts` | The table, independent of the prover: exact rationals, terms (variables, sums and differences of up to 4, pairs with coefficients up to 3, products of two, `mod k`, a function's values), `observe(terms, samples)`, Q1 `equalities`, Q2 `bounds`, Q4 `equalColumns`, Q5 `split` (atoms: 0/1 columns, the values of a column of few values, signs of differences; `holes`: values a column skips inside its range, a disequality), Q3 `ranks` (small integer coefficients first, the fewest terms and then the smallest constants; past that an exact two-phase simplex over ℚ with rows added as they're violated) |
| `z3.ts` | Z3 5.3.1 as the outside oracle (one interactive process): the guards solved when sampling, the queries' answers checked |
| `chc.ts` | A CHC-COMP task: runs of the system, each step a model of one clause's constraint where the run is (Z3 solving the guard, some head values fixed at random first: solve.ts's guided runs with Z3 in place of the kernel's `grow`), the distinct states per predicate the rows; L0 = Q1 + Q2, L1 = L0 + Q5 one atom (+ holes), L2 = L1 + Q5 two atoms; whether L_k implies Spacer's interpretation (Z3); Houdini over each level by Z3 (the largest inductive subset), whether it is safe and implies Spacer's; `--kernel`: the kept relations handed to gdp-wired's prover as laws, no search (compare/chc/prof/given.ts) |
| `term.ts` | A termination task: runs from the entrypoint, each turn a model of a rule's guard (Z3), guards split into DNF; `--sampler z3+box`: a box of points for the rules the runs never took, filtered by the guard as a Handwired word program (CPU loop runner or GPU), each kept point checked exactly; per strongly connected component, columns = the positions the guards read, closed under the updates; Q3 KoAT2's way (per transition a rank strict on it, non-increasing on the others still unbounded; the constants from Z3's optimizer over the rules; checked by Z3, with Q1+Q2 invariants made inductive by Z3 where needed; the verifier's counterexample a new row); KoAT2's proof of the same ARI text beside it |
| `tip.ts` | A TIP problem: random valuations; terms by size from class representatives (QuickSpec); Q4 by fingerprints; the lemmas looked up; `(=> h c)` by Q5 |
| `frontier.ts` | research/frontier's cycle and lemma items, the existing search beside the table |
| `gpu.ts` | The GPU passes as Handwired loop programs (u32 word stages): columns (Q2 bounds and Q4 fingerprints of sparse linear columns), implies (Q5 on 0/1 columns as bitsets), box (guard filtering) |
| `summary.ts`, `gpu-summary.ts`, `term-tasks.ts`, `jobs.ts` | The tables below; the termination tasks with failures.ts's classes; the job files |
| `modal_table.py`, `run_gpu.py` | Modal runners: one container per job (2 vCPU, 4 GB; GPU: L4), all at once (Modal-only and historical) |

The check is Z3, not gdp-wired's kernel. "Recovered" is stated two ways: **on the samples** (L_k ⇒ Spacer's invariant;
L_k holds of every sample, but may hold of no invariant) and **inductive** (the relations Houdini keeps, an inductive
invariant Z3 checked, ⇒ Spacer's). Only the second is evidence; the first is what the hypothesis literally asks.

## 1. CHC-COMP: the 536 tasks Spacer answers sat and gdp-wired 0.20.0 doesn't

`runs/modal/table/chc1` (all 536, one container each; `chc1-summary.txt`). Sampling 10 s a task; Z3's per-check limit
10 s; a 400 s deadline for the Houdini stages. Spacer's class is gap.py's (`runs/modal/chc2/gap-v020.json`).

**Table size.** Per predicate: rows (distinct sampled states) median 6, p90 49, max 2,564; 579 of the 2,086 predicates
got no row (no run reached them: their table says `false`). Columns: L0 median 196 a predicate, max 1,156 (variables,
±1 sums of 2 up to 40 Int slots, of 3 up to 8, of 4 up to 6, pairs with coefficients to 3 up to 8, `mod 2, 3, 4` up to
12); L1 and L2 split over the variables only past 8 Int slots (median 20 and 16 columns, max 143), with at most 32
atoms (8 at depth 2). Relations per predicate: L0 median 259.5, L1 810, L2 856 (max 2,321, 5,237, 7,476).

| Spacer's class | tasks | on samples: L0 | L1 | L2 | none | inductive: L0 | L1 | L2 | none | safe: L0 | L1 | L2 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| bound of one value | 204 | 204 | 0 | 0 | 0 | 187 | 0 | 0 | 17 | 187 | 0 | 0 |
| a disjunction of three or more | 154 | 64 | 39 | 28 | 23 | 2 | 1 | 5 | 146 | 7 | 5 | 6 |
| more than three values in one atom | 71 | 47 | 17 | 2 | 5 | 10 | 6 | 0 | 55 | 14 | 4 | 0 |
| a yes/no guard | 23 | 17 | 6 | 0 | 0 | 0 | 4 | 0 | 19 | 4 | 1 | 0 |
| an existential (quantified) | 19 | 7 | 6 | 1 | 5 | 1 | 3 | 0 | 15 | 3 | 2 | 0 |
| a remainder | 16 | 12 | 1 | 0 | 3 | 4 | 0 | 0 | 12 | 5 | 0 | 0 |
| two values | 15 | 14 | 1 | 0 | 0 | 9 | 1 | 0 | 5 | 10 | 0 | 0 |
| boolean structure past 4,000 clauses | 13 | 7 | 1 | 0 | 5 | 0 | 0 | 0 | 13 | 0 | 0 | 0 |
| a disjunction of two (a counterexample's form) | 11 | 5 | 4 | 0 | 2 | 0 | 4 | 0 | 7 | 1 | 3 | 0 |
| no Spacer model in 60 s | 5 | 0 | 0 | 0 | 5 | 0 | 0 | 0 | 5 | 0 | 0 | 0 |
| a disjunction of two, outside the forms | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | 0 |
| a quotient | 2 | 0 | 0 | 0 | 2 | 0 | 0 | 0 | 2 | 0 | 0 | 0 |
| three values, coefficients outside the template | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 |
| **all** | **536** | **380** | **75** | **31** | **50** | **213** | **19** | **5** | **299** | **231** | **15** | **6** |

"On samples" is the first level whose relations imply Spacer's interpretation of every predicate; "inductive", the
first level whose Houdini-kept relations do; "safe", the first level whose kept relations make every query clause
unsatisfiable (an inductive invariant that solves the task, Spacer's or not). Every one of the 237 inductive
recoveries is also safe; 15 tasks are solved by a different invariant than Spacer's.

- **Within the templates the table recovers Spacer's invariant**: 187 of the 204 bound tasks and 9 of 15 two-value
  tasks, at L0 (Q1 + Q2), and those relations are inductive (Z3). These are mostly the Lustre tasks gap.py found stuck
  on a step goal the kernel leaves undecided: the table solves the search; the check is what fails (below).
- **Disjunctions don't come from samples.** On samples, 131 of the 154 disjunctive tasks are "recovered" (64 at L0
  already), but only 8 inductively (2 at L0, 1 at L1, 5 at L2). What implies Spacer's invariant on the samples is mostly
  relations the samples satisfy and no invariant does (a bound at the samples' maximum, a hole the runs didn't fill);
  Houdini drops them, and the disjunctions they stood in for are gone.

| The 154 disjunctions, by gap.py's shape | tasks | L0 | L1 (one atom) | L2 (two atoms) | more (none of these) |
| --- | --- | --- | --- | --- | --- |
| three or more linear literals | 70 | 1 | 0 | 0 | 69 |
| two linear literals beside yes/no values | 43 | 1 | 0 | 0 | 42 |
| yes/no values beside at most one linear literal | 41 | 0 | 1 | 5 | 35 |
| all | 154 | 2 | 1 | 5 | 146 |

So a split on one atom column recovers 1, a depth-2 tree 5, and 146 need more: a Q5 that splits on the atoms the
samples offer (the 0/1 columns, the values of a column of few values, signs of differences of two at ≤ 8 Int slots)
doesn't reach the case splits Spacer's interpretations make (values of a counter, `9 ≤ i0 ∨ i0 ≤ 7 ∨ i2 ≤ 8` for
each i0 = 0..10 on `s_split_21`), and where it does, the parts are too thin (median 6 rows a predicate).

**False positives.** Houdini drops 90.5 % of L0's 728,794 relations (kept 69,245), 89.3 % of L1's 1,423,877 and
90.4 % of L2's 1,663,206 (tasks that finished: 531, 511, 510). Of a sample of the dropped ones (44,193 at L0), Spacer's
invariant implies 114 (0.26 %): nearly every dropped relation is not implied by the invariant Spacer found, i.e. a
relation of the samples, not of the system. For the kernel, every one of those is a goal it would refute or leave
undecided; Houdini by Z3 is what makes the table usable at all.

**Cost (2 vCPU containers).** Wall per task median 41.44 s, p90 192.13 s, max 401.17 s, 39,937.9 s in all. Sampling
10 s (the budget); building the tables and answering the queries median 2,408.5 ms, p90 9,676 ms, max 37,633 ms; Houdini L0 median 1,139.5 ms, L1 12,696.5 ms, L2 13,865 ms, up to 210,384 ms; 5, 25
and 26 tasks out of time at L0, L1, L2.

**The kernel on what the table found** (`runs/modal/table/chc-kernel`, the 252 safe tasks rerun with `--kernel`: the
first safe level's kept relations, at most 300, stated as laws and given to `proveRule` with no search through
compare/chc/prof/given.ts, 55 s). 251 were safe again; 28 had more than 300 relations (median 60); of the 223 handed
over, the kernel proves 25 (checked), and leaves 198 unproven — mostly "the prover's time budget ran out at 41–106
hypotheses, 2 case splits deep", the step goal of gap.py's 332. By what gap.py found given Spacer's own invariant:

| given Spacer's invariant (gap.py) | the table's invariant: proven | not proven |
| --- | --- | --- |
| proven | 20 | 29 |
| step goal undecided | 4 | 164 |
| can't be stated | 1 | 4 |
| other | 0 | 1 |

25 tasks gdp-wired 0.20.0 doesn't solve are proven by the kernel from the table's invariant with no search (4 of them
where Spacer's invariant leaves the kernel undecided, 1 where Spacer's can't be stated). The table's kept set is not
minimized: it hands the kernel every inductive relation (median 60), each a hypothesis of every goal.

## 2. Termination: Q3 against KoAT2's ranking functions

The 576 tasks another tool proves terminating and gdp-wired doesn't (compare/term/failures.ts's classes, written per
task by `term-tasks.ts`: 447 ITS, 129 SV). Two runs: `term1` (Z3-solved runs from the entrypoint only) and
`term2` + `term2-redo` (the same, then the box for the rules the runs never took, on Handwired's CPU runner; 2^22 points
a rule at most). Both run KoAT2 2.7.0 on the same ARI text in the same container (`koat2 analyse --termination
--show-proof`, 60 s). A rank counts only when Z3 checks it on the rules (decrease and bound on its transition,
non-increase on the others still unbounded), with the Q1 + Q2 invariants Z3 made inductive where it needs them.

| class (failures.ts; † KoAT2 gave no proof) | tasks | ranked, runs only (`term1`) | runs + box (`term2`) | either | KoAT2 terminates | KoAT2 MPRFs (`term2`) | within the columns | the same as one found |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| ITS: a rank fitted to the params | 207 | 59 | 59 | 66 | 202 | 1,786 | 1,202 | 189 |
| ITS: a rank fitted to the params † | 10 | 0 | 0 | 0 | 0 | 1 | 1 | 1 |
| ITS: a rank the kernel refused, no param read | 60 | 26 | 28 | 33 | 59 | 348 | 339 | 98 |
| ITS: a rank the kernel refused † | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ITS: no rank fits the sampled turns | 8 | 5 | 4 | 5 | 8 | 230 | 230 | 8 |
| ITS: no rank fits † | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ITS: no turn sampled | 154 | 26 | 53 | 54 | 151 | 1,276 | 918 | 236 |
| ITS: no turn sampled † | 4 | 0 | 0 | 0 | 0 | 2 | 2 | 2 |
| ITS: out of time | 2 | 2 | 2 | 2 | 2 | 0 | 0 | 0 |
| SV: a rank fitted to the params | 95 | 29 | 0 | 29 | 65 | 9 | 6 | 3 |
| SV: a rank the kernel refused | 24 | 8 | 0 | 8 | 15 | 0 | 0 | 0 |
| SV: no rank fits the sampled turns | 6 | 1 | 0 | 1 | 2 | 0 | 0 | 0 |
| SV: no turn sampled | 4 | 2 | 0 | 2 | 4 | 0 | 0 | 0 |
| **all** | **576** | **158** | **146** | **200** | **508** (term1's KoAT2 run) | **3,652** | **2,698** | **537** |

"Within the columns": KoAT2's rank at each location reads only positions the guards read (closed under the updates),
after undoing KoAT2's renumbering when it eliminates variables. "The same": proportional to a rank found here at
every location KoAT2 lists. Both are over `term2`'s 417 tasks with a result.

- **The table finds a checked rank on 158 tasks from the runs alone, 200 with the box** (KoAT2: 508). The box matters
  where compare/term's gap analysis said it would: on "no turn sampled", 26 → 53 (on the 162 of that class rerun with the
  box's final code, `cpu-term3`: 51, `gpu-term3`: 52, against `term1`'s 28). Guard solving alone (Z3 runs) does not
  reach the components no run from the entrypoint gets to: on those 162, 290 of 413 components had no sampled turn in
  `term1`, 193 of 401 with the box.
- **Columns restricted to what the guards read**: kept 13,644 of 55,823 argument positions (`term2`). The
  217 + 95 "fitted to the params" (failures.ts) become 59 + 29 ranked — the restriction removes the params, but 1,202 of
  KoAT2's 1,786 MPRFs in that class read only those columns; a third read positions no guard reads (why, case by case, was not examined here), so the column choice can't be
  "what the guards read" alone.
- KoAT2's 431 proofs use depth-1 ranking functions or none (failures.ts); Q3 recovers KoAT2's own function (up to a factor) for 537 of its
  3,652 MPRFs: the table finds *a* rank more often than *KoAT2's* rank.
- `term2` lost tasks to its own cost: 159 jobs ran out of their 480 s (141 still sampling, 18 in the invariants), 128 of the
  129 SV tasks among them; `term1` had 21. Hence "either".
- Cost: `term1` wall per task median 23.435 s (46,529.9 s in all); Z3 refused 32,439 rank candidates, 6,242
  counterexample rows were added, 915 ranks accepted (536 needing the invariants). `term2`: 21,818 refused, 3,028
  counterexample rows, 572 accepted (159 needing invariants).


## 3. TIP: Q4 on the 27 problems with hand-written lemmas

`runs/modal/table/tip2` (one container each; `tip1` the first run). 100 random valuations, a size-uniform generator
(depth or length 0..7), 3 variables of a type a lemma or the goal uses 3 of, terms up to 8 symbols from class
representatives, 500 s. The sample file has 27 problems and 50 lemmas (not 47).

| Lemma kind | found | of |
| --- | --- | --- |
| equation (Q4: both sides in one class) | 34 | 35 |
| boolean, `t` (Q2 on a 0/1 column: constant true) | 3 | 3 |
| disequation, `distinct (linA a) (linB b)` (the `=` column constant false) | 1 | 1 |
| implication, Q5 depth 1 (`sorted xs ⇒ sorted (insert y xs)`, injectivity of `linA`, `linB`, …) | 6 | 7 |
| implication of two, Q5 depth 2 (`nat_max_assoc`) | 2 | 2 |
| disjunction `leq x y ∨ leq y x` (Q5: ¬a ⇒ b) | 1 | 1 |
| outside the grammar | 0 | 1 |
| **all** | **47** | **50** |

The sides found go to 7 symbols (`toNat`/`plus`/`times` distributivity on binary numbers, `(-2 (plus2 x y) (plus2 x z))
= (-2 y z)`, `butlast (xs ++ y :: ys) = xs ++ butlast (y :: ys)`, `rev (l ++ [z]) = z :: rev l`), the 7 bridges to the
built-ins included (`== x y = (x = y)`, `<=2 (S x) (S y) = <=2 x y`, the `toNat` lemmas). Missed: `isPermutation ys zs ⇒
…` (its hypothesis holds on 1 of 100 rows, under the 5 a part needs), `prop_02`'s lemma (4 variables of one type and an
`ite`, 9 symbols: outside the grammar), and `prop_35`'s `qexp x y z = exp x y · z` (the evaluator overflows its stack on
`exp`'s values; enumeration complete only to size 5). "Found" means both sides land in the same class, so the equation
is in the congruence closure of the ones emitted, not that it was printed. With only the goal's types given 3
variables (`tip1`), 44 of 50.

**False positives.** Up to 300 emitted equations a problem, checked again on 1,000 fresh valuations: 699 of 7,720
false (9.1 %); at the largest size reached, 658 of 7,456 (8.8 %); `tip1`'s shorter lists: 1,213 of 7,955 (15.2 %).

**Cost.** Terms evaluated median 19,737 a problem (max 138,450), classes median 4,230 (max 38,872); complete to size 8
on 24 of 27; wall median 29.68 s, max 713.64 s, 3,010.4 s in all (the 1,000-valuation recheck included).

## 4. The frontier corpus: does the table find what findRank, findCycles, cycleLemmas and discover find?

`runs/modal/table/frontier4` (27 jobs, each running the existing search and then the table on the same samples): all
27 cycle and lemma items agree — 17 the same answer, 7 equivalent or stronger and valid (checked by the kernel for
loops and liveness, by a held-out grid 1.5× wider for claims over functions), 3 containing the existing lemma among
extras. McCarthy's 91 (Q3: 100 − n), Ackermann ((m, n) in order), the exchange (11·x + 2·y by the exact LP; the box
of 4 fails), counting to a square (n·n − i with a product column; the linear fit −i + 4n + 12 refused first),
the pyramid (Q1: 6f = 2x³ + 3x² + x), area (f = x·x), backoff (1 ≤ f ≤ 64). Getting there took findRank's own choices
in the rank query: coefficients boxed to ±4 first, the rational vertex rounded before scaling, the least constant,
turns grouped by which values fall, weak turns dropped once a component lowers them, one product column at a time
(`frontier2`: 9 of 27 failed without them; `frontier3`: 3). The table is slower there: three phases 16,740 ms against
2,693 ms, Ackermann 45,581 ms against 502 ms (the exact BigInt simplex over 10k–25k transitions).

## 5. The GPU passes (Handwired word programs on an L4)

`runs/modal/table/gpu-l4` (on `NVIDIA L4, 610.57.04`, one container a job) against `runs/modal/table/cpu-twin` (the same
jobs on 2-vCPU containers, the same word programs on Handwired's CPU loop runner); `gpu-l4-summary.txt`. Nothing the GPU
returned is used unchecked: every output is compared with the exact CPU computation and with the CPU twin.

**Disagreements: none.** CHC columns: GPU vs its JavaScript twin 0 columns, GPU bounds vs the exact BigInt table 0,
fingerprint groups that split on the exact recheck 0 (49,328 groups, 49,328 exact); implications vs JavaScript 0 pairs.
TIP: the GPU's partition after the recheck equals the CPU's on 26 of 26 problems, 0 false merges.
Termination box (`gpu-term3` against `cpu-term3`, the box's final code): documents whose masks differ between the GPU
and its CPU twin in the same container 0; points the GPU kept 161,060,130, of which the exact evaluator (ari.ts, BigInt)
refuses 0. The answers agree on 153 of the 156 tasks both finished (the Z3 runs before the box are timed, so their
samples differ between runs).

| Pass | Work | GPU (L4) | CPU |
| --- | --- | --- | --- |
| CHC columns (Q2 bounds + Q4 fingerprints), 40 largest tables (359 predicates, columns median 960, rows median 14, max 2,564) | | compile 27,933 ms + run 1,386 ms (device setup median 389.5 ms a task) | plain JavaScript 998 ms; exact BigInt table 1,951 ms; Handwired CPU twin 32,460 ms |
| CHC implications between atoms (Q5 on bitsets) | | compile 8,256 ms + run 1,155 ms | JavaScript 26 ms; CPU twin 293 ms |
| TIP Q4 fingerprints of the last size's columns (26 problems, columns median 11,603, max 104,595) | | intern 142,022 ms (CPU) + compile 10,378 + run 759 + group and recheck 41,290 ms | the values' text as the key: 125,833 ms; CPU twin run 19,755 ms |
| Termination box (162 "no turn sampled" tasks; 947 rules boxed, 2,738 skipped; 1,414,188,777 points) | | compile 41,357 ms + run 5,299 ms (setup median 441.5 ms a task) | CPU twin in the same container 302,855 ms; on CPU containers 231,907 ms (compile 241 ms) |

**Where it doesn't pay.**
- *Q2 bounds and Q4 on CHC tables*: the tables are small (rows median 14), and shader compile (27,933 ms over the 359
  predicates, one shader each) is 28× the plain JavaScript pass (998 ms); the GPU's run alone (1,386 ms) doesn't beat
  JavaScript either. The work isn't there.
- *Implications on bitsets*: 26 ms of JavaScript for all 40 tasks; nothing to win.
- *TIP fingerprints*: the GPU hashes ids, so every value is first interned on the CPU — 142 s, more than the text keys
  it replaces (126 s). And fingerprinting is not the cost: during enumeration, evaluating the terms took 1,806,349 ms
  against 207,762 ms of fingerprints (10 %); a GPU that hashed for free would save at most that. The evaluator
  (recursive TIP functions over datatypes) is what would have to move, and it isn't a word program.
- *Where it pays: the termination box.* 1.4 billion guard evaluations: the GPU's run is 5.3 s against 232–303 s on
  the CPU twin (44–57×), and 46.7 s with shader compiles (41.4 s, one per rule). It is the one pass with millions of
  cells; still, a task's wall is the Z3 runs, the invariants and the rank checks (GPU containers' median 27.78 s a task
  with the twin beside, CPU 23.955 s), so the box saves seconds of 20.
- The exact recheck is as costly as the pass for Q2 (checking a bound is computing it); for soundness it is not
  needed — a wrong bound is a candidate Houdini or the kernel refuses — so "never trusted" costs a CPU pass here.


## 6. What didn't fit the five queries, and why

- **Existentials and divisibility (CHC: 19 quantified, 16 remainder, 2 quotient).** A `mod k` column is in the grammar
  (Q2 on it gives `x mod 2 = 0`), and it recovers 4 remainder tasks inductively; but Spacer's projections (`∃y. x = 2y
  + …`) are not a column of any term over the state, and gdp-wired's laws can't state a remainder anyway (given.ts drops
  them: "unstated: mod").
- **Disjunctions past depth 2 (146 of 154).** Q5 splits on atoms the samples offer; Spacer's case splits are over
  values and thresholds the samples rarely isolate, and the parts are a handful of rows. A disjunction is a Q5 *query*
  only once its atoms are known: the atom choice is a search the table doesn't do (Spacer gets it from
  counterexamples, not samples).
- **Lexicographic ranks needing more than "decrease on one, don't rise on the rest".** `toy3`'s two resets (y := 0
  once) are each taken once; no linear rank is non-increasing on both, KoAT2 bounds them by its time bounds instead.
- **Ranks with a fitted constant.** Q3 on samples gives −x + 143 where the rule says n − x; the constant has to come
  from the rule (Z3's optimizer over the guard here, the least constant in findRank), not from the rows.
- **Function-typed arguments, `ite` and 4 variables of a type (TIP).** Outside the term grammar.
- **Sampling, not querying, is the limit.** CHC: 579 of 2,086 predicates never reached by a run; termination: a third
  of the components (term1: 690 of 1,337) have no sampled turn from the entrypoint. The queries need rows that exist;
  guard solving (Z3) fixes "a turn pinned by an equation" but not "a location no run reaches".
- **The check.** The table's recoveries within the templates are exactly where gdp-wired's kernel leaves the step goal
  undecided (164 of the 223 handed to it). A unified search doesn't change that bottleneck.

## 7. Proposal (not implemented): one search API in core/

*This is a proposal from the measurements above, not something this experiment built into the library.*

```ts
// core/table.ts
type Samples = {rows: Row[], pairs?: {strict: Pair[], weak: Pair[]}}          // states, transitions, argument tuples
type Grammar = {vars, sums?: number, coef?: number, products?: boolean, mods?: bigint[], fns?: Fns, maxSize?: number}
observe(grammar, samples): Table                                               // columns × rows, exact
table.equalities(): Lin[]          // Q1
table.bounds(cols?): Lin[]         // Q2
table.rank(locs, opts): Ranking[]  // Q3, best first: the ±4 box, fewest terms, least constant; then the exact LP
table.equal(): Term[][]            // Q4
table.split(atoms, depth): Rel[]   // Q5
// and one loop the four searches share: candidates → kernel (Houdini, counterexample → new row) → kept
refine(candidates, kernelCheck, toRow): Rel[]
```

Each search keeps its sampler and its kernel loop and hands its grammar and query to the table:

| Search | Its sampler stays | Replaced by the table | Lines that go (Explore's count of the search part) |
| --- | --- | --- | --- |
| `inferLaws` (core/infer.ts) | runs, perturbed steps | the template enumeration and its max-over-rows (Q2 over a grammar), guards (Q5) | ≈ 285 of 511 |
| `findRank`, `findLeadsTo`, `cycleLemmas` (core/cycles.ts) | runs, grids | the box LP, the exact simplex, lexicographic elimination (Q3), the exact fits and bounds of cycleLemmas (Q1/Q2) | ≈ 395 of 980 |
| `discover` (core/discover.ts) | x = 0..40, folds over random lists and trees | linear candidates and Newton differences (Q1 over [1, x, x², x³]), bounds (Q2) | ≈ 205 of 442 |
| `proveData`'s conjectures (core/data.ts) | random values | the enumeration by representatives and the fingerprint grouping (Q4) | ≈ 170 of 1,676 (its rewrite pruning, ≈ 65, stays) |

About 1,055 lines of search would become calls into one module of about 430 (table.ts here is 433, Q3's LP
included). What the measurements say it must keep from the searches it replaces: findRank's box-then-LP order and
least-constant choice (frontier2's 9 failures without them), the kernel's counterexamples as new rows (here: 3,028
counterexample rows in term2's ranks), a sampler per domain (guard solving where inputs are pinned), and the Houdini
loop behind every query — on the CHC tables Houdini drops 90 % of what the table proposes.

What it would not buy: disjunctive invariants (8 of 154), and the kernel's step goals on wide transitions, which the
table can't help with. GPU: keep the passes CPU-side (section 5) until a domain has tables of millions of cells.

## Runs

| Run | What |
| --- | --- |
| `chc1` | the 536 CHC tasks (`chc1-summary.txt`) |
| `chc-kernel` | the 252 solved ones again, the kept relations given to gdp-wired's prover |
| `term1` | the 576 termination tasks, Z3 runs only |
| `term2`, `term2-redo` | the same with the box for the rules the runs never took, KoAT2's renumbering read (`term2-redo`: the 252 that ran out of time or boxed past the deadline, with the box stopped at 40 % of it) |
| `tip1`, `tip2` | TIP Q4 |
| `frontier1`–`frontier4` | the frontier sanity check (`frontier4` the final) |
| `gpu-l4`, `cpu-twin` | the GPU passes and their CPU twin (CHC 40, termination 162 with the first box, TIP 27) |
| `gpu-term3`, `cpu-term3` | the termination box again (relevant positions only, the deadline), GPU and CPU twin |
| `*-smoke*`, `*-stopped` | smoke runs, and runs stopped for a bug (the box without a deadline), kept for the record |

    bun research/table/jobs.ts chc && modal run research/table/modal_table.py --jobs research/table/jobs/chc.json --out runs/modal/table/chc1
    bun research/table/summary.ts chc runs/modal/table/chc1
    bun research/table/summary.ts term runs/modal/table/term2 runs/modal/table/term2-redo
    modal run research/table/run_gpu.py --jobs research/table/jobs/gpu-all.json --out runs/modal/table/gpu-l4
    bun research/table/gpu-summary.ts runs/modal/table/gpu-l4 runs/modal/table/cpu-twin
