# The frontier, round 2: what the benchmarks leave

Round 1 (`research/frontier/`) went from 0 to every item. Round 2 is the next target, taken from the benchmarks:
tasks of CHC-COMP 2026's LIA-Lin track, TIP 2015, TermComp's integer transition systems and SV-COMP's termination set
that gdp-wired's benchmark runs at 0.21.0 left unproven and another tool solved. Each item stands for a group of
such tasks that fail for one reason, and the README says which tasks and how many, from which run.

    bun research/frontier2/jobs.ts > jobs.json                        # one job per item and prover
    python3 modal/run.py --jobs jobs.json --out runs/corpus2/<name>    # 168 jobs, 2 vCPU each
    bun research/frontier2/score.ts --from runs/corpus2/<name>         # the table and the score
    bun research/frontier2/score.ts [--track t] [--limit 180]         # or in one process, each item in a child

## The items

The interface is round 1's: `corpus.ts` exports `corpus: Item[]`, each `{id, track, removed, broken?, today, frontier}`.
`today` is the library's prover alone and `frontier` the library with its search. Each returns a `Verdict`, and an
item counts when it is proven and checked by the kernel. A broken variant (`broken`: the id of its item) counts when
neither proves it. `score.ts` takes round 1's flags (`--one`, `--from`, `--track`, `--not`, `--shard`, `--json`), so
a search track's score on round 1 runs on round 2 unchanged. Round 2's items also carry `source` (the benchmark, the
task, the group) and `truth` (how the claim was checked outside the library).

**Faithful.** An item is the task itself. The task's file is vendored in `tasks/`, byte for byte, at its benchmark's
pinned commit, and read by the translation its benchmark run used:
- CHC: `compare/chc/translate.ts`'s `build`. The law (error is never reached) is the system's satisfiability.
- TIP: `compare/tip/translate.ts`. It agrees with TIP's evaluator on random values.
- ITS and SV: `compare/term/translate.ts`'s `gdp` translation. One loop halts from every start exactly when the task
  terminates. The stronger `scc` statement isn't used.

**Searches**, as each benchmark ran them:
- CHC: `inferLaws` with a counted budget of 60 s.
- TIP: `proveData` with 57 s.
- Termination: `findRank` with 51 s, then solve.ts's recheck of every tree.

**Unsat CHC tasks** (groups H and I) claim the error is reached. Such an item is proven only when the library's
verdict carries a run that `checkDerivation` confirms step by step against the CHC.

**Refused definitions.** Three TIP problems are items although the library refuses their definitions: a heap sort's
`toList`, and McCarthy's nested `m` on an Int, twice. The statement is TIP's. Their verdict is not proven, with the
refusal as `why`, as in round 1's definitions that don't terminate.

**Broken variants.** Each item has one: the same task changed so that its claim is false. For the Lustre tasks it is
the benchmark's own mutant where there is one; otherwise a change to the query, the goal or a guard, said in its id.

**Checked true.** Every item and broken variant was checked outside the library:
- CHC: Spacer (z3 5.3.1), Golem 0.9.0 and Eldarica 2.3 at 200 s each (`truth-chc.json`, `runs/corpus2/truth-chc`).
- TIP:
  - Vampire 5.1.0 and cvc5 1.4.2 with conjecture generation at 600 s, through the benchmark's runner
    (`runs/corpus2/truth-tip-tools`);
  - TIP's own evaluator at 5,000 random values (`tipeval.ts`, `truth-tip.json`, `runs/corpus2/truth-tip-eval`);
  - `compare/tip/solve.ts` on each broken variant.
- Termination:
  - KoAT2 2.7.0 and LoAT 0.9.10 (`truth-term.json`, `runs/corpus2/truth-term`), and SV-COMP's own expected verdicts;
  - lassos confirmed by `compare/term/ari.ts`'s `checkLasso` (`truth-term-lassos.json`, `runs/corpus2/truth-term-lassos`);
  - one rank checked by z3 (`runs/corpus2/truth-polyrank1`).

**Groups.** `groups_chc.py`, `groups_tip.py` and `groups_term.ts` count each group from the runs named below. Their
output is in `runs/corpus2/groups-chc.txt`, `groups-tip.txt`, `groups-term.txt`, `failures-its-term-gdp.txt` and
`failures-sv.txt`, with every task listed.

## The score at 0.21.0

`runs/corpus2/baseline-0.21.0` (at 479bf81, the 0.21.0 release; 168 jobs on boat VMs, 2 vCPU each, every run killed
at 200 s; the table: `runs/corpus2/baseline-0.21.0.md`):

| Area (track) | Items | Today | Frontier | Broken variants refused |
| --- | --- | --- | --- | --- |
| step goal | 2 | 0 | 0 | 2 / 2 |
| search | 2 | 0 | 0 | 2 / 2 |
| disjunction | 3 | 0 | 1 | 3 / 3 |
| wide atom | 2 | 0 | 0 | 2 / 2 |
| projection | 2 | 0 | 1 | 2 / 2 |
| derivation | 3 | 0 | 0 | 3 / 3 |
| lemma | 5 | 0 | 0 | 5 / 5 |
| generalization | 3 | 0 | 0 | 3 / 3 |
| induction | 2 | 0 | 1 | 2 / 2 |
| integer recursion | 2 | 0 | 0 | 2 / 2 |
| termination | 1 | 0 | 0 | 1 / 1 |
| nested recursion | 3 | 0 | 0 | 3 / 3 |
| rank | 5 | 0 | 0 | 5 / 5 |
| nonlinear rank | 4 | 0 | 0 | 4 / 4 |
| sampling | 3 | 0 | 0 | 3 / 3 |
| all | 42 | 0 | 3 | 42 / 42 |

**Proven by the library's own search, which the benchmark runs didn't prove:**
- `chc/D/reve 015`: in 16,748 ms, with 8 invariants, among them case splits such as `loc is p1 → i1 + 1 <= i3 → i0 +
  1 <= i2`.
- `chc/F/break_safe.c-1`: in 19,863 ms, with 30 invariants and no existential.
- `tip/tip2015/list_PairOdds`: in 141,925 ms of wall time. The 57 s budget is counted work, which on boat ran past
  the benchmark's 60 s of wall time.

On the two CHC tasks, the benchmark's `compare/chc/solve.ts` gave `inferLaws` what was left of 60 s of wall time after
its own random and guided runs (13 s), with the states those runs reached as samples. The corpus runs `inferLaws` alone
on a counted budget, and it finds the invariants. So for those two the group's reason was not the obstacle: the
benchmark pipeline's budget and samples were. Each of their groups keeps an item no search proves (`chc/D/gulwani_fig1a`,
`chc/F/HOLA 38`). `list_PairOdds` stands for its group, more time, as intended.

Unproven:
- 4 runs were killed at 200 s, read as timeouts: the frontier of `lemma_09`, `prop_84` and `bin_nat_plus`, and the
  templates (`today`) of `Alternate`.
- Every other run ended by itself.

## The areas and the tasks they stand for

### CHC-COMP 2026 LIA-Lin (`chc.ts`, 14 items)

**How the groups are counted.** Tasks Spacer, Golem or Eldarica solves within 60 s and gdp-wired doesn't, from the
0.20.0 gap analysis (`runs/modal/chc2/gap-v020.json`, `compare/chc/prof/gap.py`). They are grouped as
`candidates-chc.md` groups them:
- by Spacer's invariant's class;
- by whether the kernel proves it when given (`prof/given.ts`);
- Lustre or not.

Kept are those still unsolved at 0.21.0 (`runs/modal/infer/chc-final`, the CHANGELOG's 0.21.0 figure, 382 solved).
The 0.20.0 counts reproduce `candidates-chc.md`'s except F: 42 here, 45 there, because 3 tasks there sit in both D
and F and are counted once here, in D.

| Group | Reason | 0.20.0 | Left at 0.21.0 | Of those, solved on boat (`runs/backends/chc-gdp`) | Items |
| --- | --- | --- | --- | --- | --- |
| A | Lustre: an invariant within the templates whose step goal the prover leaves undecided over the wide transition, even given | 195 | 195 | 0 | FIREFLY_1, MESI_i3_e1_447_e3_1180 |
| B | Lustre: within the templates, proven once given, not found by the search | 41 | 39 | 2 | hysteresis_2 |
| G | not Lustre: within the templates, not found | 16 | 15 | 1 | s_split_34 |
| C | a guard over several yes/no values (a program counter in bits) beside at most one linear literal | 38 | 38 | 0 | simple.c |
| D | a clause of two or more linear literals | 116 | 113 | 0 | reve 015, gulwani_fig1a |
| E | an atom over more than three values | 71 | 71 | 1 | three_dots_moving_2, loop2 |
| F | a remainder, a quotient, or an existential kept from a projection | 42 | 34 | 0 | break_safe.c-1, HOLA 38 |
| H | unsat, Lustre: a short derivation of false the runs don't find | 273 | 273 | 0 | durationThm_1_e1_197 |
| I | unsat, the others: a derivation the runs don't find (one of 10,002 steps) | 30 | 30 | 1 | O0_terminator_01, s_split_01 |
| - | the rest: Boolean structure past 4,000 clauses, no Spacer model, other classes | 17 | 17 | 0 | none |
| all | | 839 | 825 | 5 | |

| Item | Task | What the proof needs | Broken variant | Checked |
| --- | --- | --- | --- | --- |
| chc/A/FIREFLY_1 | lustre/FIREFLY_1_000_001 (55 Int, 22 Bool slots) | Spacer's one-slot invariant b13; the search stops on its step goal, undecided | the benchmark's mutant FIREFLY_1_e1_1092, unsat | Spacer and Golem sat, the .yml sat; mutant: Spacer and Golem unsat (Golem: 4 steps) |
| chc/A/MESI_i3_e1_447_e3_1180 | lustre/MESI_i3_e1_447_e3_1180_000_001 (44 Int, 13 Bool) | b8 and i6 <= i4; the search stops on i2 + 1 <= b8's step goal | the benchmark's MESI_i3_e1_447_e2_1098, unsat | Spacer, Golem, Eldarica sat; sibling unsat (Golem: 3 steps) |
| chc/B/hysteresis_2 | lustre/hysteresis_2_000_001 | b9, and 1 <= i1 or not b1 | the query (not O) as O | all three sat; variant: all three unsat |
| chc/G/s_split_34 | aeval multi-phase/s_split_34 | −100 <= i0 <= 100, −100 <= i0 + i1 <= 100, −1 <= i1 <= 1 | the bound 100 as 99 | Spacer, Eldarica sat; variant: Spacer, Golem unsat (Golem: 103 steps) |
| chc/C/simple.c | ctigar/simple.c_000_001 | five pc-bit clauses (`not b2 or not b3`, `i0 <= i1 or not b2`, ...) | the query at a pc the program reaches | all three sat; variant: all three unsat (Golem: 10 steps) |
| chc/D/reve 015 | reve/015-horn | clauses of three linear literals (`i0 + 1 <= i2 or i1 <= i3 or i2 + 1 <= i0`) | the query off by one | all three sat; variant: all three unsat |
| chc/D/gulwani_fig1a | ctigar/gulwani_fig1a.c_000_001 | `1 <= i1 or i0 + 50 <= 0 or not b0` and the pc clauses | the query at a reached pc | all three sat; variant: all three unsat (Golem: 11 steps) |
| chc/E/three_dots_moving_2 | extra-small-lia/three_dots_moving_2 (843 bytes) | i1 + i2 <= 2·i0 + i3, i1 <= i2 + i3, i0 <= i1 | the dots may meet | Spacer, Golem sat; variant: all three unsat |
| chc/E/loop2 | llreve clausified/loop__loop2_000_001 | i0 + i5 = i2 + i3 + 1 (four values) and i1 = i4 | equal results queried | all three sat; variant: all three unsat |
| chc/F/break_safe.c-1 | llreve/break_safe.c-1 | Spacer's projection keeps an existential (49 clauses) | equal results queried | all three sat; variant: all three unsat |
| chc/F/HOLA 38 | HOLA/38.c | i mod 2 | the check at odd i too | Spacer, Eldarica sat; variant: all three unsat (Golem: 21 steps) |
| chc/H/durationThm_1_e1_197 | lustre/durationThm_1_e1_197 (unsat) | Golem's derivation of 3 steps | the benchmark's original durationThm_1, sat | all three unsat, the .yml unsat; original: all three sat |
| chc/I/O0_terminator_01 | svcomp O0_terminator_01 (unsat) | a derivation of 4 steps from a start of at least 100 | start at most 0, error past 100: sat | all three unsat; variant: all three sat |
| chc/I/s_split_01 | aeval-unsafe/s_split_01 (unsat) | a derivation of 10,002 steps (a loop summarized: acceleration) | the second counter from 4,999: sat | Golem unsat (10,002 steps), the .yml unsat; variant: no solver in 200 s, an inductive invariant checked by z3 (`tasks/chc/s_split_01_000.broken.invariant.smt2`, three unsat) |

Group A is the step-goal area. Given Spacer's invariant, the kernel leaves its step goal undecided at the per-goal
budget on all 195; the rule is one predicate over tens of slots, and the step's case splits are over all of them.
B and G are search misses on invariants the templates contain. C, D, E and F are invariants outside the templates:
- C and D: disjunctive invariants;
- E: atoms over four or more values;
- F: projections and remainders.

H and I are refutations no run finds.

### TIP 2015 (`tip.ts`, 15 items)

At 0.21.0, 140 of TIP's 492 theorems are proven (`runs/modal/arith/tip-gdp`, and the same 140 on boat,
`runs/backends/tip-gdp3`). The groups by reading are compare/tip/README.md's: 20 failures drawn at random and
classified by reading each problem (`lemmas-sample30.json`). Their size is known only on that sample, and is given
as such. The other groups are counted from the 0.21.0 run. The other tools' column is `runs/modal/tip/full2` at 60 s.

| Group | Tasks | Unproven at 0.21.0 | Another tool proves at 60 s | Items |
| --- | --- | --- | --- | --- |
| an equation about another function | 6 of the 20 read | 6 | 1 | prod/lemma_09, isaplanner/prop_53 |
| a conditional lemma | 5 of the 20 read | 5 | 0 | prod/prop_14, prod/prop_42 |
| a theory of several lemmas | 6 of the 20 read | 6 | 0 | tip2015/sort_nat_ISortPermutes |
| an accumulator's generalisation | 2 of the 20 read | 2 | 1 | prod/prop_35, isaplanner/prop_49 |
| induction on two lists together | 1 of the 20 read | 1 | 1 | isaplanner/prop_84 |
| more time (proven only at 300 s, `diag-t300`) | 7 | 6 | 6 | tip2015/list_PairOdds |
| `add3acc` by well-founded recursion (`weird_nat_add3acc_*`) | 9 | 9 | 3 | tip2015/weird_nat_add3acc_spec |
| binary numbers (`bin_*`) | 16 | 14 | 2 | tip2015/bin_nat_plus |
| powers and factorials | 4 | 4 | 1 | tip2015/nat_pow_pow |
| termination not proven (a measure's decrease needs a lemma: `toList` 16, `idiv` 12, ...) | 91 | 91 | 13 | tip2015/sort_HSortCount |
| recursion on an Int (no measure; McCarthy's nested `m` is 2 of them) | 14 | 14 | 1 | tip2015/mccarthy91_M1, mccarthy91_M2 |

| Item | Track | What the proof needs | Broken variant | Checked true |
| --- | --- | --- | --- | --- |
| tip/prod/lemma_09 | lemma | `++` associative and `rev (l ++ [z]) = z :: rev l` | `rev (y ++ x)` | Vampire 0.04 s, cvc5cg 0.02 s |
| tip/isaplanner/prop_53 | lemma | the bridges for `==` and `<=`, then the count of an insertion | `sort (n :: xs)` | TIP's theorem, evaluator |
| tip/prod/prop_14 | lemma | `sorted xs ⇒ sorted (insert y xs)` | `sorted (1 :: isort x)` | TIP's theorem, evaluator |
| tip/prod/prop_42 | lemma | `elem x z ⇒ elem x (union y z)` | the implication reversed | TIP's theorem, evaluator |
| tip/tip2015/sort_nat_ISortPermutes | lemma | a theory of permutations | `zero :: xs` as the permuted list | TIP's theorem, evaluator |
| tip/prod/prop_35 | generalization | `qexp x y z = exp x y · z`, · associative and commutative | `qexp y x 1` | TIP's theorem, evaluator |
| tip/isaplanner/prop_49 | generalization | `butlast (xs ++ y :: ys) = xs ++ butlast (y :: ys)`, past 8 symbols | `butlastConcat ys xs` | Vampire 0.31 s, cvc5cg 0.11 s |
| tip/tip2015/weird_nat_add3acc_spec | generalization | the accumulator's generalisation over add3acc's own recursion | `z + 1` on the right | Vampire 0.17 s |
| tip/isaplanner/prop_84 | induction | induction on ys with cases of xs (two lists together) | `len zs` in take and drop | Vampire 0.31 s, cvc5cg 0.09 s |
| tip/tip2015/list_PairOdds | induction | more time (137.68 s in `diag-t300`) | `evens` for `odds` | Vampire 0.91 s |
| tip/tip2015/bin_nat_plus | integer recursion | `toNat (s x) = 1 + toNat x`, + associative and commutative | `toNat (s y)` | TIP's theorem, evaluator |
| tip/tip2015/nat_pow_pow | integer recursion | x^(y·z) = (x^y)^z through recursive times and plus | `x^(y + z)` | TIP's theorem, evaluator |
| tip/tip2015/sort_HSortCount | termination | `toList (hmerge p q)`'s decrease: the size of a merge, a lemma about another function | `count x (x :: xs)` | TIP's theorem, evaluator |
| tip/tip2015/mccarthy91_M1 | nested recursion | `m`'s termination: a call in its own argument, on an Int (101 − n below 101) | `n <= 102` (m 102 = 92) | TIP's theorem, evaluator |
| tip/tip2015/mccarthy91_M2 | nested recursion | the same, then `m n = n − 10` above 100 by unfolding | `n >= 100` (m 100 = 91) | Vampire 11.42 s |

The truth notes in the table:
- "Vampire" and "cvc5cg" are proofs within 600 s (`runs/corpus2/truth-tip-tools`).
- "TIP's theorem, evaluator": no outside prover proves it within 600 s. The claim is the benchmark's own (a TIP
  theorem, not in its `false/`), and TIP's evaluator held at 5,000 random values with none out of fuel
  (`runs/corpus2/truth-tip-eval`).

Monomorphised items: for `lemma_09`, `prop_49`, `prop_84` and `list_PairOdds` the translation takes the goal's sort
variable at the naturals. No function of theirs reads an element, so this is the same claim by parametricity.

Every broken variant was refuted:
- TIP's evaluator found a counterexample for all 15.
- `compare/tip/solve.ts` refuted 12, each with a counterexample the evaluator confirms. The other 3 have definitions
  the library refuses.

### TermComp ITS and SV-COMP termination (`term.ts`, 13 items)

The classes are `compare/term/failures.ts`'s. They cover terminating tasks that another tool proves and gdp-wired
doesn't (neither translation), by where `gdp-scc`'s rank search stopped and what KoAT2's proof used:
- ITS: gdp-wired from `runs/backends/term-gdp` (boat, just before the 0.21.0 release commit) and `gdp-scc` from
  `runs/modal/term/gdp2`; the other tools from `full1` and `koat-fix1`, KoAT2's proofs from `diag-koat`. Output in
  `runs/corpus2/failures-its-term-gdp.txt`.
- SV: `runs/modal/term/sv2` and `sv3`. Output in `runs/corpus2/failures-sv.txt`.

| Class | ITS | SV | Items |
| --- | --- | --- | --- |
| a rank fitted to the params (the runs' start values, constant along a run, read by the rank the LP fits; the kernel refuses it) | 207 (+10 with no KoAT2 proof) | 95 | Continue1, p-60, polyrank1, 2Nested-1 |
| no turn sampled (99 several fresh values bounded together, 46 an input an equation pins, 6 a constant past 64, 3 both) | 154 (+4) | 4 | AProVEMath, ListReverseCyclicList, WhileFalse |
| a rank the kernel refused, no param read | 60 (+1) | 24 | AckR, Alternate, toy3, Piecewise, McCarthy91_Iteration |
| no rank fits the sampled turns | 8 (+1) | 6 | Toulouse-BranchesToLoop-2 |
| out of time | 2 | 0 | none |
| all | 447 | 129 | |

On the `gdp` translation alone, 559 ITS and 169 SV tasks are terminating by another tool and not proven
(`groups_term.ts`, `runs/corpus2/groups-term.txt`). `gdp-scc`, a stronger statement, proves 112 and 40 of those.
KoAT2's proofs read in `diag-koat` use multiphase ranks of depth 0 (77) or 1 (354), none deeper.

| Item | Track | The loop | What the proof needs | Broken variant | Checked |
| --- | --- | --- | --- | --- | --- |
| term/Continue1.jar-obl-8 | rank | `x := 0; while x < 20: x := x + 1` (split at 10) | 20 − x, reading no param | x < 20 dropped | KoAT2 (20 − X₀, 21 − X₀), LoAT abmc YES; variant: LoAT NO |
| term/p-60.t2_fixed | rank | `while i <= 100 and x >= 1: i := i + 1` | 101 − i, reading no param | i <= 100 dropped | KoAT2 (101 − X₀), LoAT abmc YES; variant: LoAT NO |
| term/AckR.jar-obl-8 | rank | an iterative Ackermann: x resets while y drops | (y, x) in order, after a linear rank is refused | x := x − 1 as x := x | KoAT2 (1 + X₁, 1 + X₀ + X₁); variant: LoAT NO, a lasso |
| term/Alternate.jar-obl-10 | rank | three loops of two locations | a rank per location | the copy loop's x' + 1 <= x as x' <= x | KoAT2 (a rank per location); variant: LoAT NO |
| term/toy3.t2 | rank | `while y > 1 or y < 0: x := x + 1`, y := 0 once x >= 100 | 100 − x, then y's sign | y := 0 as y := y | KoAT2 (100 − X₀, X₁, −X₁), LoAT abmc YES; variant: LoAT NO |
| term/polyrank1.t2 | nonlinear rank | `while x >= 1: x := x − y; y := y + 1` | the multiphase rank (1 − y, x) | y + 1 as y − 1 | the rank's three conditions by z3 (`tasks/its/polyrank1.t2.rank.smt2`, `runs/corpus2/truth-polyrank1`), LoAT abmc YES; variant: LoAT NO |
| term/2Nested-1 | nonlinear rank | `while x >= 0: x := x + y; y := y − 1` | a 2-nested rank: y + 1, then x | y − 1 as y + 1 | SV verdict true, Ultimate YES (`sv2`), LoAT abmc YES; variant: LoAT NO |
| term/Toulouse-BranchesToLoop-2 | nonlinear rank | `x := 1 or −1; while y < 100 and z < 100: y := y + x; z := z − x` | a rank by x's sign (products with x, or a guard in the rank) | x = −1 as x = 0 | SV verdict true, Ultimate YES, LoAT abmc YES; variant: LoAT NO, a lasso |
| term/Piecewise | nonlinear rank | `while q > 0 and p > 0 and p != q`: the smaller drops, the other any | min(p, q) | q − 1 as q | SV verdict true, Ultimate YES (`sv2`); variant: LoAT NO, a lasso |
| term/McCarthy91_Iteration | nested recursion | McCarthy's 91 as a loop with a call depth c | the region n <= 111 as an invariant | c − 1 as c | SV verdict true, KoAT2, Ultimate YES; variant: LoAT abmc NO |
| term/AProVEMath.jar-obl-8 | sampling | halving: x = 2·q or 2·q + 1, q fresh | runs whose inputs meet an equation | the even case's halving as x' = x | KoAT2 (1 + X₀, 2·X₀ − 1, X₀); variant: LoAT NO, a lasso |
| term/ListReverseCyclicList.jar-obl-10 | sampling | a list built then reversed, fresh values bounded together | runs meeting ten bounds at once | the builder's n − 1 as n | KoAT2 (a rank per location); variant: LoAT NO |
| term/WhileFalse | sampling | `while false: skip` | any rank: the loop takes no turn | `while (true)` | SV verdict true, KoAT2, LoAT abmc YES; variant: LoAT NO, a lasso |

The termination checks' runs are `runs/corpus2/truth-term` and `truth-term-lassos`. Each lasso is confirmed by
`checkLasso`, which uses no gdp-wired code.

LoAT's `--engine abmc` is a weak witness for YES. It answered YES on Toulouse's broken variant, which a confirmed lasso
(a stem of 14 steps, a cycle of 4) shows doesn't terminate. So no item rests on it alone: polyrank1, an ITS task with
no verdict, has its rank checked by z3.

The SV tasks are vendored as the C program, its `.yml` and the `.ari` that `compare/term/c2ari.py` makes from it,
which is what gdp-wired ran.

## Language gaps

What the corpus can't hold, because the library's language can't state it:

- **Nontermination** (ITS: 212 tasks another tool proves nonterminating, `runs/corpus2/failures-its-term-gdp.txt`:
  127 long runs with no state repeated, 83 runs that stop within 5 turns on average, 2 that take no turn). A law is a
  claim about every run. The library has no claim that some run never ends: no recurrent set, no existential over
  starts or runs. gdp-wired answers nonterminating only with a lasso, which compare/term's code finds and checks.
- **TIP problems the translation refuses at 0.21.0** (`runs/modal/arith/tip-gdp`, `runs/corpus2/groups-tip.txt`):
  - a function variable returning a list, 4;
  - an uninterpreted sort, 2;
  - an uninterpreted constant, 2;
  - a product of two integers, 1 (`nicomachus_theorem`; 1 more in `false/`);
  - a nested datatype at ever larger instances, 1 (`polyrec_seq_index`).
- **Definitions the language takes only by structural recursion**: a ring of functions that isn't structural,
  14 theorems (9 more in `false/`).
- **Definitions refused by their termination, not their syntax**: 91 theorems with no measure proven to fall and 14
  recursing on an Int. These can be written, and the items `sort_HSortCount` and `mccarthy91_M1`/`M2` stand for them.
- **SV-COMP tasks the C translation refuses** (`runs/modal/term/sv3`, 56): recursion 28, pointers and the heap 10,
  unsigned types 10, arrays 6, a call inside an expression 2.

Every CHC task chosen translates, the remainders and projections included. Since 0.20.0 a law states them with `exists`.

## Cost

Boat (from the batches' logs): the baseline $0.02359; the CHC truth checks $0.0492 (`truth-chc-select`) and
$0.02064 (`truth-chc`); a TIP probe $0.00074.

Modal (when boat's hourly VM starts were used up by the parallel tracks): 13,688.65 s of job time in all.
- `truth-tip-tools`: 12,140.85 s of tool time in 30 containers.
- The rest: `truth-term` 695.2 s, `tip-time-modal` 583.3 s, `truth-term-lassos` 149.3 s, `chc-time1` 69.3 s,
  `truth-tip-eval` 49.1 s, `truth-polyrank1` 1.6 s.

Modal's dollar figures for the day aren't in its billing report until the day closes.

## Sources

The vendored tasks, unchanged except for the broken variants (each `.broken.*`, the change in its id):
- `tasks/chc/`: chc-comp/chc-comp26-benchmarks at b4fa7a7.
- `tasks/tip/`: tip-org/benchmarks at bace5b2.
- `tasks/its/`: TermCOMP/TPDB-ARI at 183f29d.
- `tasks/sv/`: sosy-lab sv-benchmarks at c5cc603.

The candidates they were chosen from are `candidates-chc.md`, `candidates-tip.md` and `candidates-term.md`.
