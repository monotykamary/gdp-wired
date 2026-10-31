# research/dag: is the tree the bottleneck on the CHC step goals?

A measurement. Nothing here is in the trusted base (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`,
`lean-kernel/*.lean` are unchanged); the prototypes are untrusted searches whose certificates are checked by
`check-dag.ts`, a checker outside the trusted base. Every figure below is printed by `python3 research/dag/summarize.py`
from the run directories under `runs/modal/dag/` (local, not in git); each batch ran on Modal, one job a container
(2 vCPU, 4 GB), through `modal_dag.py`. Superseded and not used here: `runs/modal/dag/cdcl` (cdcl.ts before its bound
reasons were made lazily, c1fbfc2; `cdcl-final` is the same search at the final code), `bmc-z3parsebug` (z3's models
read wrongly) and `bmc-stackbug` (the split order overflowed the stack at deep k).

## The hypothesis

On CHC-COMP LIA-Lin, given Spacer's invariant, the kernel's prover left the step goal of one of its conjuncts
undecided on 332 tasks (287 Lustre; `compare/chc/README.md`, 0.20.0). A proof is a tree of case splits with a
Farkas-style certificate at each leaf, so a refuted sub-case is refuted again in every branch that reaches it
(tree-like resolution). The hypothesis: a DAG (refuted cases learned as clauses, CDCL(T)-style, each leaf still a
linear-arithmetic certificate) would close most of them; and the same engine on k unrolled steps would find the
short counterexamples on the unsat side.

**What the runs say:** the step is easy for an SMT solver (z3 decides all 332 in 0.08 s median), the tree search
repeats itself a lot (95% of its leaves read the same rows as an earlier leaf), but learned clauses close few of
those repeats on the Lustre goals: a refutation's core is nearly its whole path (median 59 decisions), because a
hypothesis' facts read every decision on the chain of `if`s that the step's terms are. The best prototype closes 88
of 332 (46 Lustre), all 95 of the prototypes together (52 Lustre); the tree search, given the goal alone with its own
budget, closes 45. Of the 179 Lustre tasks whose invariant is a bound of one value (`DRAGON_10`'s class) 12 close. So
the certificate's shape is not the bottleneck there; the cost of each node (an elimination over every row the path gives,
the rows read again at every path: 56% of the tree search's time in the solver) and how long the cores are, are.

## The goals

`given-dump.ts` is `compare/chc/prof/given.ts` with kernel/prove.ts's `setProveDump` hook: the same laws from
Spacer's model, the same `proveRule` with no search, the same 55 s; the last root goal the prover grows is written
as JSON (`goalio.ts`, hash-consed: the step's terms are shared objects) and as SMT-LIB (`toSmt`: every name a
natural, ∸ truncating, `if`/min/max as `ite`). `runs/modal/dag/dump`: on 330 of the 332 the run stopped `unknown` on
that goal again; on 2 (`MOESI_2_e8_101`, `lustre/cd`) it proved it this time (the budget is wall time), so their goal
was dumped by the name given-spacer3 stopped on (`--abort`, `runs/modal/dag/dump-abort`). The 332 goals have 17 to
218 hypotheses, median 37 (`runs/modal/dag/goals/`).

## 1. The solvers on the same goals

`runs/modal/dag/solvers`: z3 5.3.1 and cvc5 1.4.1 on each goal's SMT-LIB, 60 s, one (solver, goal) a container;
the seconds are the process's wall time, start-up included. These are the solvers' figures, not gdp-wired's.

| solver | unsat (the step holds) | median s | p90 s | max s | under 1 s |
| --- | --- | --- | --- | --- | --- |
| z3 5.3.1 | 332 / 332 | 0.08 | 0.14 | 2.37 | 331 |
| cvc5 1.4.1 | 332 / 332 | 0.11 | 0.33 | 3.15 | 323 |

A check of the encoding (`runs/modal/dag/solvers-sanity`): each goal without its last hypothesis (the conclusion's
negation) is sat for z3 on all 332, so the unsat answers aren't an artifact of the translation.

## 2. The tree search, profiled

`profile.ts` runs `tree.ts` (kernel/prove.ts's search, lines 1–703, copied with a recorder; same splits, same
arithmetic) on each goal alone, with the goal's own budget (a second a hypothesis, at least 20 s) within 55 s, and
keeps every leaf it finds, whether it ends in the tree or is thrown away (`runs/modal/dag/profile`). Then, outside the
search's time, each leaf's derivation is checked again over `leafConstraints` at its path (all 311,921 check), its
core is computed (`cores.ts`: the decisions the rows it reads depend on, as kernel.ts's `reusing` records them) and the
derivation replayed at the core alone (all 311,921 replay).

- Given the goal alone and its full budget, the tree search proves 45 of the 332 (10 of 287 Lustre); in
  given-spacer3 it proved none (there the step goal got what was left of the 55 s after the goals before it).
- 311,921 leaves; 95.1% read exactly the same rows (as linear forms) as an earlier leaf; 33.9% have the same core
  as an earlier one; 37.3% sit on a path that already holds an earlier leaf's core (a learned clause would have
  closed them with no solve). Per goal that last share has median 0.29 (p10 0.03, p90 0.71). Lustre: 96.1% same rows,
  30.1% subsumed; the 45 others: 89.6% and 80.7%.
- Depth: each goal's median leaf depth has median 69.5 decisions (deepest leaf 203); each goal's median core 59.
- Time: 56.0% of the search in the solver, 11.2% building rows; by phase of growRoot, the capped plain search
  6,888,675 ms, the cuts 3,791,064 ms, the first quick search 251,270 ms (summed over the goals).
- `DRAGON_10` (invariant `b19`, 37 hypotheses): 37,039 ms, 2,165 nodes, 1,010 leaves, 996 of them the same rows as
  an earlier one, 42 subsumed by an earlier core; leaf depth median 74 (max 90), core median 71; solver 22,894 ms.

The repeats are real, but on the Lustre goals they are mostly repeats of the same rows reached by different
decisions, not of the same decisions. Our reading of why (not measured beyond the core sizes): the step's next state is a chain of `if`s over the clause index and the guard's conditions,
a hypothesis gives its facts only once the chain is decided, and so every refutation's core holds the chain.

## 3. The prototypes and their checker

The certificate (`dag.ts`'s `Dag`): a list of nodes, each a clause (decisions that can't all hold): a leaf
`{leaf: [[lin, holds], ...], steps}` (its path, and a derivation over the rows the kernel reads at that path, exactly
a tree leaf's check) or a resolution `{res: [a, b], on: lin}` of two earlier clauses on an atom; the root's clause is
empty. `check-dag.ts` (60 lines) checks it: each leaf by kernel.ts's `leafConstraints` and core/check.ts's
`checkRefutation`, each resolution by set operations (an atom and its flip `1 − lin` read as one variable), the root
empty.

- `dag.ts`: kernel/prove.ts's splits (growPlain's order, its arithmetic at each node) with each leaf shortened to its
  core, both sides resolved, conflict-directed backjumping, and (unless `--no-learn`) every clause learned: a path
  holding a learned clause is closed by citing it, a path holding all of one but a literal splits on that literal next.
- `cdcl.ts`: CDCL over the atoms with the kernel's reading as the theory: unit propagation over learned clauses,
  bound propagation (an open atom its variables' single-variable bounds decide, its reason a leaf made when analysis
  needs it), first-UIP learning, VSIDS, phase saving, Luby restarts; the theory solved at every node (or, `--lazy`, only
  bound conflicts until no candidate is left open).

55 s a goal (`runs/modal/dag/{dag-nolearn,dag-learn,cdcl-final,cdcl-lazy}`):

| search | proven (Lustre) | checked by check-dag.ts | search ms, median of proven | DAG leaves, median | the tree it unfolds to, leaves median | check ms, median |
| --- | --- | --- | --- | --- | --- | --- |
| dag.ts, no learning | 73 (34) | 73 | 12,593 | 1,195 | 1,195 | 1,125 |
| dag.ts, learned clauses | 73 (30) | 73 | 5,373 | 250 | 729 | 313 |
| cdcl.ts | 88 (46) | 88 | 5,952 | 526 | 688 | 562.5 |
| cdcl.ts --lazy | 56 (15) | 56 | 4,657.5 | 451 | 666.5 | 608 |

- All 290 certificates check; none is rejected. Together the four prove 95 (52 Lustre); with the profiled tree
  search, 96 (one the tree alone).
- Learning doesn't prove more than the same search without it (73 each, 66 in common, 7 either way), but makes the
  proofs smaller (median 250 leaves against 1,195) and faster (5,373 ms against 12,593). On its proven goals the DAG
  shares: it unfolds to median 1.82 times its leaves (at most 8.54). CDCL proves 19 that dag.ts doesn't, and misses 4.
- Against the tree on the goals both prove: dag.ts with learning and the tree, 43: tree leaves 22,315, DAG leaves
  13,998 (unfolded 25,344), per goal median 0.54 of the tree's; search median 10,495 ms (tree) against 2,559 ms.
  cdcl.ts and the tree, 43: 22,675 against 13,982 (median 0.82); 10,495 ms against 2,750 ms.
- By the gap's class (compare/chc/prof/gap.py's, `runs/modal/chc2/gap-v020.json`), proven by some prototype: a bound
  of one value, Lustre, 12 of 179; a disjunction of three or more, Lustre 30 of 60, others 26 of 27; more than three
  values in one atom, Lustre 7 of 32, others 8 of 9; a yes/no guard (Lustre) 3 of 13; a boolean structure past 4,000
  clauses 6 of 6; two values (Lustre) 0 of 3; the rest 3 of 3.
- Where the time goes when they don't finish (medians over the 332, cdcl.ts): 32,255 ms of the 55 s in the solver,
  4,721.5 ms building rows, 4,120.5 ms in cores, 5,380.5 ms in the split order; 1,192.5 conflicts. z3 needs 0.08 s.
  `DRAGON_10` stays unproven by all four (cdcl.ts: 931 conflicts, 3,414 solves, 30,754 ms solving).

## 4. The goals the prototypes don't close

For the follow-up (a bit-sliced checker over the yes/no values): `vars.ts` on each goal (`runs/modal/dag/vars`),
reported here for the 236 goals no prototype nor the tree closes (234 Lustre). Classes: yes/no (a top-level
`x <= 1`), finite (a top-level `x < n`, n ≤ 64: the clause index `c` and the location `loc`), the halves of an
integer (`x` and `x$neg`: a CHC integer is a difference of naturals), other.

| | median | p10 | p90 | max |
| --- | --- | --- | --- | --- |
| variables | 261 | 134 | 333 | 408 |
| yes/no | 55 | 38 | 58 | 128 |
| yes/no a hypothesis reads beside its bound | 37 | 25 | 39 | 123 |
| finite | 2 | 2 | 2 | 2 |
| integer halves (all read) | 216 | 102 | 274 | 352 |

With every yes/no and finite value fixed at random (16 assignments a goal, each value within its bound), the
kernel's reading there: per goal, the median over its samples of the atoms still open has median 3 (p90 10, max
406), of the variables those atoms read 0 (p90 8, max 113), of the rows 211 (p90 244, max 462), of the variables
the rows read 1 (p90 14, max 85). The solver refutes 3,616 of the 3,776 samples and finds 160 satisfiable; in 492
nothing is left open. (Random assignments mostly contradict the guard; the samples say how much numeric work is left
once the booleans and the two finite values are fixed, not how often an assignment is consistent.) Fixing only the
yes/no values (profile.ts, 8 samples a goal) leaves 319 atoms open (median), 302 of them reading a number: the clause
index and the location decide which numeric conditions are read. 2^37 (the median of the yes/no values read) is
137,438,953,472 assignments, 4,294,967,296 u32 words.

## 5. BMC on the unsat side

`bmc.ts` (`runs/modal/dag/bmc`): on each of the 273 unsat Lustre tasks gdp-wired 0.20.0 doesn't answer
(`bmc-tasks.json`, with Golem's derivation length from `runs/modal/chc2/golem-cex-unsat`), the rule
(translate.ts's `build`) unrolled k = 1, 2, … 10 steps from its start as one kernel goal (`substE`/`substC`: step j's
request named `input@j`, its assumption a hypothesis, the last hypothesis that the run is at error after step k),
240 s a task. Each model found is replayed on the compiled rule and checked against the CHC itself by
compare/chc/translate.ts's `checkDerivation`; no model failed to be a run.

| Golem's derivation | tasks | a checked run, cdcl.ts (the prototype) | a checked run, z3 (reference) |
| --- | --- | --- | --- |
| 5 steps or fewer | 225 | 69 | 225 |
| 6–10 | 13 | 0 | 13 |
| more than 10 | 20 | 0 | 0 |
| none in 60 s | 15 | 0 | 0 |

- z3 (a reference, its figures, not gdp-wired's): 238 runs, each at k equal to Golem's derivation length
  (k = 2: 4, 3: 126, 4: 78, 5: 17, 6: 4, 7: 5, 8: 1, 9: 3); 0.1055 s median on the k it found (max 2.741 s).
- The prototype, cdcl.ts on the unrolled goal (its share of the 240 s at each k): 69 runs (k = 2: 4, 3: 55, 4: 10),
  4,915 ms median on the k found (max 27,181 ms); 608 answers "no run of k steps" whose DAG check-dag.ts accepted (none
  rejected), 1,520 `unknown` at their budget.
- 35 jobs ran out of memory at k = 7 to 10 (in tree.ts's `nearOf`, copied from kernel/prove.ts, which writes the
  unrolled goal's terms as JSON, expanding their sharing) and 3 reached the 300 s job limit; their lines up to then
  are counted.
- So BMC finds the short counterexamples gdp-wired's guided runs miss: with z3 deciding the unrolled rule, every task
  whose Golem derivation is 10 steps or fewer; with the prototype, 69 of the 225 of 5 or fewer, slowed by the same
  per-node cost as the step goals.

## 6. The Lean path (read, not built)

From Lean v4.34.0's sources and lean-kernel/ (read, not run):

- `Std.Tactic.BVDecide.LRAT`: `LRAT.check (lratProof : Array IntAction) (cnf : CNF Nat) : Bool`
  (`Std/Tactic/BVDecide/LRAT/Checker.lean:30`) and `LRAT.check_sound : check lratProof cnf → cnf.Unsat` (`:39`),
  `CNF.Unsat f := ∀ a, eval a f = false` (`Std/Sat/CNF/Basic.lean:74`): unsat over every Bool assignment. Steps are
  RUP/RAT additions over a fixed input CNF (and deletions); a step it can't convert is skipped, and it succeeds only on
  the empty clause. No theory lemmas: each leaf clause would be an input clause proven separately. bv_decide closes the
  check by `nativeEqTrue` (`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:39`), compiled evaluation that adds an
  axiom; this project's checks close by `decide +kernel` (`lean-kernel/emit.ts:268`). `../sat/lean-lrat.ts` already
  emits `theorem unsat : cnf.Unsat := LRAT.check_sound proof cnf (by decide +kernel | native_decide)`.
- `lean-kernel/Kernel.lean`: `abbrev Path := List (Row × Bool)` and `PathHolds` (`:317–318`); `checkT_sound`
  (`:1330`) holds for any path and any tree, under a model of the hypotheses; `sound` (`:1498`) concludes the goal's
  refutation from `checkGoal`. So a DAG leaf is a tree leaf checked at its own path, and reuses `checkT_sound`
  unchanged. `Cyclic.lean` (273 lines) already checks a list of nodes by index.
- What a DAG check in the twin needs (estimates, by analogy with Cyclic.lean; not written): a clause's meaning (a
  path that doesn't hold in a model, ~5 lines); resolution's soundness by cases on `eval l x ≤ 0` with the existing
  `flip`/`eval_flip` (~50–70); a fold over the node list with lookups of earlier clauses and the invariant that each
  is refuted (~60–90); the empty root to `sound`'s statement (~15): about 150–220 lines in all. Through Std's LRAT
  instead (leaf clauses as the input CNF, each proven by `checkT_sound`; resolutions as RUP lemmas with their two
  hints; a lifting lemma, an assignment `a v := decide (eval atoms[v] x ≤ 0)` that satisfies every leaf clause in any
  model): ~80–120 lines, but the check would reduce Std's checker under `decide +kernel` or add an axiom under
  `native_decide`.
- Export size: `lean-kernel/emit.ts` writes a tree as one nested term (`.split row yes no`, `.leafAt`), with no
  reference to an earlier subtree, so today's format can't share. A node list with indices (as Cyclic.lean's) would
  make the export the DAG's live size. Not measured in Lean text: no DAG export was written. Measured as certificates
  (JSON), the 332 above: the DAG's leaves against the tree it unfolds to. On the library's own goals
  (`items.ts`, every root goal the 27 examples the test script runs grow, the first 200 distinct each, 3 s each,
  `runs/modal/dag/items`): 272 goals, the tree proves 270 (all checked by kernel.ts's `check`), dag.ts 267 (all
  checked); on the 267 both prove, 155 trees have more than one leaf; the trees have 1,274 leaves and 3,991 derivation
  steps (200,761 bytes as JSON), the DAGs 1,745 leaves (unfolded 1,837) and 18,133 steps (1,130,420 bytes): there is
  little to share in those proofs, and this search (no cuts, no lift of the tree search) makes larger ones.

## 7. A proposal (not done, not measured beyond the above)

**Put the DAG in the kernel only with a search that profits from it.** The certificate change is small and its
soundness argument is the tree's: a leaf's rows hold in every model of the hypotheses where its path holds (what
`check` already relies on), so its clause follows from the hypotheses; resolution keeps consequences; the empty
clause refutes the goal.

- Trusted base, TypeScript: kernel.ts gains `checkDag(goal, dag)`, check-dag.ts's 40 lines of logic over the
  existing `leafConstraints`, `withProducts` and `checkRefutation`; a tree stays a certificate (a tree is a DAG whose
  every clause is used once), so nothing that checks today stops checking. The prover's output type and
  `checkLaws`/`checkStepLaws` accept either.
- Lean twin: `Kernel.lean` gains the node type, `checkDag` and `dag_sound : checkDag g d = true → ∀ env maps,
  ¬ ∀ c ∈ g.hyps, evalC env maps c = true`, by a fold invariant (each clause so far is refuted), `checkT_sound` for
  leaves, a resolution lemma, and `sound`'s ending; ~150–220 lines (estimate above). `emit.ts` writes the node list
  (indices, not nested terms), and the conformance test (core/conformance.ts) runs both checkers on the same DAGs and
  tampered ones.
- Expected gain, from these runs: on the 332, 290 checked certificates from four searches, 95 goals in all against 45
  by the tree; median leaves 0.54 of the tree's where both prove. Not most of the 332: the Lustre goals that stay open
  need either much cheaper nodes (incremental arithmetic instead of a full elimination at every path, as an SMT
  solver's simplex) or shorter cores (facts about an `if` before its whole condition is decided, Tseitin-style
  definitions of the step's terms), or the bit-sliced evaluation over their yes/no values; the DAG is the certificate
  any of those would emit.

## Files

| File | What |
| --- | --- |
| `given-dump.ts` | given.ts with the step goal written out (JSON and SMT-LIB) |
| `goalio.ts` | a goal to and from hash-consed JSON; as SMT-LIB |
| `tree.ts` | kernel/prove.ts's search, copied with a recorder (and `openOrder`, growPlain's split order) |
| `profile.ts` | the tree search on one goal, its leaves' duplicates and cores; the goal's variables |
| `cores.ts` | a leaf's core and its replay at the core |
| `dag.ts` | the DAG search (backjumping, learned clauses), the certificate's sizes |
| `cdcl.ts` | CDCL over the atoms, the same certificate |
| `check-dag.ts` | the checker of the certificate (outside the trusted base) |
| `vars.ts` | a goal's variables by class, and what fixing the yes/no and finite ones leaves |
| `bmc.ts` | BMC over a CHC task's rule: the prototype, z3 as a reference, runs checked by checkDerivation |
| `items.ts` | the tree against the DAG on the examples' own goals |
| `modal_dag.py`, `jobs.py` | the Modal runner and its jobs files (Modal-only and historical: the dump g332 reads was made with it; not run since) |
| `summarize.py` | every figure here, from runs/modal/dag/ |
| `step332-tasks.json`, `bmc-tasks.json` | the 332 step-goal tasks; the 273 unsat Lustre tasks with Golem's derivation length |

```sh
# compare/chc/prof/given-models.json (gitignored): {smt2 path: Spacer's model} of the 332, from runs/modal/chc2/spacer-models-sat
python3 research/dag/jobs.py dump > /tmp/dump.json && modal run research/dag/modal_dag.py --jobs /tmp/dump.json --out runs/modal/dag/dump
# copy each dump/<task>/goal.{json,smt2} to runs/modal/dag/goals/<task>/, then: solvers, profile, dag [--no-learn], cdcl [--lazy], vars, items, bmc
python3 research/dag/summarize.py
```
