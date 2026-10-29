# The prover's cost on goals over several keys: where the time goes, and the first step

The question: why do goals over laws of 3 to 5 keys cost so much (README.md's class D), and what would make them cheap
for the six protocols still unproven with nothing written: two_phase_commit, distributed_lock, toy_consensus_forall,
consensus_wo_decide, sharded_key_value_store and ring_leader_election? This note measures where each one's time goes
on its written invariant (the search off, so the search doesn't confound it) and in its search. It then reads how the
tools that prove these protocols keep such goals cheap, judges the candidates for this codebase, and recommends one
first step, measured once on the pilot and the corpus.

## The answer in short

- **Class D is three costs, not one, and none of them is the instances.** Building the instances takes at most 0.7 s
  a run (2.7 s for sharded KV), thinning at most 0.2 s, the model rounds' instance reads nothing measurable, and the
  kernel's check of the trees nothing measurable (toy consensus's certificate: 2 s). The time goes into the prover's
  search on a few goals:
  1. **A model the tree search wanders to.** Toy consensus: 187 s of 212 s go to two rounds of one goal that end in a
     model, because a tuple is missing (181k and 137k CDCL nodes). The round after, with the model's tuples added,
     proves the goal in 0.5 s. The CDCL search's model mode, which decides at the simplex's point, finds the same model
     in 0.96 s (663 nodes).
  2. **The cell pairs, every node.** The CDCL search lists every pair of cells of one map at each node (O(cells²)).
     That is 53% of toy consensus's profile, and 154 s of consensus_wo_decide's 451 s in the CDCL search.
  3. **Fourier–Motzkin at wide leaves.** Sharded KV's stuck goal reaches leaves of about 680 rows and 400 variables.
     There the simplex finds the rows feasible and the exact elimination blows up, so the search has nothing to split
     on. The tree search's cuts then spend 407 s.
- **Cost doesn't scale with tuples or hypotheses.** One 380-hypothesis goal takes 108 s when it ends in a model and
  0.5 s when it ends in a proof, and a 940-hypothesis goal is proven in 11 s. It scales with what the search does:
  - the nodes before a model;
  - the cell pairs per node;
  - the leaf's rows under elimination.
- **Only three of the six are blocked by cost, and only one of them on a written invariant that is known correct.**
  - two_phase_commit and ring_leader_election: the written invariants are proven in 14.2 s and 2.6 s, and their
    searches end in 13.7 s and 7.9 s with "found nothing". These are search misses (classes B and E).
  - distributed_lock: **its written invariant is wrong**, not costly. It lacks "no transfer or lock before init": a
    transfer the model holds before `init` breaks "a live transfer is above every epoch" once `init` sets `Ep[first]`.
    With that conjunct it is proven in 14.1 s. Its search's 202 s are 73% random runs (`refuteByRuns`) and 27% the
    join; the prover takes 3%.
  - toy_consensus_forall: cost 1 above, on a written invariant that is proven.
  - consensus_wo_decide and sharded KV: one goal each that no search settles in 600 s. Sharded KV's is cost 3. For
    consensus_wo_decide it is open whether the goal is a model or a proof.
- **The first step: decide at the simplex's point where laws are assumed at tuples.** The tree-mode CDCL search takes
  the decision phases the model mode already takes, on the goals of laws over several keys (the goals `withModels`
  asks). It is untrusted and about 10 lines (kernel/cdcl.ts, kernel/prove.ts). Measured once on Modal:
  - **toy consensus:** the written invariant goes from 211.7 s to 17.7 s;
  - **the rest:** no verdict changes anywhere (the pilot's 10 written invariants, 18 searches, 10 broken variants, and
    30 real-world laws over Casbin, Keycloak, Gitea and TigerBeetle);
  - **real-world time:** level (594 s against 588 s for the 30 laws).
  - It closes none of the six. It removes one protocol's cost and lets toy's and wo's searches end sooner
    (38 to 19 s, 73 to 46 s), still with "found nothing".
  - Its risk is time in some searches (ticket lock at 60 s: 48.9 to 60.5 s, single runs), which the confirming
    measurement must rerun.

## 1. Measurements

Modal, 2 vCPU, one job per configuration. `runs/cost/` in the gen/cost worktree (gitignored):
- `r1`: the profiles;
- `r2`: base against point phases on every goal reading a cell;
- `r3`: reruns of TigerBeetle and Gitea #0;
- `r4`: point phases gated to laws at tuples.

The instrumentation is `research/protocols/cost.patch`: a `git apply` adds an env-gated cost log to kernel/prove.ts
(`GDP_COST_LOG=1`), the research flags below, and three scripts. Nothing in the code path changes without it.

    git apply research/protocols/cost.patch
    GDP_COST_LOG=1 bun research/protocols/cost.ts <id> [--extra] [--deadline 600000] [--search 60000] 2> err.log
    python3 research/protocols/cost_sum.py err.log 25 [--all]       # per law, per goal, phases, CDCL counters
    bun --cpu-prof --cpu-prof-interval=5000 ... ; python3 research/protocols/cost_prof.py x.cpuprofile fn@file,...

The cost log has:
- per law: its instances (tuples per assumed law), the thinned and full attempts, and each `withModels` round;
- per root goal: its hypotheses and root rows, and the time in growRoot's phases (quick plain search, CDCL, plain,
  cuts);
- the CDCL search's own counters, from `cdclStats`: row sync, candidates, bound propagation, simplex, elimination,
  core, unfold, and the rest (unit propagation and conflict analysis).

The CPU profile (bun's sampler at 5 ms) gives self and inclusive time by function. `--deadline` bounds every goal by
wall time (`withDeadline`) so that a run ends and reports.

### Per miss, on its written invariant

| Protocol | Written invariant (base, Modal) | The goal that takes the time | Where inside |
| --- | --- | --- | --- |
| two_phase_commit | proven 14.2 s | none over 3 s | not cost |
| distributed_lock | unknown 3.6 s: a model | "a live transfer is above every epoch @step", 0.15 s | a real counterexample to induction (above); with the conjunct, proven 14.1 s |
| toy_consensus_forall | proven 211.7 s | "one value decided @step" (the safety law, 2 keys, 380 hypotheses, 102 root rows): 187.8 s over 3 rounds, 108.8 s and 78.5 s ending in a model, then 0.5 s proven | CDCL 201 s: candidates 130, row sync 23, elimination 14, bound propagation 12, simplex 8, the rest 14. Profile: `cellPair` 27% self, `openCellsLive` 53% inclusive |
| consensus_wo_decide | unknown at 604 s | "a leader has the voting quorum's votes @step" (2 keys, 859 hypotheses, 243 root rows): 585.7 s, out of budget | CDCL 451 s (elimination 200, candidates 154, the rest 44, row sync 23, bound propagation 22, simplex 8), then the plain search 149 s. Model mode and point phases find no model in 20–25 s locally; leaves of 1,000 to 3,400 rows |
| ring_leader_election | proven 2.6 s | none | not cost |
| sharded_key_value_store | unknown at 600 s | "a key in transfer has no owner @step" (4 keys): thinned (664 hypotheses) 443.9 s, cuts 406.8 s; full (748) 137.0 s, CDCL 102.5 s, elimination 88.9 s | profile: solver.ts `add`, `scale`, `tighten`, `sigOf` (the elimination) about half; model mode stops "no split" in 2.6 s locally, the elimination's blow-up (pos × neg > 5 · maxRows) 18 times at leaves of 676 rows and 406 variables |

The other goals of these four rules are proven in 0.1 to 11.1 s each, among them the 3- and 4-key laws (toy's "one vote
per node", 604 hypotheses, 10.9 s; sharded KV's "a table entry is its owner's", 715 hypotheses, 2.0 s).

### Per miss, in the search (60 s, nothing written)

| Protocol | Wall | Root goals' time | Where the rest goes |
| --- | --- | --- | --- |
| two_phase_commit | 14.0 s | 4.3 s; the safety law's step goal 14 times, 12 models | the join, then "found nothing" |
| distributed_lock | 180.6 s | 3.0 s | `refuteByRuns` 73% inclusive, `inferLawsSearch` 27%; the interpreter (`evalC`, state copies) is most of the self time |
| toy_consensus_forall | 41.1 s | 32.4 s; the safety goal 8 times, up to 4,051 hypotheses and 1,730 rows, 5 models and 3 out of budget | candidates 16.8 s of 24.7 s in the CDCL search |
| consensus_wo_decide | 72.3 s | 50.6 s; the safety goal 8 times, up to 23,556 hypotheses and 4,309 rows, 5 models and 3 out of budget | candidates 21.4 s of 36.7 s |
| ring_leader_election | 7.5 s | 1.3 s | the join, "found nothing" |
| sharded_key_value_store | killed at 770 s | no goal logged | outside the prover's goals; not measured further |

### What the time scales with

Not tuples, not hypotheses (toy's goals above). Per goal, three things:
- **The nodes a search spends before a model.** In tree mode the CDCL search decides by saved phases, and on a goal
  that has a model it wanders: 94,384 nodes in 25 s locally on toy's goal without one. In model mode it decides at
  the simplex's point and finds the model in 663 nodes.
- **The cell pairs per node.** `openCellsLive` lists every pair of one map's live cells whose keys the trail leaves
  open, again whenever a cell or a pair's decision changes (nearly every node), and `cellPair` builds each pair's key
  difference behind a string-keyed cache. Toy's leaves read 1,338 rows over 796 variables.
- **Elimination at a leaf.** It is run where the simplex is feasible and nothing is open. It is exponential in the
  worst case, and sharded KV's composed keys (n·4096 + k·64 + v) are where it blows up.

### Probes of the costs (local, M-series Mac, each about 25 s, on goals dumped from the given runs)

| Probe | Result |
| --- | --- |
| toy's goal, tree search | unknown at 25 s, 94,384 nodes |
| toy's goal, model mode (`growCdcl … {model: true}`) | a model, 0.96 s, 663 nodes |
| toy's goal, tree search deciding at the simplex point (`GDP_POINT_PHASE=1`) | a model, 1.07 s, 663 nodes |
| toy's "one vote per node @step" (a proof), tree search / at the point | proven 3.9 s, 7,366 nodes / proven 0.9 s, 1,167 nodes |
| sharded KV's goal, model mode | "no split" at 2.6 s: elimination blew up 18 times; the simplex point is not integral (`GDP_LP_POINT`) |
| the same, branching on the simplex's fractional point when elimination blows up | goes on, unknown at 20 s; elimination 17.5 s of 20 (736 blow-ups) |
| the same, splitting composed keys by part first (`GDP_KEY_PARTS`: a = a', then b = b', before a·N + b = a'·N + b') | unknown at 20 s, 129 splits deep against 132: no change |
| consensus_wo_decide's goal, model mode / at the point | unknown at 20 s / 25 s; leaves of 1,054 to 3,414 rows |

## 2. How the tools that prove these protocols keep multi-key goals cheap

| Tool / technique | What keeps a goal over several keys cheap | Here: search or trusted |
| --- | --- | --- |
| Ivy, EPR (Padon et al. 2016, 2017) | the verification condition stays in EPR (∀*∃*, stratified functions), so Z3 decides it with finite models; a relation over two sorts is a predicate of two arguments, compared argument by argument, never one number | a front end's encoding; maps keyed by tuples would be a kernel change (trusted, Lean first) |
| Z3's EPR decision (de Moura, Bjørner 2008; Piskac, de Moura, Bjørner 2010) | DPLL over clauses with substitution sets: one clause stands for its ground instances, so they are never written out | a different kernel; not considered |
| mypyvy, UPDR, Phase-PDR∀ (Karbyshev et al. 2015; Feldman et al. 2019) | each query is a small formula (a frame, a diagram of one finite model), asked incrementally with assumptions (Eén, Sörensson 2003) | search |
| DistAI, DuoAI (Yao et al. 2021, 2022) | the template bounds the variables per sort (3 in all, 2 per sort), so the checks Ivy makes have few, short ∀ clauses | search |
| IC3PO (Goel, Sakallah 2021) | learns on a finite instance with a few elements per sort; a clause's orbit under the sorts' permutations becomes one quantified clause; Z3 checks the result unbounded | search |
| SWISS (Hance et al. 2021) | enumerates small formulas in parallel, pruned by models and symmetry | search |
| E-matching and triggers (de Moura, Bjørner 2007; Leino, Pit-Claudel 2016) | a quantifier is instantiated only at terms that match its trigger; triggers chosen to avoid matching loops | search: prove.ts's `matched`, `triggered`, `keySorted` already are this |
| Relevancy (de Moura, Bjørner, MSR-TR-2007-140) | only atoms relevant to the current assignment are propagated and matched | search: the cell-pair candidates are the opposite, every pair every node |
| MBQI (Ge, de Moura 2009); enumerative instantiation (Reynolds, Barbosa, Fontaine 2018) | instances added lazily from a candidate model that breaks a quantifier | search: `withModels`/`modelInstances` already are this; its cost is finding the candidate model |
| Conflict-based instantiation (Reynolds, Tinelli, de Moura 2014) | before E-matching's many instances, look for one instance that conflicts with the current ground assignment; it targets E-matching's overproduction | search |
| Finite model finding in SMT (Reynolds, Tinelli, Goel, Krstić 2013) | bounds a sort and instantiates over its representatives only | search |
| SInE (Hoder, Voronkov 2011) | an axiom enters only if its symbols are reachable from the goal's | search (which laws a goal assumes) |
| Paradox (Claessen, Sörensson 2003) | static symmetry reduction of the domain elements, per inferred sort | search |
| Simplex for DPLL(T) (Dutertre, de Moura 2006) | integer arithmetic by an incremental simplex with branch and bound and cuts, its conflicts explained by Farkas rows, in place of elimination | search, if its leaves are certified as now (a split tree with Farkas rows; core/check.ts checks combinations and cuts) |

**What they share for cost.**
- **The candidate model comes from the arithmetic.** In DPLL(T) solvers the satisfying assignment is the theory
  solver's point, and MBQI starts from it. gdp-wired's model mode does the same; its tree mode doesn't, and that is
  cost 1.
- **Relevance, not enumeration.** Z3's relevancy and E-matching's triggers keep the atoms a search touches to those
  the assignment needs. The cell pairs, every pair at every node, are cost 2.
- **No arithmetic on tuples.** Ivy's relations take tuples, and the solvers decide integers by simplex, not by
  elimination. Sharded KV's tuples as n·N² + k·N + v under elimination are cost 3.

**Trusted or not.** Every candidate below is search: it changes which atoms the prover splits on, in what order, and
how a leaf is refuted, and the kernel checks the tree as before. The one trusted change the literature suggests is
maps keyed by tuples (Ivy's relations). Nothing measured here asks for it: splitting composed keys by part changed
nothing on sharded KV, so the encoding is not shown to be the cost.

## 3. Candidates, judged for this codebase

| Candidate | Search or trusted | Size | Closes of the six | Real-world laws over several keys | Risk to speed and CHC | Verdict |
| --- | --- | --- | --- | --- | --- | --- |
| **C1. Decide at the simplex's point where laws are assumed at tuples** (`GDP_POINT_PHASE=2`: `withModels` marks the goals of laws over several keys or quantified flags over several keys; the tree-mode CDCL search then sets each decision's phase as model mode does, and still unfolds its refutations) | search | about 10 lines: cdcl.ts's one phase line, prove.ts's scope in withModels | none. Toy's written invariant 211.7 → 17.7 s; searches end sooner (toy 38.1 → 19.2 s, wo 73.3 → 46.2 s), still "found nothing" | Gitea #0 unknown either way (62.8 s against 53.4–58.5 s); TigerBeetle, Casbin and Keycloak verdicts the same; the 30 laws 594 s against 588 s | CHC: off by construction (no maps, so no laws at tuples). Searches, single runs: ticket 60 s 48.9 → 60.5 s, async 60 s 86.9 → 111.3 s, decentralized 60 s 11.8 → 17.0 s, all still proven; sync 109.7 → 102.1 s, wo 10 s 41.0 → 27.6 s faster | **the first step** (below) |
| C1 ungated (`GDP_POINT_PHASE=1`, every goal reading a cell or a quantified flag) | search | as C1 | none; toy 10.1 s | TigerBeetle #0, #1, #3 and #4 slower in every run (9% to 46%); #2 killed at 150 s in 2 of 3 runs and #5 in 1 of 3, both proven in every base run | a loss on wide one-key records | **no-go** |
| C2. The cell pairs kept incrementally (each map's open pairs updated by the cells that come and go and the pair decisions that change, as reader.ts keeps rows) | search | about 30 lines in cdcl.ts | none by itself | a constant factor wherever a map has many live cells; whether that is TigerBeetle #4 and #6's 110–157 s is unmeasured | none to CHC (no cells); output unchanged (the same candidates, in the same order) | **second**: after C1, toy's candidates are 3.3 of 15.4 s, and wo's stuck goal still spends 154 s there |
| C3. Integer leaves by the simplex: branch and bound on its point, Farkas rows as the leaf, elimination only on a conflict's support (Dutertre, de Moura 2006) | search, certified as now | large: the elimination is also the integer witness and CHC's workhorse | sharded KV's goal, if the blow-ups are the whole story (unshown: the probe kept the elimination at every node) | none known | high for CHC: every linear goal's leaf check changes | **later, behind its own probe**: sharded KV's goal with the elimination skipped where the simplex decides |
| C4. Composed keys split by part (a = a', b = b' before a·N + b = a'·N + b') | search | about 20 lines | none measured | Casbin's link table is the same encoding | low | **no-go as measured** (sharded KV unchanged at 20 s) |
| C5. The removed model-first step without its floor of 500 hypotheses | search | the 2,444 bytes e634828 took out | none | as C1 | a proven goal pays the model search first, up to its share | **subsumed by C1**: one search finds the model (toy, 1.07 s) and proves faster too (3.9 → 0.9 s) |
| C6. Conflict-based instances: a tuple added as soon as the trail breaks an assumed law there, then the goal asked again | search | a hook in the CDCL loop plus withModels' restart | none measured; would remove toy's two model rounds | Gitea #0, if its models are of this kind | restarts cost; a goal's hypotheses are fixed while it is grown (the kernel checks a tree for that goal) | **later**, if C1's rounds stay costly |
| C7. distributed lock's written invariant completed ("no transfer or lock before init") | the research model | one law in models.ts | none (a written invariant, not the search) | – | – | **do it**: README's table counts a wrong written invariant as unknown. Not done here: models.ts is unchanged on this branch |

**One organizing idea?** C1 and C2 come from one reading. The CDCL search is the ground solver of an instantiation loop
(`withModels`). The literature keeps that solver cheap by asking the arithmetic for its candidate model (C1) and by
touching only relevant atoms (C2). Both are general, untrusted and blind to the protocol. They do not reach sharded
KV's elimination (C3) or consensus_wo_decide's unresolved goal, and no candidate closes one of the six by itself.
Those six are blocked mostly elsewhere:
- 2PC and ring: the search's own misses (classes B and E);
- distributed lock: its written invariant, then its search's runs;
- toy and wo: their searches end with nothing found once the cost is gone.

## 4. Recommendation: decide at the simplex's point on the goals of laws at tuples

- **The step:** C1 as measured: kernel/cdcl.ts sets a decision's phase at the simplex's point (`phaseAtPoint`) when
  its goal is asked inside `withModels` for laws over several keys or quantified flags over several keys. About 10
  lines, untrusted, no flag kept.
- **Why first:** it is the measured cost of the one class-D protocol whose written invariant is right and proven
  (toy: 92% of its time). It reuses a piece the CDCL search already has, and it is small. Its one measured loss (the
  ungated form on TigerBeetle) is gated out.
- **The measurement that confirms it:**
  - the protocols pilot, three runs a side: every verdict as before. The searches at 60 s must keep ticket lock,
    lock_server_async and decentralized lock proven in every run (the single-run slowdowns above are the risk). Toy's
    written invariant must stay under 30 s;
  - a quick bar against its base:
    - CHC dev unchanged (the step is off there by construction, so any change is timing);
    - real-world dev: no verdict lost, and the per-law time level;
  - Gitea #0 and TigerBeetle #0–#7, three runs: verdicts and times level.
- **If ticket lock is lost at 60 s in any run:** no-go as is, and the next measurement is C1 in `proveLaw` and
  `proveThinned` only (the claim path), not in the join's `stepWith`.
- **What it will not do:** prove any of the six. After it, the next costs are C2 (consensus_wo_decide's candidates)
  and C3 (sharded KV's elimination), and the misses are the search's.

## Spend

Modal only. Apps of this round, billed (`modal billing report --for today --resolution h --json`):
- r1, the profiles, 10 jobs, 2,600 s of job time: $0.130;
- r2, base against the ungated step, 128 jobs, 6,078 s: $0.273;
- r4, the gated step, 69 jobs, 3,007 s: $0.142;
- the pilots: $0.002.

- r3, reruns of TigerBeetle and Gitea #0, 36 jobs, 2,595 s: $0.114.

Total billed: $0.66.

## Citations

- Padon, McMillan, Panda, Sagiv, Shoham. Ivy: Safety Verification by Interactive Generalization. PLDI 2016.
  [PDF](https://ilyasergey.net/CS6213/_static/papers/ivy.pdf). Padon, Losa, Sagiv, Shoham. Paxos Made EPR. OOPSLA 2017.
- de Moura, Bjørner. Deciding Effectively Propositional Logic Using DPLL and Substitution Sets. IJCAR 2008; with
  Piskac, JAR 2010. [MSR](https://www.microsoft.com/en-us/research/?p=153263).
- Wilcox et al. mypyvy. [GitHub](https://github.com/wilcoxjay/mypyvy).
- Karbyshev, Bjørner, Itzhaky, Rinetzky, Shoham. Property-Directed Inference of Universal Invariants or Proving Their
  Absence. CAV 2015; J. ACM 2017. [PDF](https://www.tau.ac.il/~sharonshoham/papers/jacm17.pdf).
- Feldman, Wilcox, Shoham, Sagiv. Inferring Inductive Invariants from Phase Structures. CAV 2019.
  [arXiv:1905.07739](https://arxiv.org/abs/1905.07739).
- Yao, Tao, Gu, Nieh, Jana, Ryan. DistAI. OSDI 2021. [PDF](https://www.cs.columbia.edu/~nieh/pubs/osdi2021_distai.pdf).
  Yao, Tao, Gu, Nieh. DuoAI. OSDI 2022. [PDF](https://www.cs.columbia.edu/~nieh/pubs/osdi2022_duoai.pdf).
- Goel, Sakallah. On Symmetry and Quantification: A New Approach to Verify Distributed Protocols. NFM 2021.
  [arXiv:2103.14831](https://arxiv.org/abs/2103.14831).
- Hance, Heule, Martins, Parno. Finding Invariants of Distributed Systems: It's a Small (Enough) World After All
  (SWISS). NSDI 2021. [PDF](https://www.andrew.cmu.edu/user/bparno/papers/swiss.pdf).
- de Moura, Bjørner. Efficient E-Matching for SMT Solvers. CADE 2007.
  [PDF](https://inst.eecs.berkeley.edu/~cs294-260/sp24/papers/efficient-ematching.pdf).
- Leino, Pit-Claudel. Trigger Selection Strategies to Stabilize Program Verifiers. CAV 2016.
  [MSR](https://www.microsoft.com/en-us/research/publication/trigger-selection-strategies-stabilize-program-verifiers/).
- de Moura, Bjørner. Relevancy Propagation. MSR-TR-2007-140. [MSR](https://www.microsoft.com/en-us/research/?p=153156).
- Ge, de Moura. Complete Instantiation for Quantified Formulas in Satisfiability Modulo Theories (MBQI). CAV 2009.
  [Springer](https://link.springer.com/doi/10.1007/978-3-642-02658-4_25).
- Reynolds, Barbosa, Fontaine. Revisiting Enumerative Instantiation. TACAS 2018.
  [PDF](https://verit.loria.fr/papers/tacas2018.pdf).
- Reynolds, Tinelli, de Moura. Finding Conflicting Instances of Quantified Formulas in SMT. FMCAD 2014.
  [PDF](https://homepage.cs.uiowa.edu/~tinelli/papers/ReyTD-FMCAD-14.pdf).
- Reynolds, Tinelli, Goel, Krstić. Finite Model Finding in SMT. CAV 2013.
  [record](https://bibtex.github.io/CAV-2013-ReynoldsTGK.html); with Deters and Barrett, Quantifier Instantiation
  Techniques for Finite Model Finding in SMT, CADE 2013,
  [abstract](https://theory.stanford.edu/~barrett/pubs/RTG+13-abstract.html).
- Hoder, Voronkov. Sine Qua Non for Large Theory Reasoning. CADE 2011.
  [Springer](https://link.springer.com/doi/10.1007/978-3-642-22438-6_23).
- Claessen, Sörensson. New Techniques that Improve MACE-style Finite Model Finding. CADE-19 workshop, 2003.
  [PDF](https://lara.epfl.ch/w/_media/projects/paradoxpaper.pdf).
- Eén, Sörensson. Temporal Induction by Incremental SAT Solving. BMC 2003, ENTCS 89(4).
  [Chalmers](https://research.chalmers.se/en/publication/74330).
- Dutertre, de Moura. A Fast Linear-Arithmetic Solver for DPLL(T). CAV 2006.
  [Springer](https://link.springer.com/doi/10.1007/11817963_11),
  [PDF](https://lara.epfl.ch/w/_media/fv20/fastsimplexdpllt.pdf).

## After this note: three steps (gen/cost)

**1. Why random runs ate the search.** `refuteByRuns` is counted in trials, not timed (its comment says why). The
cost was each step's law watch: a law about n keys was read at every n-tuple of 0..bound+1 and every key any map
held. Composed keys (e·64 + a) made those raw keys values of every name, so distributed_lock's 3-key safety law was
read at about 27³ tuples a step, and sharded KV's 5-key law at about 27⁵. On distributed_lock that is about 600k
reads a trial over `searched`'s 2,400 deeper trials, and sharded KV would take half an hour.
- **The fix, general:**
  - each name takes its own keys: a composed key's digits where a map's reads key it, with 0..bound+1;
  - a cap on each call: 10,000 tuples read per trial it is given, counted, so deterministic. The broken variants'
    runs read at most 2.2M of a 600-trial budget's 6M.
- **What it bought:**
  - the protocols' 18 measured searches at 10 s and 60 s: 964 s to 369 s;
  - sharded KV's search ends;
  - every broken variant is refused by the same run as before, faster;
  - the 311 real-world laws: the same 274 / 29 / 8, per-law time −7.1% (`runs/cost/s1-base`, `s3-off`).

**2. distributed_lock's written invariant** completed with "no transfer or lock before init": a fix to our model, not a
prover gain. Proven in 12.9 to 16.3 s.

**3. Decisions at the simplex's point, on the proof path only** (`proveLaw`, `proveThinned`; laws about several keys):
- three runs a side, every verdict the same, and ticket_lock, lock_server_async and decentralized_lock proven in
  every 60 s run;
- toy's written invariant: 209–260 s to 12–16 s;
- Gitea #0 slower (54 to 62 s, unknown either way), TigerBeetle level;
- the quick bar (chc, rw): nothing lost, wrong 0.

Kept. With the cost gone, the six misses' searches end with "found nothing" inside their budgets: what blocks them now
is the search, not its cost.

**The full bar against 4f7c7a6** (base launched together: a shared baseline was past the budget;
`runs/bar/runs/cost-full-83dbc59`):
- wrong 0 everywhere, nothing lost in every run;
- CHC 1,166 against 1,167 (timing flips at the limit: no changed path runs there), ITS +3, SV, TIP and the frontier
  corpora level;
- the real-world corpus one flip of noise, the 332 step goals' search 284.7 against 298.6 s, suites 224 of 224, Lean
  48 of 48;
- size +3,815 bytes.

## Steps 4 and 5 (gen/cost2, from fb46b48: e7eab01 with gen/cost)

**4. The cell pairs listed cheaply (kept).**
- **The change:** the CDCL search's list of open cell pairs stands in a flat list, made again only where the live
  cells change, each pair's atoms read once a session.
- **The same search:**
  - local, toy's "one vote per node": 7,366 nodes, 193 conflicts, 4,329 decisions and one tree both ways, candidates
    1,783 to 828 ms; its model search 663 nodes both ways;
  - the 332 step goals: the same search on all 332.
- **The protocols:** two runs a side, every verdict the same, wall times level. One candidate run of 2PC's written
  invariant took 95.5 s; three reruns took 12.6–14.7 s, so it was a container stall.

**5. Integer leaves by branch and bound (dropped).**
- **The leaf histogram** (every leaf elimination's rows and outcome, `runs/cost2/fm`, `fm-chc`):
  - CHC has 13 blow-ups over 1,406 tasks, beside tens of thousands of leaves of 600 rows or more that elimination
    answers (integer points, cut refutations, models);
  - the protocols and the multi-key real-world laws have none;
  - sharded KV blows up at 670–760 rows over 55 variables.
  - So a fixed size gate would take over CHC's leaves for nothing. The gate tried is the blow-up itself, per session.
- **Sharded KV's goal:** branch and bound keeps it moving, 113,622 nodes in 25 s against 5,833. But 600 s on Modal
  prove neither sharded KV's written invariant nor consensus_wo_decide's. A no-go on its own probe.
- **What the leaves need:** these leaves are rationally feasible and integer-infeasible (elimination refuted 17 of
  them by cuts). Splitting at fractional points doesn't find those refutations in budget.

**The full bar against fb46b48** (step 4 alone, base launched together; `runs/bar/runs/cost2-full-20618f2`):
- wrong 0, nothing lost in every run;
- CHC 1,177 against 1,165 in the first pass, 2 gained and 2 lost after reruns, none solid; ITS +3, TIP, SV, the
  frontier corpora and the real-world corpus level within one flip of noise;
- the 332 step goals the same search; suites 225 of 225, Lean 48 of 48; size +1,347 bytes.
