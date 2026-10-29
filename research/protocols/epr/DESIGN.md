# A fast decision path for EPR-shaped goals: design round and probe

The question: DuoAI's checks are EPR queries of a second or less, and gdp-wired's are full kernel goals that cost 90 to
900+ s on the protocols it misses (enum/DESIGN.md, COST.md). Can an untrusted decision path for EPR-shaped goals check
them fast, with every refutation still a certificate today's kernel checks? This note measures the blocking goals with
a real solver, reads where ours fails, designs the path, and says what is trusted. Nothing is built into the library.

    bun research/protocols/epr/goals.ts <protocol> <dir>          # every law's step goal of the written invariant, as JSON
    bun research/protocols/epr/tosmt.ts <goal.json> <out.smt2>    # the goal as SMT-LIB 2 (QF_UFLIA): unsat iff proven
    python3 research/protocols/epr/z3time.py <files> [--model]    # Z3 4.13 on each, 60 s each

Figures come from `runs/epr/` in the gen/epr worktree (gitignored) unless they cite another round.

## The answer in short

- **The goals are easy; our engine is weak on them.** Translated as they are, maps as functions of one integer key and
  the naturals' arithmetic kept, the blocking goals are small ground problems: 11 to 14 names and 49 to 251 cells. Z3
  4.13 decides each in at most 8.0 s, most under 1 s. Ours takes 90 to 900+ s on them, or never finishes.
  - **Sharded KV:** every step goal of the written invariant is unsat in Z3, 0.02 to 8.0 s, about 9.4 s in all. The
    two goals our kernel never settles take 0.6 s ("a key in transfer has no owner", 748 hypotheses; the kernel
    unknown at 456 s) and 8.0 s ("one transfer per key", 985; unknown even as a 57-hypothesis part at 210 s).
  - **consensus_wo_decide:** laws 5, 6, 7 and 9 are unsat in Z3 in 0.03 to 0.2 s. Laws 8 ("a leader has the voting
    quorum's votes") and 10 ("one leader") are sat in 0.1 to 0.2 s at the full instance set `lawInstances` gives:
    models a tuple short. In our encoding law 8 is provable once the quorum witness w is in the tuples that "a counted
    vote was sent" and "one vote message per voter" are assumed at (below). The kernel's search ran 586 s on law 8
    without a model or a proof.
  - **toy_consensus_forall:** the safety goal's model in 0.03 s (the tree search took 108 s before point phases); "one
    vote per node" unsat in 0.04 s (3.9 s ours).
- **What is weak in ours:** integer reasoning over composed keys. A cell of a relation over two or three sorts is
  `M[a·64² + b·64 + c]`, so equality of two such cells is integer arithmetic on keys:
  - Fourier–Motzkin elimination blows up at the leaves (COST.md: 670 to 760 rows, simplex-feasible, no integer point);
  - the clausal CDCL mode stops "no split" on sharded KV's 5-key goal in 1.8 s for the same reason;
  - branch and bound at those leaves moved nothing in 600 s (COST.md, step 5).
- **The path: decide by equality of key parts, not by arithmetic on keys** (kernel/epr.ts, untrusted, described in
  section 3):
  - a composed key as the tuple of its parts (its digits under the frame bounds);
  - a yes/no cell as a propositional atom per (map, tuple);
  - the parts' equalities as atoms with transitivity, and congruence for cells;
  - CDCL over that;
  - a model read back as a kernel witness, which the existing model rounds judge.
- **The trust question: nothing trusted needs to change, by construction.** A refutation of the abstraction unfolds
  into today's certificate, a split tree over the goal's linear atoms. Each leaf is one of three things, all refuted by
  kernel.ts's linear reading at that path, as today:
  1. a hypothesis false under the path;
  2. a transitivity or congruence instance;
  3. the injectivity of a composed key under its parts' bounds (`a ≠ a' ∧ 64a + b = 64a' + b'` with `b, b' < 64`).

  The cost is the unfolding: a CDCL refutation, unfolded, can be exponentially larger than its DAG. cdcl.ts already
  unfolds its DAGs under a leaf cap. Only a resolution certificate over ground clauses would avoid that, and it would
  be a trusted change (Lean-first). Not proposed now.
- **Recommendation:** build the abstraction's probe next, on sharded KV's 9 step goals and consensus_wo_decide's 6,
  measured against Z3's times above: time to decide, and the unfolded tree's size against cdcl.ts's leaf cap. It is
  search-only but not small, about 400 to 600 lines (section 5), so per the brief this round stops here and reports.

## 1. What the blocking goals are

A kernel goal is ground: the laws are assumed at the tuples the prover chose, so there is no quantifier left. What
remains is a conjunction of hypotheses over naturals: linear terms, if-then-else, truncating subtraction, min/max, and
reads of maps at key terms. `tosmt.ts` writes it as QF_UFLIA. Each map is a function of its key, every name and cell is
at least 0, and every hypothesis is asserted. The goal is proven iff the formula is unsat.

| Goal (step goal of the written invariant) | Hypotheses | Names | Cells | Z3 4.13 (Modal, 1 job) | Today's kernel path |
| --- | --- | --- | --- | --- | --- |
| sharded KV 3, one owner per key | 547 | 12 | ~50 | unsat 0.04 s | proven, 1.1 s (COST.md r1) |
| sharded KV 4, a table entry is its owner's | 798 | 12 | ~50 | unsat 0.07 s | proven, 2.0 s |
| sharded KV 5, a key in transfer has no owner | 748 | 12 | 49 | unsat 0.62 s | unknown at 456 s (`runs/prune/p1`) |
| sharded KV 6, one transfer per key (5 keys) | 985 | 13 | 65 | unsat 7.98 s | never reached; its 57-hypothesis part unknown at 210 s |
| sharded KV 7, one value per owner and key | 1,026 | | | unsat 0.17 s | never reached |
| sharded KV 8, nothing in the table before start | 744 | | | unsat 0.02 s | never reached |
| sharded KV 9, one value per key (the safety law) | 1,264 | | | unsat 0.53 s | never reached |
| consensus_wo_decide 5, a vote message means voted | 1,126 | | | unsat 0.05 s | proven, 1.1 s |
| consensus_wo_decide 6, one vote message per voter | 1,335 | | | unsat 0.20 s | proven, 11.1 s |
| consensus_wo_decide 7, a counted vote was sent | 1,272 | | | unsat 0.06 s | proven, 4.5 s |
| consensus_wo_decide 8, a leader has the voting quorum's votes | 1,212 | 14 | 251 | **sat** 0.11 s | unknown at 586 s |
| consensus_wo_decide 9, nothing before init | 927 | | | unsat 0.03 s | never reached |
| consensus_wo_decide 10, one leader (the safety law) | 1,055 | | | **sat** 0.23 s | never reached |
| toy, one value decided (old dump, before model rounds) | 377 | 11 | 122 | sat 0.03 s | a model at 108 s (1 s with point phases) |
| toy, one vote per node | 604 | 12 | 170 | unsat 0.04 s | proven, 3.9 s |

The goals are those `goals.ts` builds: each law's step goal at `lawInstances`' tuples, the instances `proveLaw` starts
from, before `withModels` adds any. So a sat answer there may be a model a tuple short, not a counterexample.

**consensus_wo_decide's model at law 8, read.** The request is `choose_voting_quorum` (op 4) with Q = {29, 31} and the
stored voting quorum {31}. It leaves a leader whose votes don't cover Q. In our encoding the step is safe:
- Ivy's quorum axiom, here assumed of Q and the stored quorum at the request's witness w, gives `Votes[n·N + w]` (the
  leader's) and `Votes[src·N + w]` (Q's, by `quorumVotes`);
- "a counted vote was sent" makes both votes messages from w, and "one vote message per voter" makes n = src.

Those three laws must be assumed at tuples through w, which `lawInstances` doesn't name. `modelInstances` reads such
models and adds the tuples; the decision path must keep that loop (section 3).

## 2. Why ours is slow where Z3 is fast

Both are DPLL(T)-style searches over the same atoms. The differences that matter here:
- **Integer feasibility at the leaves.** Our leaves are decided by exact Fourier–Motzkin elimination with cuts. On
  sharded KV it blows up at 670 to 760 rows over 55 variables, where the simplex is feasible and no integer point
  exists. Z3's arithmetic is an incremental simplex with branch and bound, cuts and a relevancy filter (Dutertre and de
  Moura 2006; de Moura and Bjørner's relevancy propagation). It never eliminates.
- **Equality of cells.** We list every pair of one map's cells as a case to split on (COST.md: 53% of toy's profile
  before gen/cost2). Z3 merges cells by congruence closure only where two keys are equal in the E-graph.
- **Phases.** Our tree search decides by saved phases and wanders before a model (toy: 181k nodes). Z3's model comes
  from the arithmetic's point. gen/cost moved our proof path to the simplex's point on laws over several keys.

The first is the one no measured change of ours moved (COST.md steps 3 to 5, gen/prune). It is also the one the EPR
shape makes unnecessary. In Ivy's models the two keys of `table(N, K, V)` are uninterpreted sorts, so there is no
arithmetic on keys at all. Ours has arithmetic on keys only because of the encoding `a·N² + b·N + c` (README.md, "The
encoding").

## 3. The design

### Recognising an EPR-shaped goal

The test is syntactic, on the goal's hypotheses (kernel/epr.ts `shape`), and untrusted. A wrong answer only sends a
goal down the slower path.
- **Every map read's key is a radix tuple.**
  - Its linear form is `Σ cᵢ·xᵢ + d` with the coefficients a chain: each a multiple of the next by at least N, the last
    1.
  - Each part xᵢ is bounded by the frame below its place's base (`x < N`): a hypothesis of the goal, or of the law's
    guard at the instance.
  - A plain key `M[x]` is the one-part case.
- **Every comparison between keys is of radix tuples.** Equality is part by part. An interval write over a composed
  key (sharded KV's `put`, `z ≥ pk3 − v ∧ z < pk3 − v + N`) is the equality of its upper parts. A comparison of key
  parts by order (`e < Ep[a]`, epochs) is an order atom, as Ivy's `le`, with its transitivity and totality as clauses.
- **Every cell is few-valued** (its kind: a yes/no, a choice), or a value compared only with other values of its sort
  (an epoch, as in DuoAI's order atoms).
- **What isn't EPR:** a counter's arithmetic (`next + 1`), a sum, a product, a cell added to another as a number. A goal
  with these is not EPR-shaped and keeps today's path. Protocol goals mostly qualify: the 0/1 sums of the consensus
  laws are at-most-one constraints over yes/nos, which the abstraction states as clauses. Counters, sums and every CHC
  task do not, so the path is off there by construction.

### Deciding it

1. **Atoms.**
   - The equalities between key parts of one sort: the goal's own terms, its skolems, the request's inputs, the
     quantified flags' witnesses. The EPR small-model property: no fresh element is needed past the terms that occur,
     for a ground goal.
   - One atom per yes/no cell at a tuple of part terms.
   - The order atoms of an ordered sort.
   - For few-valued cells, one atom per value.
2. **Clauses.**
   - Each hypothesis by Tseitin (reader.ts's `Clausal` already writes the goal's hypotheses as clauses over linear
     atoms; here the atoms are the abstraction's).
   - Equality's reflexivity, symmetry and transitivity over each sort's part terms (Bryant and Velev's equality
     encoding, cubic in the terms of a sort: about 10 a sort here).
   - Congruence: two cells of one map at tuples whose parts are equal are equal.
   - Order: transitivity and totality, where a sort is ordered.
3. **Search.** CDCL: the clausal mode's propagation, learning and activity heap, with no simplex, since nothing is
   arithmetic.
4. **Answers.**
   - **A model** is read back as a kernel witness. Each part gets a value per equivalence class, below its bound. A
     composed key's value is the tuple's radix sum. Each cell takes its atom's value. `withModels` judges it as today:
     a model a tuple short gets its tuples and the goal is asked again.
   - **A refutation** is a DAG of learned clauses. It is unfolded into a kernel tree as cdcl.ts unfolds its own (the
     next section).

### The certificate

The kernel's certificate is a tree:
- **A split** is a linear atom: an atom of the goal, or any linear form, as cdcl.ts and `fractional` split on.
- **A leaf** is a derivation of `1 ≤ 0` from the kernel's rows at that path (kernel.ts `leafConstraints`): the
  hypotheses' facts under the path, each cell's natural row, and a cell equality row for every two cells of one map
  whose key difference the path decides both ways.

The abstraction's atoms map onto linear atoms:
- a part equality `x = y` is the split on `x − y ≤ 0` and then `y − x ≤ 0`;
- a yes/no cell atom is the split `M[t] ≤ 0`;
- an order atom `x < y` is `x − y + 1 ≤ 0`.

A resolution refutation over clauses whose atoms all have such splits unfolds into a tree with these splits. Its leaves
are where the path falsifies one clause, and each clause is one of three kinds, each refuted at that path from the
kernel's own rows:
- **A hypothesis' clause.** Under a path that decides every atom it reads, kernel.ts's truth reading makes the
  hypothesis false, and its fact row is `1 ≤ 0`.
- **A transitivity clause** (`x = y ∧ y = z → x = z`). The path's rows `x − y = 0`, `y − z = 0` and `x − z ≥ 1` refute it
  by one combination.
- **Congruence, and the composed key's injectivity.** Two cells `M[64a + b]` and `M[64a' + b']` with `a = a'` and
  `b = b'` decided need the key difference `64(a − a') + (b − b')` decided both ways for the kernel's cell equality row.
  So the unfolding adds that split: its `≥ 1` side is refuted from `a − a' = 0` and `b − b' = 0`, and its `= 0` side
  gives the equality row. In the other direction, `a − a' ≥ 1` with `64(a − a') + b − b' = 0` and `b' ≤ 63`, `b ≥ 0` is
  `64 ≤ 63`. Every leaf is linear and small.

So the existing tree format, checked by kernel.ts and its Lean twin as today, carries the abstraction's refutations:
**no trusted change**. Two costs remain, both search's:
- **The unfolding's size.** A DAG refutation unfolded into a tree is exponential in the worst case. cdcl.ts unfolds its
  own under `maxLeaves` (20,000), and its trees have been the certificates since the CDCL search went in. The probe
  must measure the trees on these goals.
- **The atoms' order.** The congruence splits must come after the part splits on each branch, so a cell's key
  difference is split only where its parts are decided. The unfolding chooses the order, the kernel doesn't care.

**When a new certificate would be needed, and why it isn't proposed now.** If the unfolded trees exceed the leaf cap on
these goals, the alternative is a resolution certificate: the ground clauses, each checked as a consequence of a
hypothesis or as an equality or congruence axiom instance, and a resolution derivation of the empty clause. That is a
new certificate form and a trusted change:
- **Lean first:** a theorem that a checked resolution derivation from those clauses refutes the goal, on the standard
  axioms (propext, Quot.sound, Classical.choice), with the TS checker its exact mirror;
- **why not now:** nothing yet shows the trees are too big, and the tree route needs no trusted change.

The probe decides which.

## 4. The literature

| Tool / work | What it does for EPR goals | Here |
| --- | --- | --- |
| Ivy (Padon et al. 2016; Padon, Losa, Sagiv, Shoham 2017) | keeps every verification condition in EPR: relations over uninterpreted sorts, no arithmetic on elements, total orders as axiomatized relations; Z3 decides them with finite models | the shape test; sorts as tuples of parts, orders as atoms with axioms |
| Z3's EPR decision (de Moura, Bjørner, IJCAR 2008; with Piskac, JAR 2010) | DPLL with substitution sets, complete for the Bernays–Schönfinkel class, a clause standing for its ground instances | our goals are already ground (the prover's instances): plain CDCL over ground clauses suffices; the instance choice stays `withModels`' |
| MBQI (Ge, de Moura 2009) | instances from a candidate model that breaks a quantifier | `withModels`/`modelInstances`, kept: the abstraction's models feed it |
| Equality logic to SAT (Bryant, Velev 2002; Ackermann's reduction) | `e_ij` atoms with transitivity clauses; functions by congruence | the part equalities and the cell congruence clauses |
| iProver (Korovin 2008) | Inst-Gen: instantiation with a SAT solver on the ground abstraction, complete for EPR | the shape of the loop: ground, solve, instantiate where the model breaks a law |
| Paradox (Claessen, Sörensson 2003) | finite models by SAT with static symmetry reduction per sort | the model side: a model over each sort's terms; symmetry reduction a later option |
| Simplex for DPLL(T) (Dutertre, de Moura 2006) | integer arithmetic by an incremental simplex, branch and bound and cuts, never elimination | the path off for arithmetic; the alternative design (a stronger integer theory in cdcl.ts) |

**Search or trusted, for each piece:**
- **Search:** the shape test, the abstraction, the clauses, the CDCL, the model's read-back, the unfolding.
- **Trusted:** only a resolution certificate, if the trees prove too big, and only after its Lean theorem.

## 5. What the build would be, and the next measurement

| Piece | Where | Size |
| --- | --- | --- |
| The shape test: radix keys, part bounds, cell kinds, orders | kernel/epr.ts | ~100 lines |
| The abstraction: atoms, Tseitin over hypotheses, equality and congruence clauses | kernel/epr.ts (reusing reader.ts's Clausal where the atoms are linear) | ~150 |
| The CDCL | the clausal mode of kernel/cdcl.ts, its theory off, or a small one in kernel/epr.ts | ~0 to 150 |
| The model's read-back as a kernel witness | kernel/epr.ts | ~40 |
| The unfolding into a kernel tree (part splits before congruence splits) | kernel/epr.ts, beside cdcl.ts's `unfold` | ~100 |
| The hook: growRoot, an EPR-shaped root goal first by the path, today's after | kernel/prove.ts | ~10 |

About 400 to 600 lines, all search. **The measurement that decides the build**, run on its probe before any hook:
- **Sharded KV's 9 and consensus_wo_decide's 6 step goals** (`goals.ts`):
  - time to decide, against Z3's 0.02 to 8 s above;
  - for each refutation, the unfolded tree's leaves against the 20,000 cap, and `check` on the whole goal.
- **The answer must agree with Z3's on every goal:** sat where it is sat, unsat where unsat. A disagreement is a bug in
  the abstraction (the shape test let an arithmetic fact through).
- **If the trees fit:** hook it into growRoot, gated on the shape. Then measure:
  - the pilot, three runs at 60 s;
  - the 30 multi-key real-world laws;
  - the quick bar against 383928a;
  - a full bar `--together`.

  It is off on CHC by construction (no maps).
- **If the trees don't fit:** the resolution certificate, Lean-first, is the next design round, not a build.

**What it would close, if it works.**
- **sharded KV's written invariant:** all its step goals are refutable, so proven.
- **consensus_wo_decide's:** laws 8 and 10 only after `withModels` finds the tuples through w.
- **The search:** both protocols' nothing-written searches need their checks this cheap to reach their candidates
  (enum/DESIGN.md), and distributed_lock's 4-key goal over 124 enumerated laws is the same kind (not measured here).
- **The verdict at 60 s:** not shown here. This path makes the checks cheap; the candidates are enumeration's.

## Citations

- Padon, McMillan, Panda, Sagiv, Shoham. Ivy: Safety Verification by Interactive Generalization. PLDI 2016.
  [PDF](https://ilyasergey.net/CS6213/_static/papers/ivy.pdf). Padon, Losa, Sagiv, Shoham. Paxos Made EPR. OOPSLA 2017.
- de Moura, Bjørner. Deciding Effectively Propositional Logic Using DPLL and Substitution Sets. IJCAR 2008; with
  Piskac, JAR 2010. [MSR](https://www.microsoft.com/en-us/research/?p=153263).
- Ge, de Moura. Complete Instantiation for Quantified Formulas in Satisfiability Modulo Theories. CAV 2009.
  [Springer](https://link.springer.com/doi/10.1007/978-3-642-02658-4_25).
- Bryant, Velev. Boolean Satisfiability with Transitivity Constraints. ACM TOCL 3(4), 2002.
  [ACM](https://dl.acm.org/doi/10.1145/566385.566390).
- Korovin. iProver – An Instantiation-Based Theorem Prover for First-Order Logic. IJCAR 2008.
  [PDF](https://korovin.gitlab.io/pub/iprover_descr_08.pdf).
- Claessen, Sörensson. New Techniques that Improve MACE-style Finite Model Finding. CADE-19 workshop, 2003.
  [PDF](https://lara.epfl.ch/w/_media/projects/paradoxpaper.pdf).
- Dutertre, de Moura. A Fast Linear-Arithmetic Solver for DPLL(T). CAV 2006.
  [Springer](https://link.springer.com/doi/10.1007/11817963_11).
- de Moura, Bjørner. Relevancy Propagation. MSR-TR-2007-140. [MSR](https://www.microsoft.com/en-us/research/?p=153156).

## Spend

Modal: two Z3 jobs (7.9 s and 14.9 s of job time) and the earlier dumps local: under $0.01. Nothing is left running.

## Built: kernel/epr.ts and its hook (gen/epr)

**What was built differs from section 3 in one place, the certificate.** The design unfolded the abstraction's
refutation into a tree. The build uses its core instead:
- the CDCL keeps each clause's hypotheses, so a refutation names the few hypotheses it read (2 to 13 on these goals);
- kernel/prove.ts's usual search proves the goal over those alone, a weaker goal, in 15 to 431 ms;
- `widen` makes that tree one of the whole goal, as it does for core/cyclic.ts's parts, and kernel.ts checks it.

That needs no unfolding code and no new certificate, and the trees are small: 11 to 417 leaves against the cap of
20,000.

**What the abstraction reads.**
- **Keys.** A key at its map's pattern (the rule's reads, `patternsOf`) is a tuple of parts.
- **Comparisons.**
  - A key equality is the equality of the parts, where the parts are under their bounds.
  - `L ≤ X` and `X < L + c` (put's row interval) are an equal prefix.
  - `a ∸ b` with b's terms in a is exact.
  - A part against a constant is a bound atom.
  - A comparison of finite terms (cells, scalars, if-then-else) against constants is enumerated over capped values.
- **Ill-sorted reads.** A read at a key of the wrong sort (an instance at a composed key in a part's place) is a cell of
  its own, with no congruence.
- **Opaque atoms.** Anything else is an opaque atom.
- **Soundness.** Every clause added holds in every model of the goal, so unsat is sound.

The hook asks it first on a rule with a composed key, and only where no opaque comparison reads a scalar or a cell
(counters, sums, products). Rules with no maps (every CHC task) have no patterns, so it is off there by construction.

**The probe** (`probe.ts`, 28 step goals of four protocols, Modal, `runs/epr/all1`):

| Protocol | Goals | Agree with Z3 | Certified (core, leaves, checked) | No answer |
| --- | --- | --- | --- | --- |
| sharded_key_value_store | 7 | 7 unsat | all 7: core 2–10, 12–417 leaves | 0 |
| consensus_wo_decide | 6 | 4 unsat, 2 sat | all 4: core 3–8, 11–79 leaves | 0 |
| toy_consensus_forall | 5 | 4 unsat, 1 sat | all 4: core 3–13, 11–276 leaves | 0 |
| distributed_lock | 10 | 1 unsat | 1: core 5, 66 leaves | 9 (its epochs need order atoms, not built) |

No answer disagrees with Z3's. Decisions take 19 to 273 ms.

**In the prover** (Modal, three runs a side, `GDP_EPR=0` against on; `runs/epr/m1`):
- **sharded_key_value_store's written invariant: proven in every run, 22.3–26.3 s.** It was killed at 150 s in every run
  without the path, and never proven before.
- **consensus_wo_decide's written invariant:** law 8 ("a leader has the voting quorum's votes"), unknown at 586 s
  before, is proven: the path's models (about 40 ms each) give `withModels` its tuples, then a 13-hypothesis core is
  proven. The safety law still ends in models.
  - The first was a real counterexample to induction: an empty voting quorum lets any node lead. The written set
    lacked "after init the voting quorum has a member", now added to models.ts as an ∃ law with the request's witness
    as its ghost, and proven.
  - The later models are a tuple short at the ghost, which `modelInstances` doesn't propose (the model rounds end
    with nothing to add): instance choice, not the decision. Unknown at 20–26 s, where it was killed at 150 s.
- **The searches at 60 s:** the same five proven in every run both ways (sync, async, decentralized, 2PC, ticket). The
  misses end sooner: toy 11–13 s against 15–19, wo about 28 s against 34–45, sharded KV 35–38 s against 48–53.
- **Broken variants:** refused by the same runs in every run.
- **The 30 real-world laws over several keys:** the same verdicts, 637 s against 644 s.

**The bars** against 383928a (base launched together: no shared baseline of 383928a; `runs/bar/runs/epr-quick-b056b08`,
`epr-full-b056b08` in the main checkout). Wrong 0 everywhere, nothing lost in every run anywhere.
- **Quick (chc, rw dev):** CHC 518 against 522, 1 gained and 5 lost after reruns, none solid, all 5 at the time limit
  (CHC has no maps: the path never runs there). Real-world dev 74 / 14 / 3, nothing differs.
- **Full:**
  - CHC 1,169 against 1,159 in the first pass: 3 gained, 4 lost after reruns, none solid.
  - ITS 1,150 against 1,148, and 1,156 against 1,155 per component. SV, TIP and the frontier corpora level.
  - The real-world corpus 289 / 33 / 8 both ways.
  - The 332 step goals: the same search on all 332, 288 s against 304 s.
  - Suites 225 of 225 both ways (5,663 against 5,695 job seconds; --usual 5,138 against 5,187). Lean 48 of 48.
  - The 1-vCPU medians within 5%.
- **Size:** core/ and kernel/ without tests +34,407 bytes, almost all kernel/epr.ts.

**Spend** (this track): the probes and the pilot about $0.25; the quick bar $1.85 and the full bar $11.02, both
estimated by the bar from task seconds (their hours not yet billed). About $13.1 of the $15.

## gen/epr2: the ghost's instances, order atoms, a slimmer epr.ts

**1. Model instances at the goal's own names, witnesses first** (kernel/prove.ts `modelInstances`).
- **The cause:** consensus_wo_decide's safety goal ended in models through every round. Each round's 20,000
  evaluations went to laws over three keys at 91 to 178 key values, most of them composed terms in a part's place
  (instances at keys of the wrong sort). The tuples through the ∃ law's ghost were never reached.
- **The fix, general:**
  - each sort ranges first over the goal's own names: skolems, the request's inputs, flags' witnesses, ∃ ghosts;
  - witnesses come first;
  - every key the goal reads is tried only where those show nothing.
- **Least values:** kernel/epr.ts's models take the least values of their finite variables, so they break no kind law at
  keys nothing names.
- **Two fixes to our model** (models.ts): the quorum member is below N (as every request's quorum is), with the ∃ law
  from gen/epr.
- **Result:** consensus_wo_decide's written invariant is proven in every run (30.6–42.7 s).

**2. Order atoms** (kernel/epr.ts).
- **Which terms:** a map's cells, or a scalar, compared with another non-constant term (distributed_lock's epochs: `e ≤
  Ep[a]`, `Ep[b] < Ep[a]`, the step's `Ep := e`) are ordered terms, with parts, constants and if-then-else over them.
- **The axioms:** the order is total, transitive and discrete, with the constants in their order and every term at
  least 0, all true over the naturals.
- **Result:** distributed_lock's step goals went from 1 decided of 10 to 10 of 10, all agreeing with Z3; its written
  invariant takes 6.4–10.8 s against 13.0–15.8 s.
- **A cap:** a join query that compares cells with cells made whole maps ordered, and the order's cubic transitivity
  took consensus_wo_decide's search from 43 to 157 s of wall time. A goal with more than 64 ordered terms now keeps the
  usual path.

**3. Slimmer.** Every part is an ordered term, and its bound and equality are the order's. The bound atoms, equality's
own transitivity, the bounds' monotonicity and congruence, and the parts' class-by-class read-back are gone.
- **Bytes:** kernel/epr.ts 40,755 after the order atoms, 38,231 after (−2,524), 38,428 with the cap.
- **What isn't shared:**
  - the CDCL, because cdcl.ts's is over linear atoms with a simplex and this one is propositional with each clause's
    hypotheses;
  - finite variables as ordered terms, because the order's transitivity is cubic and wo's goals hold 141 finite
    cells.

**Measured** (Modal, three runs a side, against e537601: `runs/epr2/p2` base, `p3` candidate):
- **Written invariants: 10 of 10 proven in every run.** consensus_wo_decide's was unknown at e537601.
- **The searches at 60 s:** the same five proven in every run (sync, async, decentralized, 2PC, ticket). Times are level
  but the misses' ends:
  - consensus_wo_decide 33–59 s against 22–34 s;
  - toy 16–18 s against 12–14 s.
- **Where the misses' time goes:** wo's search took 34 s with the path off on the same tree. The path's work isn't on
  the search's counted clock, so the join asks more queries in the same counted budget. Counting it would need a
  calibration that could cost other searches their proofs; not done.
- **lock_server_async:** level, 16.8 and 21.7 s on against 25.0 and 18.2 s off; not the path.
- **Broken variants:** refused by the same runs.
- **The 30 real-world laws over several keys:** the same verdicts, 607 s against 594 s.
- **The quick bar against e537601:** CHC 521 against 518 (2 gained, 1 lost after reruns, none solid); real-world dev 73
  against 74 in the first pass, noise after reruns (lost 0); wrong 0.
- **The full bar against e537601** (base together; `runs/bar/runs/epr2-full-a14265f`): wrong 0 everywhere, nothing lost
  in every run anywhere.
  - CHC 1,165 against 1,174 in the first pass: 2 gained and 7 lost after reruns, none solid, 5 of the 7 at the time
    limit. CHC has no maps, so neither the EPR path nor the changed model instances run there.
  - ITS 1,153 against 1,151, and 1,157 both per component. SV, TIP and the frontier corpora level. The real-world
    corpus 288 / 33 / 8 / 1 timeout against 288 / 33 / 9, noise after reruns (lost 0).
  - The 332 step goals: the same search on all 332, 293 s against 308 s.
  - Suites 225 of 225 both ways.
  - The 1-vCPU medians within 10% (infer's four-value join 6,139 against 5,599 ms).
- **Lean: 47 of 48.** The one not checked is slayer-3.t2_fixed, an ITS task this run solved (nonterminating in 48 s;
  the base's first pass unknown, so it was sampled first as gained). Its 17 MB certificate stops at Lean's
  `maxRecDepth`, using the standard axioms only. ITS has no maps: none of gen/epr2's code runs there.
- **Size:** core/ and kernel/ without tests +7,517 bytes against e537601. kernel/epr.ts is 38,428 bytes, against 40,755
  before the slimming.
- **Spend:** about $13.1 of $14: the probes and pilots about $0.35, the quick bar $1.78 and the full bar $10.95 (the
  bars' estimates; their hours not yet billed).

## gen/epr3: functions of a key, exact cells, the search's end on the wall, many-key instances

Branch gen/epr3 from b2df5dc. Nothing trusted changed: every refutation is still the usual search's tree on the core,
widened and checked by kernel.ts.

**1. A function of one key is a part (ring_leader_election).** `idn(n)` read at a part is a part of its own, `idn(n)`
(patterns `[0]`): a key `Pending[idn(n)·64 + n]` is a tuple of two parts. Functions are Ackermann's: equal arguments,
equal values (a clause). The rule's injectivity is its fact, an instance among the hypotheses like any other law. A
successor (`n1 = n + 1`) is an atom with nothing between, one way. A read at a key of the wrong sort (`idn(64·m + n)`) is
key-only, and the read-back gives it a value of its own, the least unused, so an injective function's instance there
holds.
- **Probe** (`probe.ts`, Z3 4.13 on Modal, `runs/epr3/all1`): ring's four step goals decided, three refuted (cores
  proven, widened, checked) and one satisfiable, all as Z3. The 28 step goals of skv, wo, toy and distributed still
  agree.

**2. The enumeration's goals (traced on gen/enum3, 44fe305, with these changes).**
- **distributed_lock:** the four-key cube took 48 s and the three-key ones 2–7 s in the usual search, because the EPR
  path refused them. Their wrong-sort instances compare an epoch cell with a composed key (`Ep[x] + 1 <= 64·z + n`).
  An ordered cell is key-only beside a composed key, so these goals are now decided: 0.1–0.4 s each. Nothing in the run
  is over a second.
- **consensus_wo_decide:**
  - **Ordered terms.** The 361 and 381 ordered terms were yes/nos compared as implications (`Leader[k] <= Voted[k]`).
    A cell or scalar that a hypothesis bounds (`M[t] <= 1`, a kind's instance) is now exact: values 0 to the bound,
    compared with any finite term by cases, not ordered. That hypothesis is the origin of its one-hot clause, so a core
    keeps it. Ordered terms: 57 → 9 and 89 → 10 on the dumped goals.
  - **The cap.** Past 64 ordered terms, transitivity is lazy (the model's broken triples added, 16 rounds at most), up
    to 512 terms.
  - **The 65 s search** was proveLaw's thinned goals outside the EPR path's scope. Now 0.5 s.
  - **What is left:** the 29,130-hypothesis goal of the candidate `Leader[k] <= VoteRequestMsg[k]` (a relation of
    pairs read at one key). Its wrong-sort reads have no bound, so `started` and four maps stay ordered. 4,264
    comparisons are outside the shape, and the usual search takes 12.5 s to unknown. That candidate is the template's.
  - **The spurious model** is a real model of the ground goal (every EPR model is validated with evalC), with too few
    instances. Model rounds add the rest where the model's keys can be read.
- **sharded KV:** the caller goal held 112,587 hypotheses: five-key laws at 24,608 tuples each, from `matched`'s
  paired matches. Building took 10 s and each EPR decision 20–38 s. A law about several keys now takes at most 512
  related tuples (each place's own focus key first) and 512 paired matches, and the model's tuples add the rest. Now
  8,139 hypotheses, 0.3 s to build, about 1 s a decision, and skv's run 304 s → 42 s.
- **ring (written invariant):** a model's cell at a key that reads a cell (`Pending[idn[n]:64,n]`) was skipped by
  modelInstances (keyValue), so 'one leader' never got its instance. Now valued, and proven.

**3. The search's end on the wall.** proveRule's search runs inside `withWall(end)`. `late()` reads it, and so do grow,
the EPR path's propositional search (every 256 conflicts), model rounds, model instances and instance building. Past it,
a goal is unknown. The counted clock still decides everything before the end, so verdicts don't depend on the machine
except past the search's own end.
- **Test:** research/protocols/epr/deadline.test.ts, on gen/enum3 with these changes (Modal, 4 of 4).
  - ring at 2 s and 5 s: 1.6 and 4.5 s past the 0 ms base.
  - wo at 5 s and 10 s: 4.2 and 10.1 s past it.
  - wo at 2 s overruns by 0.8 s in core/infer.ts's runs, a fixed 16,000 requests, about 1.4 s of wall time at any
    budget. That is the enumeration's side.
- **gen/enum3's 60 s runs** with these changes: ring 14 s, distributed 47 s, sharded KV 42 s (304 s before), wo 67 s
  (154 s before).

**Not done: charging the EPR path's work to the counted clock.** It would change how much every counted search may do,
so it needs a calibration that could cost other searches their proofs. The wall end now bounds the work it hides.

**Measured on gen/epr3** (Modal, three runs, against b2df5dc: `runs/epr3/p1b` base, `p2c` candidate):
- **Written invariants:** 10 of 10 in every run. wo 27–29 s against 31–37 s, skv 15–19 s against 19–25 s.
- **Searches at 60 s:** the same 6 proven in every run. skv's miss ends at 19–20 s against 35–38 s; wo's at 49–54 s
  against 41–46 s.
- **Broken variants:** refused by the same runs.
- **The 30 real-world laws:** the same verdicts, 584 s against 602 s.
- **The quick bar against b2df5dc** (`runs/bar/runs/e38d91ac7027+960092bb-vs-b2df5dc1fca8-quick-2026-10-291427`): wrong 0
  everywhere, nothing lost solidly (CHC lost 1 and ITS lost 2 after reruns, all at the 60 s limit, noise). SV, TIP, the
  frontier corpora level. The 332 step goals: the same search on all 332, 291 s against 306 s. The 1-vCPU tests level.
  Lean 6 of 6.
  - **Real-world dev set:** 74 proven both. One refutation lost in the single candidate run: vendure's 'a placed order
    is cancelled only with every line cancelled'. Its shallow bounded run has its own 250 ms wall stop. When that stop
    misses the bug on a slow container, the last bounded run finds it, and the wall end had cut that run. That phase
    now has the wall lifted (its own stop stays). Rerun on Modal, refuted in 9.0–9.6 s on both sides.
- **The full bar was not run:** the quick bar's estimate is $15.6, since it made b2df5dc's shared baseline (21 runs),
  and that is past this round's budget. Suites and Lean beyond the quick sample are not measured.
- **Size:** core/ and kernel/ without tests +10,833 bytes against b2df5dc; kernel/epr.ts 46,725 bytes (+8,281).


## gen/epr4: no work past the wall, ring's caller goal proven, models as diagrams

Branch gen/epr4 from 9987874. Nothing trusted changed.

**Wall overruns under proveLaw** (traced on gen/enum3's stage, 857ebc9, with these changes; a stack sampler past the
wall found each):
- **ring's caller goal ran 300+ s past the end.** It was the function parts' congruence: a part was listed once per
  read, so its pairs grew with the square of the reads, not of the parts. Each part is now listed once.
- **Smaller ones, now checked:**
  - the EPR path every 4,096 clauses, hypotheses and read nodes (a throw, then unknown), including the order's walk
    and the read-back;
  - model instances per law;
  - triggered's rounds;
  - the cuts (`withCuts`, `growFocused`);
  - before a root goal's rows;
  - widen, at each node and between a leaf's two readings.
- **What isn't interruptible:** one kernel.ts reading of a large goal's rows (trusted, unchanged), about 0.3 s on
  7,000 hypotheses.
- **wo's search** still overruns by 4–6 s in core/infer.ts's `realCti`, the enumeration's own code.
- **Test:** research/protocols/epr/deadline.test.ts runs the two caller goals (callers/, dumped from the stage: ring's
  'one leader' with 33 cubes, wo's with 36) inside walls of 2, 5 and 10 s.
  - Modal, the last four runs: 38 of 40 checks within 0.5 s.
  - The two misses are ring at 5 s, ending at 5.6 and 5.8 s.

**Why the caller goals ended in a model:**
- **ring:** the EPR path's model broke its own hypotheses. These were injectivity and cube instances at keys of the
  wrong sort: `idn(64·m + n)`, with keys that nest them.
  - Such reads are now terms of the order, valued by the read-back.
  - Nested keys are valued from the tables so far.
  - Near constants get the constants between them on a retry (`k:0 < x < y < k:2` has no room otherwise).
  - With these, the model is a real model, and its rounds' instances prove the goal: proven alone in 4.3 s
    (laptop) and 6.6–8.5 s (Modal). It had taken 21 s to unknown in the usual search before.
- **wo:** the EPR path's model is real. After one round, no law fails at any tuple of the goal's keys, so this is not
  missing instances. The cubes are not inductive there: a second leader at a node with a quorum's vote. Whether that
  state is reachable is the enumeration's to judge (realCti).

**Models as diagrams.** decide's sat answer, and proveLaw's unproven one, carry a `Diagram`:
- the elements: the values of the parts and ordered terms, in order;
- each part's element, and each ordered scalar's;
- the scalars' values;
- each map's cells the goal reads, at tuples of elements;
- each function's table, element to element.

It is the pre-state and request of the step goal's model. Two models equal up to the order's renaming give the same
diagram.

**Speed.** The propositional search picks its decisions from an activity heap. The scan over every variable was a fifth
of a decision. The choices, models and cores are the same (byte-identical output on 46 goals).

**Symmetry breaking: not done.** Over the 32 step goals, the dumps and the caller goals, the propositional search is
about half of a decision after the heap, and the clause building is the rest. Lex-leader constraints cut only the
search's share. The protocols' goals are refuted or satisfied in a few hundred conflicts. So it would not pay here.

**Measured** (Modal, two runs, 60 s budgets with a 90 s kill; against gen/epr3's pilot, `runs/epr4/p1c`):
- Every verdict the same: written invariants 10 of 10, searches 6 of 10, broken variants refused by the same runs.
- The 30 real-world laws: the same verdicts, 609 s against 584 s.
- **The quick bar against 5d4da3f's cached baseline** (`runs/bar/runs/c8f7fc27e4f2+195ccb9c-vs-5d4da3f49013-quick-2026-10-291621`):
  - wrong 0 everywhere, nothing lost solidly;
  - CHC gained 2;
  - ITS, SV, TIP, the frontier corpora and the real-world dev set level;
  - the 332 step goals: the same search on all 332;
  - the 1-vCPU tests level, Lean 6 of 6.
- **Size:** kernel/epr.ts 51,849 bytes (+5,213), kernel/prove.ts +567, against 9987874.
- **Spend:** about $4 of $8: the bar's estimate is $2.71, plus the probes and pilot.

## gen/epr5: the enumeration's unsure cube goals decided

Branch gen/epr5 from e5253d4. Nothing trusted changed.

**The goals.** gen/enum4 (a33b07b) leaves 13 cube goals of ring and 21 of distributed_lock unsure in its first Houdini
round. Each took up to 2 s of CDCL and 2 s of proof. They are dumped in research/protocols/epr/callers/ring-cubes.json
and dist-cubes.json: the round's machine and laws, and the unsure cubes' indices.

**Why each was unsure:**
- **ring (13 of 13): the EPR path's model broke its own conclusion.** A successor atom (`n1 = n + 1`, the ring's next
  node) makes its two terms adjacent in the order, but the read-back gave them values two apart: odd values where
  there was room. A successor chain the model holds now gets consecutive values, pinned to a constant where the chain
  reaches one.
- **distributed_lock: all 21 were already models for the EPR path.** The stage's quick check is cdcl.ts's model mode,
  not the EPR path, and it ran out of its 2 s. The proof path then spent up to 5 s in model rounds.
  - One broke the model in its third model round, at a wrong-sort instance a round added (`key3 = 64·e + n`).
  - Keys of two shapes are now unequal in the abstraction. A model that has them equal is judged by its read-back; a
    refutation through them is re-proven by the usual search on its core.
- **None** fell outside the shape or hit a cap or a missing atom kind.

**Z3 4.13** (Modal) on the 34 step goals: sat on all 34, as the EPR path. The 32 protocol step goals and the two caller
goals still agree.

**decideLaw(m, laws, i)** (kernel/prove.ts) is a law's goals by the EPR path alone:
- each goal decided;
- a refutation's core proven and widened as growRoot's;
- a model's broken tuples added (model rounds) until it is a model on every tuple of the goal's keys;
- the model returned with its diagram;
- undefined where a goal isn't EPR-shaped, so the caller's proveLaw comes next.

Measured on Modal, every one of the 34 cubes is decided in at most 0.43 s (callers/ in deadline.test.ts, two runs).

**gen/enum4 with this kernel** (two runs at 60 s each, a 90 s kill). In a scratch copy of its stage, the quick check asked
decideLaw first (research/protocols/epr/decideLaw.patch, for the engine agent):
- ring: 46 and 48 cube decisions in the run against 21 and 28 without it;
- distributed: 100 and 54 against 77 and 76, the run ending at 60 and 52 s;
- both still unknown.

The cubes are models now, fast. That a model is no real counterexample (realCti) keeps them unsure, and unsure cubes
are dropped only where no real one is. That judgment is the stage's.

**Deadline test** (Modal, two runs): 23 of 24 checks pass. Ring's caller goal ended at 5.52 s once at a 5 s wall.

**The quick bar against 5d4da3f's cached baseline** (`runs/bar/runs/431e6caf6548+d0a3d1cb-vs-5d4da3f49013-quick-2026-10-291716`):
- wrong 0 everywhere, nothing lost solidly;
- CHC, ITS, SV, the frontier corpora and the real-world dev set level;
- the 1-vCPU tests level, Lean 6 of 6.
- **TIP:** 93 against 94 in the first pass, the one task at the limit. Rerun alone: 94 against 94.
- **The 332 step goals didn't run on either side.** Their goals' directory (runs/modal/dag/goals in the main checkout)
  is gone. That is the bar's input, not this branch.

**Size:** kernel/epr.ts +1,154 bytes, kernel/prove.ts +1,578, against e5253d4. **Spend:** about $3.5 of $6, the two bar
launches estimated at $2.72 and about $0.3, the probes and pilots the rest.
