# Enumeration as a mode of the invariant search: DuoAI's candidates, gdp-wired's kernel

The question: can DuoAI-style enumeration of candidate invariants become one more mode of gdp-wired's invariant search,
for rules with keyed maps, and reach parity with DuoAI on the protocols pilot? This note says how DuoAI covers the five
misses, maps its pieces onto gdp-wired's, runs a probe of the mapping on the misses, and recommends a first step.
Nothing is built into the library here. The probe is `probe.ts` beside this note; `duoai_checks.py` counts DuoAI's own
candidate sets. Figures come from `runs/enum/` in this worktree (gitignored) unless they cite another round.

    bun research/protocols/enum/probe.ts <protocol> [--check houdini] [--weaken 1] [--plus] [--held] [--depth 200]
    modal run research/protocols/enum/duoai_checks.py --out runs/enum/duoai
    modal run supercomputer/run.py --jobs research/protocols/enum/jobs-p4.json --out runs/enum/p4    # (p1: toy, p2–p4: the rest)

## The answer in short

- **Enumeration fits gdp-wired's structure.** Its pieces are pieces the join already has:
  - DuoAI's sorts are keySorts';
  - a sub-template is a view;
  - its subsamples are the view's rows;
  - an enumerated clause is a view cube;
  - its check is the kernel's.

  Nothing trusted changes: the kernel proves the final set as it proves a written invariant.
- **The probe proves toy_consensus_forall with nothing written.** No gdp-wired search had proven it before.
  - The search: 10 candidates from 184 to 460 samples, enumerated in under 0.2 s. A Houdini over the kernel's per-law
    goals takes 3 rounds and keeps 8 laws.
  - The proof: `proveRule` with the search off proves the 8 laws and the safety law, certificate checked.
  - Time: 128 s and 131 s on Modal (2 vCPU, two runs). DuoAI takes 3.2 to 3.7 s.
- **It does not reach parity.** distributed_lock, consensus_wo_decide and sharded_key_value_store get candidate sets
  that hold the laws they need, but the kernel doesn't settle their Houdini rounds in 450 to 1,300 s. One goal of
  distributed_lock ran 900 s over 4 keys with 124 laws assumed, wo_decide's one-key goals take 90 to 180 s each, and
  sharded KV's second goal never settles. ring_leader_election's template lacks a function of a key.
- **What binds:**
  1. **The kernel's cost (class D).** A goal that assumes many laws over 3 to 5 keys costs a lot, and Houdini assumes
     every candidate in every goal.
  2. **The samples.** distributed_lock gets 124 candidates where DuoAI gets 60, and wo_decide 91 where DuoAI gets 12.
     Each candidate that only the shallow samples support is stronger than a true law, so when the kernel drops it
     the true law goes too. DuoAI's checks cost about 0.1 to 1 s for 60 laws (EPR in Z3); ours cost 0.2 to 900 s per law.
- **Recommendation:** enumerated view cubes as a fallback stage of the join, over the views' own atoms, gated to keyed
  rules whose join found nothing (section 5). It is small (about 150 lines in core/infer.ts) and general, and its
  measurement is toy proven with nothing written in the pilot. Parity also needs the kernel's multi-key goals to be
  cheap, which this mode doesn't provide.

## 1. How DuoAI gets 10 of 10

### What it does

DuoAI (Yao, Tao, Gu, Nieh, OSDI 2022) is DistAI (OSDI 2021) with a better refinement. Read from its source
(github.com/VeriGu/DuoAI at ecd37c4: `src-py/translate.py`, `src-c/Solver.cpp`, `src-c/InvRefiner.cpp`):
- **Simulation.** `translate.py` compiles the Ivy protocol to Python samplers, one per instance size: every sort from
  1 to 3 elements (`INSTANCE_SIZE_WIDTH = 3`), each run drawing only enabled actions (rejection sampling on the
  `require`s), up to 2,500 rounds. Each reached state is projected onto every assignment of the template's variables
  (DistAI's subsamples) and written as a row of the predicates' values (`traces/<p>/<size>.csv`). Nine sampler
  processes run at once.
- **The template.** Per sort, as many variables as the most places of that sort in one relation (`calc_template_sizes`:
  `vote(N, V)` gives a node and a value; `le(E1, E2)` gives an ordered sort two), at least 2 nodes, 2 values where
  there are keys or quorums, 3 nodes for a ring. Its sub-templates are enumerated in order (`enumerating vars (1,1)`,
  `(2,1)`, `(1,2)`, `(2,2)`).
- **The atoms.** Each relation at the sub-template's variables (repeats allowed, `vote_msg(N1, N1)`), a function's value
  compared by the sort's order (`le(E1, ep(N1))`, `le(ep(N1), ep(N2))`), an individual equal to a variable (`first = N1`,
  `e1 = E1`, `zero = E1`), `idn(N1) = I1` for a function into another sort. Variables of one sort are distinct
  (`N1 ~= N2 ->`) and, for an ordered sort, increasing (`~le(E2, E1) ->`).
- **Enumeration.** The strongest clauses of at most 3 disjuncts (`max-ored-clauses`; 4 or 5 literals in all) true on
  every row, each with the clauses it implies in a minimum implication graph. A second process adds one ∃ variable
  (`max-exists 1`) and refines top-down; a third, ∀ only, refines bottom-up from the safety property.
- **Checking and weakening.** Ivy (Z3 4.7.1, EPR) checks the conjunction. A failed invariant is dropped
  (removal-only, Houdini) or replaced by its successors in the implication graph, the next weaker clauses
  (co-implication), in two processes side by side. When the safety property fails with nothing left to drop, the
  formula size grows (`Retry with a larger formula size`: max-literal 4 to 5) and the template grows after that.

### Per protocol (the five misses, DuoAI's own runs)

`duoai_checks.py` replaced DuoAI's `IVY_CHECK_PATH` with a wrapper that keeps every file DuoAI hands to `ivy_check`, so
the candidate sets below are its own (one run per protocol at 60 s, Modal `cpu=2.0`; the answer's invariants are the
pilot's `runs/duoai/main`, gen/duoai worktree). Each check is made twice, by the two refinement processes.

| Protocol | DuoAI wall | Simulation | Ivy checks (invariants in each file, safety included) | Its answer |
| --- | --- | --- | --- | --- |
| toy_consensus_forall | 3.2 s | 2.0 s | 4, 4 (fails), 13, 13 (with ∃, fails), 7, 7 (OK, max-literal 5) | 7: a vote means voted; one vote per node; the voting quorum voted for a decided value (3 forms) |
| distributed_lock | 7.5 s | 2.8 s | 61, 61, 97, 97, 74, 53, 46, 43 (OK), 84 | 43: 13 over (node, epoch), 9 over (node, 2 epochs), 12 over (2 nodes, epoch), 8 over 2 nodes and 2 epochs |
| consensus_wo_decide | 4.2 s | 2.3 s | 13, 13, 27, 27, 18, 18 (OK) | 18, two of them over 3 nodes (one vote message per voter; one counted vote per voter), generalized from 2-node clauses |
| ring_leader_election | 4.3 s | 4.5 s | 15 (OK, first check) | 15: over (node, id) with `idn(N) = I`, 3-node ones with `ring.btw` and id orders |
| sharded_key_value_store | 2.5 s | 3.2 s | 13 (OK, first check) | 13, the widest over (key, 2 values, 2 nodes) |

So on the misses DuoAI checks sets of 3 to 96 candidates (∃ ones among them) in 1 to 4 rounds of Ivy checks; its samples are good enough that for
ring and sharded KV the first candidate set is already inductive. Its time is the simulation (2 to 4.5 s of 2.5 to
7.5 s here; 63% of the wall time at the median over all ten, `../duoai/README.md`), then about 0.1 to 1 s per Ivy check.
Enumeration itself is a few hundredths of a second (`enumerate_dnf time: 0.00s` to `0.38s`).

### Our join on the same five (from ../README.md and ../COST.md)

| Protocol | Where the join stops | What it lacks |
| --- | --- | --- |
| toy_consensus_forall | round 1, "stuck unknown": the safety step goal with nothing assumed outruns the 8 s query budget. With gaps2.patch's three fixes it finds "one vote per node", whose step goal then runs out of budget too | a carried map's cells in a model's request, a carried map's sort, a 3-key template view (gaps2); then the kernel's cost per goal |
| distributed_lock | "target none" at 300 s with four times the budget | the key as a value (`e ≤ Ep[a]`), laws over 4 keys (2 nodes, 2 epochs) |
| consensus_wo_decide | "found nothing" (36.6 s at 60 s) | 3-node laws (one vote message per voter); its quorum goal unsettled at 600 s (COST.md) |
| ring_leader_election | "found nothing" (8 s) | a function of a key (`idn(x)`), a composed key with such a part (`Pending[idn(x)·N + y]`), the ring's order over 3 keys; runs that elect a leader |
| sharded_key_value_store | ends in 47 s, "found nothing"; its written invariant killed at 600 s | views of 4 and 5 keys over 3 sorts; the kernel on "one transfer per key" (5 keys: an elimination blow-up) |

**What DuoAI's space has that our views can't state.**
1. **Order atoms between a key and a cell of its sort, and between two such cells** (`le(E1, ep(N1))`,
   `le(ep(N1), ep(N2))`): the key as a value. A view's atoms are cells; its keys are never values (distributed lock).
2. **Every sub-template, not the caller's law's shape.** Our views come from the caller's laws, the pair space and
   gaps2's composed-key templates. DuoAI enumerates every sub-template up to (2 nodes, 2 epochs) or (2 nodes, 1 key,
   2 values): four and five keys over two and three sorts (distributed, sharded), and three of one sort by generalizing
   a repeated variable (wo_decide).
3. **Individuals equal to a key** (`first = N1`, `e1 = E1`, `zero = E1`): the init's free individuals as atoms.
4. **Functions of a key and orders between keys** (`idn(N1) = I1`, `~le(I2, I1)`, `ring.btw(N1, N2, N3)`): ring only.
5. **Completeness inside the template.** Every minimal clause of at most 3 disjuncts true on the samples is a candidate.
   The join makes hull forms and cubes one counterexample at a time, so a law is found only if a counterexample asks
   for it and the cube generalizes to it.

The join's own strengths DuoAI's space lacks: linear forms with coefficients (budgets, sums, clocks), levels, remainders,
which every CHC and real-world law needs. Enumeration is a mode beside the join, not a replacement.

## 2. The mapping onto gdp-wired

| DuoAI | gdp-wired, today | What enumeration adds |
| --- | --- | --- |
| sorts (declared) | `keySorts` (core/infer.ts): union-find over the places keys are read at | a map's **value** place (`V:Ep` with the epochs a request compares or writes there), so a map into a sort is a function of a key; an order flag per sort (two of its terms compared by < or ≤); params and scalars of a sort (individuals) |
| small instances | random runs from the start at bounds 1 to 4 (`refuteByRuns`, infer.ts's runs) | runs that redraw a stutter (a request whose flag is false), as DuoAI's samplers draw only enabled actions; inputs drawn from the values the state holds (class E's fix) |
| subsamples (CSV rows) | a view's rows (`View.rowsOf`, `distinctRows`): the cells at each assignment of the keys a state holds, kept once | the rows of every sub-template of the template, as views |
| template | the views: the pair space, one per caller law of several keys, gaps2's composed-key templates | per sort, the most places of that sort one map or the caller's law reads (two for an ordered sort), one more for a sort one map reads twice (`--plus`); every sub-template |
| atoms | a view's cells, the cubes' literals (a few-valued cell at a value, two cells of one map equal) | order atoms of an ordered sort (key ≤ cell, cell ≤ key, cell ≤ cell), individual = key, key = 0 |
| enumeration | `viewCube`: one cube per counterexample row no sample row is | every minimal cube no sample row is (DistAI's enumeration is exactly this), up to 3 literals, one per renaming of a sort's keys, tautologies out |
| Ivy check | the kernel (`proveLaw` per law, `proveLaws` for the set, certificates checked) | nothing |
| removal-only refinement | Houdini in the join (a form nothing strengthens is dropped) and on the runs' neighbors | nothing |
| co-implication refinement | `down` (a blocked cube's literals taken out: stronger) | a dropped cube's one-literal weakenings that the rows allow (weaker) |

**How it shares structure.** An enumerated candidate is a join `Form` with `view` and `cube` set: "never all of these
literals at once at every tuple of the view's keys", printed by the existing cube printer and proven as any form. The
sub-templates are views made by `addView` (vars, places, frame, `rowsOf`); their rows are the views' rows. What is new:
- the enumerator over a view's rows: rows as bitsets per literal, a depth-first search over literals in order, minimal
  and canonical clauses (the probe: about 70 lines);
- order atoms of an ordered sort and individuals in a view's atoms (about 25 lines; keySorts' value places about 10);
- the sub-template views (about 20 lines over addView);
- weakening on a dropped cube (about 20 lines).
About 150 lines, 8 to 10 kB in core/infer.ts, nothing in kernel/.

**What is trusted.** Nothing new. The candidates, their pruning by samples, Houdini and the weakening are search; the
kernel proves the final set as it proves any written invariant (`proveLaws`: per-law goals at a fresh key, assumed at
the instances the prover names, certificates checked, the Lean twin unchanged). The probe's toy proof goes through
`proveRule(r, laws, {search: false})`, the same call run.ts uses for written invariants.

**Where it runs.** Only on rules with maps whose keySorts finds a sort (CHC, TIP and the SV/ITS tasks have no maps, so
it is off there by construction), and only on the caller's laws over several keys or where the join finds nothing.

## 3. Risks

- **Speed, and CHC.** Enumeration is off by construction where a rule has no maps (every CHC, SV, ITS and TIP task):
  keySorts finds no sort, so no view, no template. Its own cost is small. Locally, toy's search takes 0.05 to 0.07 s,
  distributed's 0.1 to 0.4 s and sharded KV's 1.4 s; on Modal the tautology filter takes distributed's to 10 s, and
  that filter could read the clause's terms once instead of brute force. The cost is the check:
  - **Per round:** a Houdini over n candidates asks n goals, each assuming all n. Toy's round 0 takes 58 to 61 s for
    10 candidates; distributed's round 0 did not finish in 1,300 s for 124.
  - **Where toy's time goes:** 77 of its 108 s are three goals that end in a model (52.9, 13.0 and 11.2 s). Its proofs
    take 0.2 to 1.5 s each, and the safety law's last goal 15.3 s.
- **The kernel's "sat" is not always a counterexample.** In toy's round 1 the safety law's goal ends in a model with
  9 candidates assumed; in round 2, with one candidate fewer (a copy of the safety law itself), it is proven. A model
  after `withModels`' rounds can be a tuple short. A Houdini that drops on every model can drop a law the set needs. The
  join judges a model by the interpreter first ("outside", a model's state at the cells it names). Enumeration's drops
  must go through that judgement, not the probe's plain `proveLaw`.
- **Samples too shallow for strong candidates.** distributed_lock's first samples (stutters counted as steps, 54 to 88
  states) gave 337 to 458 candidates. Redrawing a stutter (DuoAI's samplers draw only enabled actions), inputs from the
  values the state holds, and 200 steps a run give 155 states and 96 to 124 candidates (DuoAI's first check: 60). Each
  candidate the samples support but the protocol doesn't is stronger than a true law. "Two transfers to one node are
  one", for one, is stronger than "two live transfers are one". When the kernel drops the strong form, removal-only
  Houdini can't recover the weak one.
  - **Weakening as built is a no-go.** Each dropped candidate's one-literal weakenings that the rows allow (DuoAI's
    co-implication refinement, one step) turned 19 drops into 591 new candidates. The goals then cost 10 to 30 s each.
  - **DuoAI's version weakens less.** It weakens along a minimum implication graph, to the next weaker formulas only, and
    only on its own small, near-inductive sets.
- **Our encoding's init phase needs atoms DuoAI doesn't.** Ivy's `after init` is no step, but here the state before
  `init` is reachable, so laws need "nothing before init" (`started ∨ ¬Held[x]`, `started ∨ Ep[x] = 0`). DuoAI's order
  atoms (a key against a cell, or two cells) leave out `cell = 0`; the probe adds it (p4: 124 candidates against p3's 96).
  In both runs round 0 still ends in a model for "two holders are one" and "a holder's epoch is above every other".
  Whether those models are real counterexamples (a supporting law the set lacks) or a tuple short is not diagnosed.
- **The real-world corpus.**
  - **Gitea #0** ("two counted approvals are never by the same reviewer"; guards i < j < next, `By[i] = By[j]`,
    `Ty[k]` a choice) is in an extended template: equal cells of an unordered value sort, few-valued cells at a value,
    and the row sort ordered by `next`. It is the one open real-world law in reach, and it is not probed here.
  - **TigerBeetle's open laws** are sums over a map, which no clause states.
  - **Casbin's and Keycloak's laws over several keys** are already proven.

  So the expected real-world gain is at most Gitea #0, unmeasured.
- **The search budget.** gaps2's template views, added to every keyed rule's join, cost decentralized_lock its proof
  (../README.md). Enumerated candidates added to the join's first set would risk the same on the five proven
  protocols: the join's whole-set queries already take 2 to 5 s at 1,100 forms (COST.md).
  - **The safe split:** enumeration runs only where the join ends with nothing found, in the budget it leaves. The
    misses end 8 to 48 s into a 60 s budget.
  - **Its candidates join that leftover search:** at most about 32 per view, fewest literals first, smallest
    sub-template first.

## 4. The probe

`probe.ts` runs the mapping with nothing from the library changed. Its pieces:
- **Sorts:** a union-find over the rule's reads, with value places and individuals.
- **Samples:** random runs that redraw stutters, with `--held` inputs.
- **The template:** per sort, the most places one map or the safety law reads (two for an ordered sort; `--plus`, one
  more for a sort one map reads twice), and every sub-template.
- **Atoms:** cells as yes/nos, scalars of yes/nos, individual = key, and for an ordered sort a key ≤ a cell, a cell ≤ a
  key, cell ≤ cell and `= 0`.
- **Enumeration:** minimal clauses of at most 3 literals over the rows' bitsets, canonical per renaming, tautologies out.
- **Checking:** `--cti` runs Houdini on states near the samples by the interpreter. Then Houdini over the kernel's
  `proveLaw` (each candidate's goals with every other assumed), and the survivors and the safety law through
  `proveRule(..., {search: false})`.

Modal, 2 vCPU, 4 GB (`runs/enum/p1` to `p4`); enumeration counts are local runs too.

| Protocol | Sorts (keys in the template) | Samples | Candidates (DuoAI's first ∀ check) | The kernel | Verdict |
| --- | --- | --- | --- | --- | --- |
| toy_consensus_forall | node 1, value 2 | 184 to 460 | 10 (3, then 6 at max-literal 5) | Houdini: round 0 58.5 / 60.7 s drops one, round 1 28.3 / 29.7 s drops the safety law's copy, round 2 19.0 / 18.5 s none; then proveRule 18.2 / 19.5 s | **proven, checked**, 128.3 / 131.3 s (p1, p2) |
| distributed_lock | node 2, epoch 2 (ordered; `Ep` its values; `first`, `e1`) | 155 | 124 (60) | round 0: 98 of 125 goals in 449 s (82 proven, 16 models), then goal 99 (`¬Transfer[e1,n1] ∨ ¬Transfer[e2,n2] ∨ Locked[e1,n1]`, 4 keys) ran over 900 s | killed at 1,400 s (p4) |
| consensus_wo_decide | node 3 (`--plus`) | 1,005 | 91 (12) | the first four goals (one key each) 90.2 to 181.7 s each, with 91 laws over up to 3 keys assumed | killed at 520 s (p3) |
| sharded_key_value_store | node 2, key 1, value 2 | 1,393 | 17 (12, inductive at once) | goal 1 proven 3.5 s; goal 2 (`¬Table[n,k,v] ∨ ¬TransferMsg[n,k,v]`) unsettled at 450 s | killed at 520 s (p3) |
| ring_leader_election | node 2 (ordered, by `size`), id 1 | 14 | 8 (14, inductive at once) | not run: the template lacks what ring needs | – |

**toy's 8 laws**, as enumerated (s0 nodes, s1 values):

    ¬Decided[v] ∨ started                     ¬Voted[n] ∨ started            ¬VotingQuorum[n] ∨ started
    ¬Vote[v, n] ∨ started                     Voted[n] ∨ ¬Vote[v, n]          (a vote means voted)
    Voted[n] ∨ ¬Decided[v] ∨ ¬VotingQuorum[n]
    Vote[v, n] ∨ ¬Decided[v] ∨ ¬VotingQuorum[n]                               (the voting quorum voted for v)
    v1 ≠ v2: ¬Vote[v1, n] ∨ ¬Vote[v2, n]                                       (one vote per node)

Houdini dropped `v1 ≠ v2: ¬Vote[v1, n] ∨ ¬Decided[v2] ∨ ¬VotingQuorum[n]` (true in Ivy, DuoAI's [202]), whose step goal
in our model has a real model: the quorum is over-approximated (it meets the stored one only at the witness `w`). These
are the written invariant's laws (models.ts) plus "nothing before init" for each map. They come with nothing written,
from a template read off the rule, with no protocol switch.

**Why the other four aren't proven:**
- **distributed_lock: the check, then the samples.** The candidates hold the written laws' forms:
  - `¬Locked[e, n] ∨ e ≤ Ep[n]`;
  - two holders are one;
  - a holder's epoch is above every other;
  - nothing before init;
  - the 4-key transfer exclusions.

  Round 0's goals end in models for 16 of them, "two holders are one" and "a holder's epoch is above every other"
  among them. Some candidates only the samples support (`¬Held[n1] ∨ ¬Transfer[e, n2]`) stand in for weaker true laws. The kernel
  never finished round 0: one 4-key goal ran over 900 s with 124 laws assumed. Before `= 0` was an atom, round 0
  finished in 305 s with 19 drops (p3). In round 1 it reached 61 of 78 goals by the cap. Weakening on drops (`--weaken
  1`) took 19 drops to 591 new candidates and 10 to 30 s a goal.
- **consensus_wo_decide: the check.** Its template needs 3 nodes for "one vote message per voter" (DuoAI generalizes
  `vote_msg(N1, N1) ∧ vote_msg(N1, N2)` to N1, N2, N3). With 91 candidates over up to 3 nodes assumed, even a one-key
  goal costs 90 to 180 s (COST.md: its quorum goal is unsettled at 600 s even alone).
- **sharded_key_value_store: the check.** 17 candidates; the second goal (3 keys, with 5-key laws assumed) doesn't settle
  in 450 s. That is COST.md's elimination blow-up on composed keys of three parts.
- **ring_leader_election: the template.** Ring needs `idn(x)` as an atom, `Pending[idn(x)·N + y]` as a place, and
  orders between ids (`~le(I2, I1)` with `idn(N) = I`). Its runs also never elect a leader (14 states).

**DuoAI's counts, side by side** (`runs/enum/duoai`): toy 3 candidates, then 6 (2 rounds of checks); distributed 60,
weakened to 42 in 4 rounds; wo_decide 12, then 17; ring 14 and sharded KV 12, each inductive at its first check.

## 5. Recommendation

**The step: enumerated view cubes, a fallback stage of the join** (core/infer.ts, untrusted, about 150 lines, 8 to 10 kB).
- **The template's views.** keySorts gives each sort its width: the most places of that sort one map or the caller's
  law reads. Every sub-template is a view built by `addView`, with distinct keys and the domain frame. This one rule
  replaces gaps2's composed-key templates and covers the caller-law views as special cases.
- **The enumeration.** For each view, every minimal cube of at most 3 literals that no sample row is in, canonical per
  renaming of a sort's keys. The literals are the view's own: each few-valued cell at a value, a scalar of yes/nos, two
  equal cells of one map. They become `cube` forms, printed and proven as the view cubes are.
- **Where it runs.** Only on rules whose keySorts finds a sort and that have a caller law over several keys, and only
  when the join has ended with nothing found, in the budget left.
- **How the forms are checked.** They go into the join's Houdini on the cone, not the probe's plain Houdini: the
  relative induction, the CDCL model first at a quarter of the budget, models judged by the interpreter, and a form
  nothing strengthens dropped.
- **Runs that redraw a stutter** (a request whose flag changes nothing), for the samples the enumeration reads: about
  3 lines in the runs.
- **Not in it yet:** order atoms (the key as a value), individuals, and weakening. Each is measured to need the check's
  cost fixed first (distributed_lock above).

**Why this first.** It is the part of DuoAI that the probe shows closes a miss. It reuses the join's views, rows,
cube forms, printer and Houdini. It is off on CHC by construction and off on every protocol the join already proves.

**The measurement that confirms it:**
- **The pilot** (`research/protocols/run.ts --skip given,broken`), Modal, three runs at 60 s and three at 120 s:
  - toy_consensus_forall proven with nothing written in 3 of 3 at 120 s, its time at 60 s reported;
  - lock_server_sync, lock_server_async, decentralized_lock, two_phase_commit and ticket_lock proven in every run, as at
    1ce51c3;
  - every broken variant refused as before.
- **A quick bar** against 1ce51c3:
  - CHC dev unchanged (the stage can't run there; any change is timing);
  - real-world dev with nothing lost and the per-law time level;
  - Gitea #0 and TigerBeetle #0 to #7, three runs a side, verdicts and times level.
- **If toy isn't proven at 120 s** inside the join, where the probe's plain Houdini needs 128 s: the join's relative
  induction doesn't make the enumerated set cheaper, and the stage is a no-go until the multi-key goals are cheap.

**What parity needs beyond it, in order:**
1. **The kernel's goals with many laws over 3 to 5 keys.** Every remaining miss is blocked there:
   - distributed's 4-key goal at over 900 s;
   - wo_decide's one-key goals at 90 to 180 s with 91 laws assumed;
   - sharded KV's elimination.

   The options, all search: assume each candidate only at the tuples of its own sort (COST.md's class D), or check
   stratified by sub-template. Neither is in hand.
2. **Order atoms and individuals** for ordered sorts (distributed_lock), with `cell = 0` for our encoding's init.
3. **Samples as deep as DuoAI's**, so that candidates are few and near-inductive (distributed 124 against 60, wo_decide
   91 against 12).
4. **A function of a key as an atom** (ring), which nothing else in the corpora needs (gaps2).

**Plainly:** enumeration fits gdp-wired's structure and is the first route to prove toy_consensus_forall with nothing
written. It is not a route to parity on its own. DuoAI is fast because its checks are EPR queries of a second or less;
ours are the kernel's goals, and on these protocols they are what costs.

## Spend

Billed (`modal billing report --for today --resolution h --json`, this round's apps): $0.78 by 10:00 UTC, with that
hour still open (p4, 1,400 s on 2 vCPU, about $0.10 more): about $0.9 in all, against a $6 budget.
- **DuoAI's checks:** $0.008.
- **Wasted, about $0.35:** p2's first batch of four jobs, each killed at its 1,770 s cap with its output lost (stderr
  was not kept at the cap). Its rerun (p3) killed bun inside the container at 520 s with stderr kept.

Nothing is left running (`modal app list`: no app of this round live).
