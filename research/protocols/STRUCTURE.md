# Quantified invariants: what structure, and the first step

The question: what structure would let gdp-wired infer the quantified invariants of distributed protocols (the pilot
in README.md: 0 of 10 with nothing written, miss classes A to E), and carry over to its other domains? This note reads
how the leading tools do it, checks each candidate against gdp-wired's own machinery, and recommends one first step.
The probe at the end runs that step by hand on two protocols and one real-world law.

## The answer in short

- **The trust is already there.** gdp-wired's kernel proves a law about every key at a fresh key (`k#`) and assumes the
  laws about keys at the tuples the prover names (kernel.ts `obligations`, `assumed`, `closing`; Sets.lean's quantified
  flags). That is the unbounded check IC3PO, DistAI and DuoAI hand to Ivy or Z3, and here it is checked again in Lean.
  No candidate needs a new trusted theorem to be sound.
- **The gaps are in the search and in which instances it chooses.** The leaders differ from us in three places:
  1. they search over a template of a few variables per sort, on small-instance states projected onto those variables
     (DistAI's subsamples);
  2. they read a solver's model over its whole finite domain: Ivy's EPR check, UPDR's diagrams, IC3PO's finite
     instances;
  3. they name sorts.
- **The structure that organizes all three is the key's sort**, read off the rule by matching the keys its laws read
  against the keys its goals read:
  - the model's keys per sort (model-based instances);
  - the join's spaces as views over a few keys per sort;
  - the prover's tuples;
  - later, sums per row.
- **The first step: model-based instances.**
  - **Where:** kernel/prove.ts, untrusted, about 80 lines.
  - **What:** a model of a goal that breaks an assumed law (or a quantified flag) at a tuple of the goal's own keys is no
    counterexample. Those tuples are added and the goal is asked again, each key ranging only over the terms its own
    reads match.
  - **Why first:** it closes the "outside" stop the pilot found under the pair cubes (class B) and is the lazy form of
    class C's instance fix. The next structures (views, cubes, sums) all make laws about several keys, and their models
    would hit the same wall without it.
  - **What the probe shows:** it is necessary and not sufficient. It removes the stop on ticket lock's caller law and
    finds the missing tuples on decentralized lock, but the kernel then takes over 60 s on the larger goal (class D). The
    measured results on the pilot and the quick bars are in "Results" below.

## 1. What gdp-wired already has

| Piece | Where | What it gives a quantified invariant |
| --- | --- | --- |
| Laws about every key (and every tuple) | kernel.ts `Law.forall/keys`, `obligations` (`k#`), `assumed` | the unbounded ∀ check: proven at a fresh key, assumed at chosen tuples (∀-elimination); sound for any choice |
| Quantified flags | kernel.ts `closing`; Sets.lean `closingHyps`, `closing_true` | a request's ∀ guard: ?f = 1 means the body holds at the instances; ?f = 0 means it fails at a witness `w?f` |
| Instance choice | prove.ts `instancesFor`, `withReads`, `matched`, `triggered`, `withFacts` | untrusted E-matching: tuples where a law's reads match the goal's reads (Link[x·N + y] against Link[a·N + b]) |
| The join | infer.ts (samples, hull, levels, cubes, Houdini) | IC3-style inference over three spaces: the state, the cells at one key, the cells at two keys (`pairingOf`) |
| Runs | infer.ts runs (bound 2, doubling every 20 trials) | small instances first: keys 0..2 at the start, as DistAI's small sizes |
| Sums over a map | Sums.lean, kernel.ts `sumMachine` | `Σ_k M[k]` exact, a cell at most the sum, `dsum_le` for any list of distinct keys |
| Refinement | compose.ts `refinement`, Refine.lean | a run of one machine matched by a run of another, related by laws |

The join's spaces are DistAI's subsamples:
- the cells at one key are a view over one variable;
- the pair space is a view over two;
- the forms found in a space are laws at every key, or at every two keys.

So the join already lifts a sample's quantifier-free facts to ∀-forms by symmetry ("candidate 2"). It lifts them over at
most two plain keys, or two keys of one composition.

## 2. How the leading tools get quantified invariants

| Tool | Core idea | Trusted / checked | What it needs of the logic |
| --- | --- | --- | --- |
| IC3PO | IC3 on a finite instance; each learned clause is replaced by its orbit under permutations of each sort, and the orbit is written as a quantified formula: ∀ for a sort whose constants all play one role, ∀∃ when one cell of the partition grows with the sort; the instance grows until the invariant stops changing | the finite-instance IC3 and the orbit's quantifiers are untrusted; the unbounded invariant is checked by Z3 (and printed for Ivy). The paper's cutoff checks are "sufficient, we believe", "but we still do not have a formal convergence proof" | sorts of indistinguishable constants (fully symmetric); no order or arithmetic on a sort (future work); the final check may leave EPR |
| DistAI | simulate at several instance sizes; project each state onto ≤ k variables per sort (subsamples); enumerate the strongest ∀ clauses true on every subsample; Ivy checks the conjunction and failing clauses are weakened (monotonic refinement) | samples and enumeration untrusted; Ivy (Z3, EPR) checks | ∀ only; the template (variables per sort, literals); EPR for the check to be decidable |
| DuoAI | DistAI's sampling, and a minimum implication graph over the template's formulas: each formula with the strongest formulas it implies, so strengthening and weakening walk the graph. Two searches run side by side: top-down with ∃, bottom-up without | as DistAI; Ivy checks | ∀ and ∃ (one alternation); sorts; template bounds (max_and, max_or) |
| FOL-IC3 / P-FOL-IC3 | IC3 whose lemmas are quantified separators: the smallest formula of a prefix that separates the states to block from those known reachable. P-FOL-IC3 searches breadth-first in parallel, with bodies in k-term pDNF | separation untrusted; every lemma's induction checked by an SMT solver | first-order with sorts; ∀∃ prefixes; checks in EPR where the prefix is stratified |
| UPDR (PDR∀) / Phase-PDR∀ | PDR whose obligations are diagrams: a model's finite structure as an existential conjunction of its facts, blocked as a universal clause. It finds a universal invariant or proves none exists in the abstraction. Phase-PDR∀ takes a user's phase automaton and solves for one invariant per phase as linear CHCs | diagrams and generalization untrusted; EPR solver checks | EPR, so that a model is finite and its diagram finite; universal invariants |
| SWISS | exhaustive search over small formulas (bounded size), pruned by counterexample models; Breadth builds many small invariants, Finisher one large; symmetry and parallelism cut the space | search untrusted; each candidate's induction checked by Z3 | a finite candidate space (the small-world hypothesis); EPR or extended EPR for the checks |
| Ivy | the verifier: protocols in a restricted language so that every verification condition is in EPR (∀*∃* with stratified functions), which is decidable with the finite model property. A failed check shows a finite counterexample to induction, which the user generalizes | Z3 decides EPR; the user's generalization is checked | EPR: no function cycles between sorts (stratification); arithmetic and total orders axiomatized |
| Bounded quantifier instantiation (Feldman et al.) | check ∀*∃* invariants outside EPR by instantiating only with terms up to a depth bound; bound 1 captures natural instrumentations | sound for proving (instances are ∀-elimination); complete only up to the bound | any first-order theory; sorts to bound the terms |
| Invisible invariants (Pnueli, Ruah, Zuck) | compute the reachable set of a small instance (BDDs), project it onto one or two process indices, generalize to ∀i or ∀i≠j, check the verification conditions on a small instance by a small-model theorem | the small-model theorem is the trust: the checks at size N₀ decide every size, for the fragment it covers | bounded data, indices compared by = (later < too), assertions ∀ (or ∀∃ by heuristics) |
| Cutoffs (Emerson–Kahlon) | for guarded systems of identical processes (disjunctive or conjunctive guards), a property holds for every number of processes iff it holds up to a cutoff | a meta-theorem per class of systems | identical finite-state processes, the guards' syntax |
| Symmetry reduction (Ip–Dill, Emerson–Sistla) | a scalarset sort (unordered, used only by =, as an index, in for-all loops) makes states equal up to permutation behave alike; model check the quotient | the reduction's theorem: the quotient bisimulates the full system | scalarsets: no order, no arithmetic, no constants of the sort |
| Counter abstraction (Pnueli, Xu, Zuck) | count how many processes are in each local state, capped at (0, 1, ∞); prove on the finite abstraction, liveness with the fairness it derives | the abstraction's soundness | identical processes, finite local states |
| Kondo / Basilisk | split invariants into regular ones (message provenance, ownership: generated from the protocol's syntax) and protocol ones (Kondo: written by hand); Basilisk derives provenance invariants by static analysis ("atomic sharding") | generation untrusted; Dafny checks every invariant | none beyond Dafny's; the protocol's host/message structure |
| WLOG in provers (Harrison; Isabelle's `wlog`) | a symmetric statement proved for a canonical case, the symmetry proved once | the symmetry lemma, checked | a group action and invariance proofs, per problem |

**What they share.** Three things recur across them:
- **They infer from finite data.** That is a small instance (IC3PO, invisible invariants), samples from small instances
  projected onto a few variables per sort (DistAI, DuoAI), or models (UPDR, SWISS, FOL-IC3).
- **Symmetry is used only to pool or name what was learned.** IC3PO's orbit, DistAI's subsamples and Ip–Dill's quotient
  all do this.
- **The unbounded result is checked by a solver, and the inference itself is never trusted.** Only the model-checking
  lineage trusts a meta-theorem (small models, cutoffs, symmetric quotients). IC3PO, the closest to our setting, states
  that it has no proof of its cutoff and re-checks the invariant unbounded.

**What the logic must give.** Three things matter:
- **Sorts.** They bound the template, the instances and the projections.
- **A finite model for each failed check.** EPR gives it. Bounded instantiation gives one relative to the instances.
- **Alternation (∀∃), where a protocol needs it.** It is needed for Paxos and for the quorums of the consensus family.
  The pilot leaves those out.

## 3. Three structures this suggests for gdp-wired

### S1. The key's sort, by matching

A sort, here, is the set of places a bound name is read at: a plain map key (`HasLock[x]`), one slot of a composed key
(`Link[x·N + s]`'s x, or its s), a function's argument. Two bound names have one sort when their places match.
Matching a law's read patterns against a goal's ground key terms binds each bound name to the ground terms of its
sort. prove.ts's `matchMany` and `matched` already do this matching, for instances. Read the same way, it is a sort
system:
- it needs no declaration;
- it survives the encoding (a front end's a·N + b);
- it is the many-sorted EPR universe of a goal: the ground terms of each sort.

What it organizes:
- **(a) A model read per sort** (S3).
- **(b) The join's views** (S2).
- **(c) The prover's tuples:** class D's "a tuple only of keys of the law's own sorts".
- **(d) The runs' draws:** keys of a sort from the values that sort holds, for class E.

### S2. Views: one space per template

A view is a multiset of sorts (DistAI's template: at most 2 per sort, 3 keys in all). Its rows are the cells read at
the keys a law of that view would read, for each assignment of the view's keys to keys a sample holds. Every existing
space is a view:
- the state is {};
- the cells are {s: 1};
- the plain pairs are {s: 2};
- Casbin's composed pairs are {row: 1, column: 1} with the cell at N·x + y.

Class A's three-key invariants are views the join lacks:
- {node: 2, lock: 1} for both lock servers: Grant[a·N + l], Hold[b·N + l], Server[l];
- {node: 1, value: 2} for "one vote per node";
- {node: 2} with a composed message key for decentralized lock.

The forms found in a view are laws at every tuple of the view, so the kernel checks them as it checks the pair forms.
- **Size:** a generalization of the pair space's fixed places 0, 1, 2 (infer.ts's `pairing`, `placeKey`, the rows at
  `[kx, ky, n·kx + ky]`) to the places a view's reads name. Perhaps 150 lines changed, replacing the special case.
- **Risk:** rows grow as (keys held)^3. DistAI's answer is to sample small instances, and our runs already start at
  bound 2.

### S3. The model on the goal's keys (model-based instances)

**The trouble.** A goal's laws about keys are assumed at some tuples. Its model, read as a state, may break a law at a
tuple the prover never chose. The join calls that model "outside" and stops on the caller's law. The pilot's cubes over
two keys stopped exactly there on ticket lock.

**The fix: model-based quantifier instantiation**, as SMT solvers' MBQI and Ivy's EPR checks read a model:
- evaluate each law (and each quantified flag the model sets) at every tuple of the goal's keys, each key over its own
  sort's terms (S1);
- add the tuples where it fails;
- ask again, a few rounds.

**When it terminates, and what it then means.** For an EPR-like rule the model then satisfies every assumed law on
every tuple of the goal's keys. EPR-like here means:
- keys compared only by = and used only as plain or composed indices;
- functions stratified.

Such a model is a real one: the finite model property, read constructively. Outside the fragment (order on keys, a
ring's n + 1) it is a better model, not a proof of one.

- **Trusted:** nothing; it chooses instances only.
- **Size:** about 80 lines (prove.ts `modelInstances`; hooks in `proveThinned`, `proveLaw` and the join's `stepWith`).

### S4 (trusted, later). Counting by rows

**The idea.** A mutual exclusion over two keys says that at most one of a row's cells holds:
- "one holder per lock" is Σ_n Hold(n, l) ≤ 1;
- "one token among grant, hold, unlock and the server" is Σ_n (Grant + Hold + Unlock)(n, l) + Server(l) = 1.

Read as a sum, that is a linear fact at one key (the row l), which is the join's strength (a hull), in place of a
disjunctive fact at three keys. TigerBeetle's per-account sums (#0, #1) are the same object: a sum over the transfers
whose debit account is a.

**Trusted change, Lean first** (Sums.lean). Two facts are needed:
1. **A sum per row.** For a map M, a term g over the cells at a key, and a key function ρ (the row: k ↦ k mod N for
   a·N + b, or a map cell `Debit[k]`), `IsSum (fun k => if ρ k = r then g k else 0) (S r)`. The ghost map S gets one
   cell per row. Its step facts are Sums.lean's `isSum_change` restricted to the row the step writes, and its start is
   `isSum_zero`.
2. **Two distinct cells are at most the sum.** This is `dsum_le` at a list of two distinct keys: the fact a safety goal
   at two skolems needs (Hold[a] + Hold[b] ≤ S for a ≠ b). The kernel's sum flag today covers one key plus the step's
   cover keys.

**How long.** Sums.lean is 50 kB and has every lemma but the row restriction. This is weeks, not days, with its
conformance tests.

## 4. The candidates

### Candidate 1: a checked symmetry theorem

**The statement (Lean-first).** For a machine `s : SMachine` whose keys of a sort σ are read only by equality and as
indices (σ a scalarset), and a permutation π of σ's keys, extended to states and requests slot by slot (on a·N + b, π
acts on a for a row sort and on b for a column sort):

```lean
-- the action on states and requests: each map read through π⁻¹ at its σ slots, each σ-valued input mapped by π
def SMachine.Equivariant (s : SMachine) (σ : Sort) : Prop :=
  ∀ (π : Equiv.Perm Nat) (st : State) (r : Request), s.step (act σ π st) (actR σ π r) = act σ π (s.step st r)
    ∧ s.allowed (act σ π st) (actR σ π r) = s.allowed st r ∧ act σ π s.init = s.init
theorem reach_act {s σ} (h : s.Equivariant σ) (π) : Reach s st → Reach s (act σ π st)
theorem law_of_canonical {s σ} (h : s.Equivariant σ) (φ : State → List Nat → Prop)
    (hφ : ∀ π st ks, φ (act σ π st) (ks.map π) ↔ φ st ks)
    (hc : ∀ st, Reach s st → φ st (canon n)) : ∀ st ks, ks.Nodup → ks.length = n → Reach s st → φ st ks
```

`canon n` is [0, ..., n − 1]. The axioms are the standard three.

**What the kernel checks.** It checks `Equivariant` syntactically: no σ key in `<`, `+`, `·` or a constant, apart from
the frame (k < N, which restricts π to permutations of 0..N − 1). The check is the scalarset discipline, and it fails
on:
- ticket lock's tickets (ordered; the threads are symmetric);
- distributed lock's epochs;
- ring election's n + 1 mod size (rotations only);
- every real-world id compared with `next` (Gitea's `k < next`, the fresh-id high-water laws).

**What it unlocks, and what it doesn't.**
- **Per-key laws from one representative:** nothing new. The kernel already proves a law at `k#`, a key about which
  nothing is known, which is stronger than a canonical key.
- **The one-server cuts are not symmetry.** The projection of lock_server_sync onto one server is a simulation (each
  action touches one server, and the others' actions are stutters of the projection). The existing `refinement`
  (Refine.lean), with the server as a ghost parameter, is the checked route, untested here.
- **Better still, the cuts need no theorem.** Search the cut, lift what it finds (k ↦ k·N + l, every l), and prove the
  lifted laws on the full rule. The kernel already proves the lifted forms there: lock_server_sync's written invariant
  in 2.9 s and lock_server_async's in 26.8 s with the pilot's matching.
- **What the theorem would buy:** a finite instance checked exhaustively standing as a proof, which is candidate 3's
  cutoff.

**Verdict:** not now. It is sound and provable, but it makes nothing provable that the kernel cannot already prove.
Proving equivariance for each rule (Harrison's "weak spot") is where the cost lies.

### Candidate 2: small-instance inference plus generalization

- **Trusted:** nothing.
- **The untrusted search:**
  - runs at small key bounds (already there);
  - rows per view (S2);
  - the join's hull, levels and cubes per view;
  - forms lifted to every tuple of the view;
  - the kernel checks the conjunction (as now);
  - the lift is the space's quantifier, which is IC3PO's orbit for a fully symmetric sort.
- **What it should close:**
  - class A (8 protocols), at the views {node: 2, lock: 1} and {node: 1, value: 2}, and decentralized lock's composed
    message key;
  - class B, with the cubes per view, where the literals include equality and order between a view's values (Ticket[x]
    = Ticket[y]: DuoAI's literals);
  - Gitea's two-row invariants per reviewer, a view {review: 2} with By[x] = By[y];
  - Casbin, Keycloak, and TigerBeetle's per-transfer laws (one sort, already in the cells space).
- **Size:** S2's ~150 lines, replacing `pairing`'s fixed places.
- **Risks:**
  - **Class D:** the kernel's cost with laws over 3 to 5 keys. The probe below shows the kernel is the binding
    constraint once the right tuples are in.
  - **Rows grow as keys^3.**
  - **"Outside" models**, which S3 fixes. It must therefore come first.

### Candidate 3: cutoff or finite-model reasoning

**When an unbounded law is decided by a bounded instance.**
- **The fragment.** A rule whose keys are used only by = and as indices (S1's places), whose cell values are finite kinds
  or keys of another sort, and whose functions are stratified (no sort cycle).
- **Why the instance decides it.** The induction goal for a set of ∀-laws is then an EPR formula. Its negation has a
  model iff it has one over the goal's ground key terms per sort (the Bernays–Schönfinkel–Ramsey finite model property,
  many-sorted).
- **The cutoff.** It is the number of ground terms of each sort in the goal: for one step, the skolems, the request's
  keys and the flags' witnesses. A complete instantiation is every well-sorted tuple of those.

**As a checked theorem.**
- **What it would be:** completeness, not soundness ("if no tree exists, the model is real"). The kernel needs only
  soundness, so the theorem buys nothing a proof needs.
- **What it could license:**
  - reporting "not inductive" with certainty (a real counterexample to induction);
  - an exhaustive check of a finite instance standing as a proof, which with candidate 1 is a cutoff theorem.
- **Its cost:** both are larger than Sets.lean's quantified flags.
- **Where it holds:** none of ticket lock, ring election, distributed lock, two-phase commit (`k < size`) or any
  real-world rule with `next`.

**Operationally, without the theorem:** S3 is that theorem's algorithm. On the fragment it finds the instances a
complete instantiation would need, lazily. Elsewhere it is a heuristic, and the kernel's check stays the proof.

**Verdict:** take the algorithm (S3), not the theorem.

### Candidate 4: other structures the literature shows

**Counting (S4).**
- **Trusted, Lean-first:** a sum per row, and two distinct cells at most the sum.
- **The search:** the existing `withMapSums` route, which adds a map's sum when nothing is found, extended to rows of a
  composed key.
- **What it should close:**
  - lock_server_sync and lock_server_async;
  - decentralized lock: Σ HasLock + Σ Message ≤ 1 needs only whole-map sums plus the two-distinct-cells fact;
  - TigerBeetle #0, #1;
  - the per-account sums.
- **Risk:** weeks of Lean, and the facts at two distinct keys widen every goal of a rule with sums.

**Slicing (an independent index).**
- **What it is:** where every request names one element of a sort and touches only its slice, search the slice, lift,
  check the whole.
- **What it closes:** lock_server_sync, lock_server_async, and sharded KV per key (still a 2-sort slice).
- **Real-world:** no composed-key rule (Casbin and Gitea relate two keys of a sort).
- **Verdict:** a special case of S2's view {node: 2, lock: 1}. By the track's rule, take the view, not the slice.

**∃ and quorums.**
- **What they need:** DuoAI's top-down search, P-FOL-IC3's pDNF, and a quorum sort with Ivy's intersection axiom.
- **Verdict:** out of scope until a front end exists: Paxos, and the consensus family's quorums.

**Phases (Phase-PDR∀).** The join's control states and levels already are phases, read off the rule.

**Provenance (Basilisk).** "A message in flight was sent by its holder" is a view {node: 2} form. Nothing separate.

## 5. What closes what

| | A | B | C | D | E | Real-world |
| --- | --- | --- | --- | --- | --- | --- |
| C1 symmetry theorem | – | – | – | – | – | – |
| S3 model-based instances | – | the "outside" stop | lazily, the tuples a model names | – (adds tuples) | – | Casbin #52's "the step goal doesn't instantiate it at (a, b)" kind; Gitea |
| S2 views (C2) | 8 protocols, given S3 | with cubes per view | – | rows cost | – | Gitea #0's two-row forms |
| S1 sorted tuples in prove.ts | – | – | fewer, right tuples | the instance count | – | TigerBeetle #4, #6 (cost), Gitea's 55.8–68.2 s |
| S1 draws per sort | – | – | – | – | consensus_wo_decide, ring (inputs from values held) | the 13 deep-run refutations |
| C3 finite-model theorem | – | – | – | – | – | – |
| S4 row sums | sync, async, decentralized | mutual exclusion as a sum | – | 1-key facts for 3-key ones | – | TigerBeetle #0, #1; Medusa #4's live total |

CHC with arrays: none of this applies until arrays are maps. Then S3 and S2 apply as they do to maps; array CHC
invariants are ∀-forms over one index (the cells space). TIP-style datatypes: no keys; none applies. Their quantified
lemmas are core/data.ts's, over constructors.

## 6. Recommendation: model-based instances, per sort

- **The step:** S3, with S1's matching to give each key its sort.
- **Small:** about 80 lines in kernel/prove.ts, and three hooks (`proveThinned`, `proveLaw`, infer.ts's `stepWith`).
  Nothing trusted. `GDP_MODEL_INST=0` turns it off.
- **Measurable:**
  - the pilot's "outside" stops;
  - the given invariants (classes C and D);
  - the search with and without the pair cubes (`GDP_PAIR_DISTINCT`), since S3 is what the cubes lacked;
  - the quick bars (CHC and real-world): no CHC task has maps, so CHC must not move.
- **General:**
  - every law about keys, in every domain with maps: protocols, Casbin, Gitea, Keycloak, TigerBeetle;
  - quantified flags too;
  - CHC with arrays once they are maps.
- **Then:**
  1. S2's views on top of it (class A);
  2. S1's sorted tuples in the prover's eager instances, if class D's cost is from ill-sorted tuples;
  3. S4 when a Lean slot is free.

## 7. The probe (local, M-series Mac, about 30 s each, `GDP_MODEL_INST` on and off)

The step was hand-applied in this worktree first:
- `modelInstances` evaluates each law at every tuple of the goal's keys by value;
- after the first measurement, each key ranges over its own sort's terms only.

`bun <scratchpad>/p1.ts <id> <ms> [given]` is run.ts's search or its given check alone.

| Run | Off | On | What happened |
| --- | --- | --- | --- |
| ticket_lock, search, 10 s | unknown, 3.3 s | unknown, 8.4 s | The join's stop on the caller's law ("outside" at round 9, off) is gone. With S3 the caller's law is proven relative to the set at rounds 8, 11, 14 and 20. The set is then 712 forms, and each query over all of them takes about 2 s, so the budget ends the join. |
| ticket_lock, search, 30 s | | unknown, 28.9 s | 41 join rounds, no "outside" on the caller's law; 3 forms set aside as outside (their own goals); the join ends at time. |
| decentralized_lock, written invariant | unknown (sat), 4.0 s | killed at 60 s (and at 100 s, unsorted) | Unsorted: 25 key values, so the 4-key law "one message in flight" needs 25^4 tuples, and the evaluation cap (20,000) is hit. Sorted: 4, then 1, then 1 tuple added. The kernel then does not finish the step goal of "one message in flight" in 60 s: class D, as the pilot's eager no-go (4 s to over 300 s). |
| lock_server_sync, ticket_lock, two_phase_commit, written invariants | proven 1.2, 0.3, 5.9 s | proven 1.3, 0.3, 6.0 s | unchanged |
| Casbin roleManager #3 (real-world, two keys), 60 s | proven, 21.7 s | proven, 17.8 s | unchanged verdict; the same found laws |

**What the probe says:**
- S3 does what it is for: it removes the documented "outside" stop on ticket lock, and it finds the tuples decentralized
  lock's written invariant lacked. It doesn't by itself prove a new protocol.
- In both, the next binding constraint is cost (classes D and B's join set), not a missing instance:
  - the join's set of 700 forms per query;
  - the kernel on 4-key laws.
- That points to the order after S3:
  - S1's sorts to cut tuples, and a smaller join set per view (S2's views keep each space's forms apart);
  - or S4, which replaces 4-key exclusion laws by sums at one key.


## Results

The step as committed (0d815ec, `modelInstances` with each key over its own sort's terms), on Modal, 2 vCPU, the
search at 10 s as in README.md, each configuration its own job (`runs/protocols/r3` in the main checkout, 56 jobs):
- **off:** `GDP_MODEL_INST=0 GDP_PAIR_DISTINCT=0 GDP_JOIN_DROP=0` (README's mid);
- **on:** `GDP_MODEL_INST=1 GDP_PAIR_DISTINCT=0 GDP_JOIN_DROP=0`;
- **on + cubes:** `GDP_MODEL_INST=1` (the pair cubes on).

These runs are of ade69cd, which still had the cubes and their flags. gen/protocols-merge removes both, so its default
is "on".

Search capped at 300 s, the written invariant at 420 s ("killed").

| Protocol | Search off / on / on + cubes | Written invariant off / on | Broken variant |
| --- | --- | --- | --- |
| lock_server_sync | unknown 69.6 / 82.5 / 73.1 s | proven 3.3 / 3.4 s | refuted, 5 steps |
| lock_server_async | unknown 70.5 / 91.7 / 79.6 s | proven 19.1 / 22.5 s | refuted, 21 steps |
| decentralized_lock | unknown 12.3 / 10.1 / 11.2 s | unknown 11.8 s / **killed at 420 s** | refuted, 19 steps |
| distributed_lock | unknown 191.5 / 164.1 / 171.4 s | killed / killed | refuted, 23 steps |
| two_phase_commit | unknown 9.8 / 9.1 / 8.8 s | proven 13.9 / 12.8 s | refuted, 5 steps |
| ticket_lock | unknown 6.1 / 10.8 / 12.8 s | proven 1.3 / 1.0 s | refuted, 20 steps |
| toy_consensus_forall | unknown 43.6 / 25.5 / 36.7 s | killed / killed | refuted, 18 steps |
| consensus_wo_decide | unknown 84.1 / 62.7 / 52.3 s | killed / killed | unknown (as before; the hand run breaks it) |
| ring_leader_election | unknown 13.3 / 17.8 / 13.8 s | unknown 14.0 s / **proven 38.9 s** | unknown (as before; the hand run breaks it) |
| sharded_key_value_store | killed at 300 s (all three) | killed / killed | (not reached) |
| lock_server_sync@one | proven 1.8 / 2.1 / 1.6 s | | refuted, 3 steps |
| lock_server_async@one | proven 5.8 / 5.4 / 4.9 s | | refuted, 21 steps |

**What moved:**
- **Ring leader election's written invariant: unknown to proven.** Locally it is proven in 17.4 s on and unknown in
  8.7 s off; checked, as every proof is.
  - Its third law, an id pending past a node is above that node's, is about three keys.
  - The step goal needed it at a tuple the prover's matching didn't name, and the model named it.
  - The rule is not EPR-like (n + 1 mod size, an injective `idn`), so this is S3 as a heuristic, not as the finite
    model property.
- **No protocol moves with nothing written.** That holds with or without the cubes, so the cubes still don't pay and
  stay out of a merge.
- **Every broken variant is refused as before.**
- **One loss in time: decentralized lock's written invariant.** It went from unknown in 11.8 s to killed at 420 s. The
  model's tuples (4, then 1, then 1 locally) make the step goal of "one message in flight", a law over 4 keys, one the
  kernel doesn't finish. The given check runs with the search off, so nothing budgets it. This is class D's cost, as in
  the probe.

**The quick bars** against 3cdf37e (`runs/bar/runs/0d815ec65635-vs-3cdf37eddf65-quick-2026-10-281106`), wrong 0 in
both:
- **CHC-COMP dev (662):** 517 against 517, 518, 517.
  - 3 gained and 1 lost, none in every run, all four at the time limit.
  - No CHC task has maps, so these are timing flips.
- **Real-world dev (91):** 74 against 74, 74, 73.
  - Nothing differs in the first pass.
  - Gitea's, Casbin's, Keycloak's and TigerBeetle's laws over several keys are unchanged.

**Size.** `core/` and `kernel/` without tests:
- the bar reports 2,399,551 bytes against 0.30.1's 2,387,735;
- against this branch before the step (b94e8a5's 2,393,564), +5,987 bytes;
- by diff lines, kernel/prove.ts +102 −9, core/infer.ts +22 −31: the join's `stepWith` loop, with its copy of
  `keyValue` now prove.ts's.

**Reuse.**
- **Reused:**
  - the interpreter's `evalE`/`evalC` (a model read as a state);
  - prove.ts's `mapKeys`, `eachRead` and `matchMany` (the sort of a key is the matching `matched` already does);
  - the kernel's quantified-flag variables;
  - infer.ts's `keyValue`, moved to prove.ts and shared.
- **New search:** about 70 lines (`modelInstances`) and three retry loops.
- **Could be shared:**
  - infer.ts's `mapsOf`/`stateOf` read a model as a state as `modelInstances` does, and could share one helper;
  - the three retry loops (`proveThinned`, `proveLaw`, `stepWith`) are one pattern: a goal, its instances, a model, again.

**Spend.**
- The pilot: 56 jobs, 6,889.8 s of job time, plus one job of 11.8 s. Estimated about $0.25; its hour isn't billed yet.
- The quick bar: estimated $1.02 from its task seconds; its hour isn't billed yet.

**Where it leaves the design.**
- S3 is in, and its one gain is a law about three keys.
- Its one loss is the kernel's cost on a law about four keys.
- The next step is still S2 (views, so that the join finds the three-key forms) with S1's sorts cutting the prover's
  tuples. For the exclusion laws over 4 to 5 keys (decentralized, distributed, sharded KV), it is S4, which says them
  as sums at one key.

## Citations

- Goel, Sakallah. On Symmetry and Quantification: A New Approach to Verify Distributed Protocols. NFM 2021.
  [arXiv:2103.14831](https://arxiv.org/abs/2103.14831). Towards an Automatic Proof of Lamport's Paxos, FMCAD 2021,
  [arXiv:2108.08796](https://arxiv.org/abs/2108.08796).
- Yao, Tao, Gu, Nieh, Jana, Ryan. DistAI: Data-Driven Automated Invariant Learning for Distributed Protocols. OSDI 2021.
  [PDF](https://www.cs.columbia.edu/~nieh/pubs/osdi2021_distai.pdf).
- Yao, Tao, Gu, Nieh. DuoAI: Fast, Automated Inference of Inductive Invariants for Verifying Distributed Protocols.
  OSDI 2022. [USENIX](https://www.usenix.org/conference/osdi22/presentation/yao),
  [PDF](https://www.cs.columbia.edu/~nieh/pubs/osdi2022_duoai.pdf), [code](https://github.com/VeriGu/DuoAI).
- Koenig, Padon, Immerman, Aiken. First-Order Quantified Separators. PLDI 2020.
  [PDF](https://people.cs.umass.edu/~immerman/pub/FOQuantifiedSeparators.pdf).
- Koenig, Padon, Shoham, Aiken. Inferring Invariants with Quantifier Alternations: Taming the Search Space Explosion
  (P-FOL-IC3). TACAS 2022. [arXiv:2112.05304](https://arxiv.org/abs/2112.05304).
- Karbyshev, Bjørner, Itzhaky, Rinetzky, Shoham. Property-Directed Inference of Universal Invariants or Proving Their
  Absence. CAV 2015; J. ACM 64(1), 2017. [PDF](https://www.tau.ac.il/~sharonshoham/papers/jacm17.pdf).
- Feldman, Wilcox, Shoham, Sagiv. Inferring Inductive Invariants from Phase Structures. CAV 2019.
  [arXiv:1905.07739](https://arxiv.org/abs/1905.07739).
- Hance, Heule, Martins, Parno. Finding Invariants of Distributed Systems: It's a Small (Enough) World After All
  (SWISS). NSDI 2021. [USENIX](https://www.usenix.org/conference/nsdi21/presentation/hance),
  [PDF](https://www.andrew.cmu.edu/user/bparno/papers/swiss.pdf).
- Padon, McMillan, Panda, Sagiv, Shoham. Ivy: Safety Verification by Interactive Generalization. PLDI 2016.
  [PDF](https://ilyasergey.net/CS6213/_static/papers/ivy.pdf). Padon, Losa, Sagiv, Shoham. Paxos Made EPR: Decidable
  Reasoning about Distributed Protocols. OOPSLA 2017 (listed in [Shoham's SAS 2018
  talk](https://www.tau.ac.il/~sharonshoham/talks/sas18.pdf)).
- Feldman, Padon, Immerman, Sagiv, Shoham. Bounded Quantifier Instantiation for Checking Inductive Invariants. TACAS
  2017; LMCS 2019. [arXiv:1710.08668](https://arxiv.org/abs/1710.08668).
- Pnueli, Ruah, Zuck. Automatic Deductive Verification with Invisible Invariants. TACAS 2001.
  [Springer](https://link.springer.com/content/pdf/10.1007/3-540-45319-9_7.pdf).
- Emerson, Kahlon. Reducing Model Checking of the Many to the Few. CADE 2000.
  [TR](https://www.cs.utexas.edu/ftp/techreports/tr00-03.pdf).
- Ip, Dill. Better Verification Through Symmetry. Formal Methods in System Design 9, 1996 (CHDL 1993 version:
  [PDF](https://www.cs.ubc.ca/~ajh/courses/cpsc538d/ID93.pdf)).
- Emerson, Sistla. Symmetry and Model Checking. Formal Methods in System Design 9, 1996.
  [PDF](https://people.irisa.fr/Nicolas.Markey/PDF/Papers/fmsd9(1-2)-ES.pdf).
- Pnueli, Xu, Zuck. Liveness with (0, 1, ∞)-Counter Abstraction. CAV 2002.
  [Springer](https://link.springer.com/doi/10.1007/3-540-45657-0_9).
- Zhang et al. Inductive Invariants That Spark Joy (Kondo). OSDI 2024.
  [USENIX](https://www.usenix.org/conference/osdi24/presentation/zhang-nuda). Zhang et al. Basilisk: Using Provenance
  Invariants to Automate Proofs of Undecidable Protocols. OSDI 2025.
  [USENIX](https://www.usenix.org/conference/osdi25/presentation/zhang-tony).
- Harrison. Without Loss of Generality. TPHOLs 2009. [Paper page](https://www.cl.cam.ac.uk/~jrh13/papers/wlog.html).
- Ge, de Moura. Complete Instantiation for Quantified Formulas in Satisfiability Modulo Theories. CAV 2009 (MBQI).
  [Springer](https://link.springer.com/doi/10.1007/978-3-642-02658-4_25).
