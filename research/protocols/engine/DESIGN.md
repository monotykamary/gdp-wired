# One engine for parameterized relational rules: small instances, minimal patterns, diagrams

**The shared structure.** The ten pilot protocols are one kind of system: a few interchangeable sorts (nodes, values,
epochs, ids), yes/no or few-valued maps over tuples of them, guarded steps that add and remove tuples, and safety laws
that forbid a small bad pattern ("two nodes locked at one epoch"). The tools that prove all ten (DuoAI, DistAI, IC3PO,
UPDR, Cubicle's BRAB) use three facts about such systems: a law over k keys per sort can be found, and vetted, on
instances of about k elements per sort; what is never reached is upward-closed, so it is an antichain of minimal
patterns; and a counterexample to induction names a pattern (its diagram) that can be blocked as one more law.

**The engine, a mode of the invariant search** (core/infer.ts, gated on rule shape: maps of yes/no or few values over
keys of keySorts' sorts, a caller law over several keys; off for CHC, counters and every rule without keyed maps):

1. **Small instances, exhaustively** (BRAB's finite instances, DuoAI's simulation made complete). Each key sort bounded
   to 2–3 elements (its template width), params set small, each input over its sort's elements (a carried set over
   its subsets, a function's values over its arguments), every reachable state found by BFS up to a state cap and a
   counted step cap. States are deduplicated as they are; renaming within a sort (symmetry) and bitset states are the
   next step where an instance outgrows the caps, and research/hw/compile.ts's exact word ops are the hook past that.
   These states are the rows the patterns are read from: a cube true of every reachable small state at every
   assignment of its keys, in place of random runs' samples.
2. **The antichain of minimal patterns.** keySorts' template views (every sub-template, plain, composed and
   function-part places, order atoms between a sort's keys and values) give the literals; every minimal cube that no
   reachable small state holds at any assignment is a candidate law ¬P, one per renaming of a sort's keys
   (subsumption by literal subsets and canonical renaming). This is the enumeration stage's generator, now on
   exhaustive rows, so the first set is the small instance's true facts rather than a random sample's.
3. **Checking, with diagram blocking** (UPDR, IC3PO). The candidates and the caller's laws are checked goal by goal by
   the kernel (the EPR path inside proveLaw), each model judged by the interpreter:
   - a model whose state is a reachable small state's row (in every view it reads) is a real counterexample: its cube
     is dropped, as Houdini drops one;
   - a model whose state is no reachable small state's, in some template view, is a counterexample to induction from
     an unreachable state: its diagram there (each few-valued cell and order atom at its value) is blocked as a new
     law ¬diagram, generalized by dropping literals while no reachable small state's row is inside it, and the round
     goes on. This strengthens, which Houdini alone can't: it is how a caller's law with too few cubes gets the rest.
   The set left with every goal proven is proven again whole by proveRule with the search off: the kernel's proof,
   checked, its certificate as for any law. Nothing new is trusted.
4. **Order and functions** are atoms like the others: an epoch against a node's epoch, ring positions, `idn(x)`.

**What it reuses:** keySorts and the views (addView), the enumeration's minimal-cube search and its canonical renaming,
the interpreter's judgement of a model (stateOf, requestOf, holdsAt), the EPR path through proveLaw, prove() for the
final set. **What it replaces:** the random deeper runs of the stage, and Houdini-only weakening as the only response
to a counterexample.

**Measured in this order:** a local probe on distributed_lock and toy (state counts, candidate counts, whether
round 0 stops being too strong); the pilot on all ten (2 runs at 60 s, tight caps); the six proven stay proven; the
quick bar against 5d4da3f's baseline; one full bar at the end.

## Where it stands (read this first; the checkpoints below are the history)

**Branch and code**
- **Branch:** gen/enum4, in the worktree ../gdp-wired-enum4. It started from gen/rel8 9987874 (main 5d4da3f plus gen/epr3).
- **Merged in:** gen/epr4, gen/epr5 at 0b65591, gen/epr6 at e47121a, and gen/epr7 at 977e9c6 (decideLaw about 2.6× faster on distributed's goals).
- **Where:** all the engine's code is in core/infer.ts, and nothing trusted changed. It runs as `engine()` inside `inferLawsSearch`, after a join that found nothing, on rules of keyed maps whose scalars take few values (`few`).
- **A commit message to read with care:** c105a71's message says "an ordered sort's keys at every value up to its largest". That change was reverted in 689f492 (it made ring's rows heavier, and its run overshot to 69 s); 689f492's own message doesn't say so.
- **Size:** core/infer.ts is 214 KB, against 202 KB at ea838a3 and 162 KB at 9987874.

**The stage, in order**
1. **Template:** views over each key sort, up to its width, with order literals and function-part places.
2. **Small instance:** a BFS over canonical states, the step compiled once (`loadJs`), at most 4 s, then random walks where the BFS was cut.
   - **A view's rows** (the engine's own views, `product`): at most per^keys a state, 64 at least, the cut on the most-valued sort. Before, every key was cut to `per` values, so distributed's 4-key views (2 a key) never saw epochs 2 and 3, and "two locks" or "two transfers" looked unreachable. The join's views are as they were.
   - **A model's state:** every row up to 1024, so that the realness and blocking checks read it at the keys the model names.
3. **Enumeration:** minimal cubes, up to 400 a view and at most 4 literals.
4. **Round 0** is the minimal (≤ 2-literal) cubes, at most 24, else 16 in all: distributed 17, ring 16, toy 9, decentralized 16, sharded 17, wo 24. Before, it was 64 places.
5. **Rounds** (Houdini plus IC3/PDR). The goals are the caller's law first, then the cubes.
   - **Deciding a goal:** the EPR path first (`decideLaw`, a cube's goal within 2 s). If it runs out of time on a cube, the cube is unsure at once, without the 2 s CDCL search after it (ring's unsure cubes cost 5 s before, 2.5 s now). Else the CDCL search; for the caller's law, the proof path too.
   - **A cube false at a start** is never asked. Its start goal's model is judged at the interpreter's own start for the model's params, keys and function values (facts checked at those keys); `atStart`, cached. A start model in the goal loop is real the same way. This catches ring's `z + 1 <= idn(x) and w + 1 <= idn(y)` and its twins.
   - **A counterexample's state is blocked** first by the enumeration's minimal cubes false there (`blockers`), at most 2, ranked by how many of the last 16 counterexample states each rules out, then by fewest literals. Only where none is false there do its diagrams block it. A blocker already blocked this round blocks as well. A blocker already in the set does not: such a model is spurious against the set, so the goal is unsure.
   - **Drops:** a dropped cube (real, or at the set's proof) never comes back, as a blocker or by relevance (`dead`). A drop takes back only the proofs made since the dropped cube came in (`provenAt`, `addedAt`, `unstand`), not every proof.
   - **Growth:** each round adds the cubes most relevant to the counterexamples so far:
     - **scoring:** false at the caller's, 4096; may be false at the caller's, 64 (cells the model leaves unnamed, wo's voting quorum); false at the cubes' unsure obligations, 1;
     - **how many:** what a quarter of what is left affords at the costliest round's mean per goal (250 ms at least), less the goals asked again;
     - **when the caller's law fails with no diagram:** the round grows by relevance and goes on, instead of ending.
   - **The set's proof:** `prove()`. A cube it fails at is dropped and the proof asked again at once (up to 24 times).
   - **Reserve:** the sums pass gets min(10 s, a quarter of what is left).
6. **Trace events** (GDP_INFER_TRACE=2): 'join small instance', 'join template', 'join view', 'join enumerated' (rounds), 'join exists', 'join set', 'join cubes' and 'join made'. The per-goal trace (`GDP_GOAL_TRACE`, 'join goal' with each goal's ms and verdict, and its blockers), the set-proof probe (`GDP_ENGINE_PROBE`) and the dump for woprobe.ts (`GDP_ENGINE_DUMP`) are at 689f492, taken out after. Bring them back from there for a probe, and take them out before a merge.

**Verdicts** (`runs/engine/q15`, all ten, 2 runs at 60 s; `q16` for the six's paths after the last change)
- **The six, proven:** sync 7–10 s, async 17–24, decentralized 20–32, 2PC 13–21, ticket 29–45 (ticket never runs the engine; 3 runs each at ea838a3 and at HEAD gave 32–37 and 29–36, Modal's noise), toy 16–18.
- **The four, unknown:** distributed 63–64, ring 60, wo 63–65, sharded 21–28.
- **Round timings** (Modal; the engine starts after a join of about 10 s on distributed, 3.5 s on ring, 26 s on wo):
  - distributed: round 0 (17 cubes) about 1 s, round 1 (21) 1.5–2 s, round 2 (33) 10–13 s, round 3 (52) 18–24 s, round 4 (64) to the wall. Nothing true is dropped now (before: two holders, and a live transfer means nobody holds). The set reaches its proof in some runs (q11, at 44.6 s), and the drop loop then spends 1–5 s a cube.
  - ring: round 0 (16) 25–26 s, of which 9–10 unsure cubes at about 2.5 s each; round 1 2–5 s; the set's proof drops the own-id and leader laws, which have no support without the between law.
  - wo: round 0 (24) about 2 s; the caller's goal costs 9–17 s a round from round 1.
- A Mac M-series laptop runs these about 2.3× faster than Modal's 2-CPU container. Distributed reaches round 4 at 26 s locally.
- No protocol moved, so no bar ran.

**The probes**
- **sharded** (`runs/engine/sh1`): proving the caller's law from its 17 enumerated cubes alone, with a 120 s budget and a 150 s cap, did not finish: killed at 150 s, no verdict. The cubes are the written laws and their twins. The README already has the written invariant killed at 420–600 s (an elimination blow-up on 5-key laws). So the gap is the kernel's cost on 5-key laws, not the rounds, a drop or the frames. It belongs to kernel/.
- **wo** (`runs/engine/wo11`, woprobe.ts on the set at the caller's last failure): with each written ∀ law added on its own, the caller's law fails with the others, but with "a leader has the voting quorum's votes" it proves, in 29.7 s. That law's own step from the set fails (a model), so it needs support beside it. It scored 0 because the caller's counterexamples leave VotingQuorum's cells unnamed, and holdsAt skips such rows. The may-fail score now ranks the voting-quorum cubes (q14 picks two of them), but not yet the exact one (`Votes[64·x + y] is 0`, x the leader). wo also starts its rounds at 29 s, and its caller's proof with the law costs 29.7 s, so it can't fit 60 s on Modal until those costs fall.

**Since 3d5668a** (ring's expressibility, wo's three questions; `runs/engine/r1`–`r7`, `wo12`)
- **The between law is in the space:**
  - **The enumeration:** a view whose literals are more than 40 also gets the 4-literal cubes that hold a chain of three keys of one sort (a < b, b < c: betweenness and each cyclic turn), 200 a view, any ordered sort, ranked like the rest.
  - **The small instance at several function tables:** a function the kernel knows by its facts alone (no recurrence, no call), on a template sort, runs at its own table and up to three others that keep its facts on the sort's keys (reversed, turned by one). Their states' rows are read under their own table and never join the search's samples. With ring's one table (x XOR 5), every y < z < x had idn(x) > idn(y), so the third turn was not minimal.
  - **No cube reads no state.** A cube over keys and functions alone is a fact of the tables, or false; the junk blockers like `w + 1 <= idn(x) and w + 1 <= idn(y) and w + 1 <= idn(z)` were these.
  - **Ring's 198 → 160 cubes** now hold all three turns, the leader's and the own-id law.
- **The set's proof blocks before it drops:** at a cube with a model at its step, the enumeration's cubes false at the model's state (not in the set) join it, and the rounds go on. Only where there are none is the cube dropped.
- **A cube's EPR budget is 1 s** (was 2 s): ring's round 0 went from 27 s to 16–20 s; distributed's rounds end at 46–52 s (was 56+); toy 12–19 s.
- **Relevance ties go to the fewer keys** (the more particular law).
- **Ring still unknown.** Round 0 (16 cubes, 11–12 unsure) ends at 24 s. A set's proof over its 14–17 cubes costs 2–21 s, against 1.2 s locally for the written invariant (`run.ts --skip search,broken`). Round 0 pads its 9 minimal cubes with 3-literal ones that are unsure at 1 s each, and its set holds the true but hard "own id home means everywhere" law. That law's blockers (the path law: `x<y<z ∧ Pending[idn z, x] is 0 ∧ Pending[idn z, y]`) cost more rounds than are left.
- **wo (a):** the exact cube (`Leader[x] ∧ VotingQuorum[y] ∧ Votes[64·x + y] is 0`) climbs with the caller's counterexamples: 66th, then 14th, then 6th by the third. It ties at the top score with six 3-key cubes, which the old tie-break (wider first) put ahead. Now the fewer keys go first.
- **wo (b)** (`woprobe.ts <dump> support`): from the set at the caller's last failure in round 2 (35 laws), "a leader has the voting quorum's votes" has its step proven from the set alone, in 27.5 s (21.6–35.3 s with each written law beside it). Its support came in through the rounds, so nothing written is missing. The cost is the kernel's: 21–35 s for each such goal.
- **wo (c):** the 21–29 s before wo's engine is the join (9 s locally, about 17–21 s on Modal), the small instance's BFS at its 4 s cap, and the template, about 3 s.
  - **Tried:** a join capped at a quarter of the wall where the engine follows (10 s at least). It saved 2–6 s on wo but put 2PC's join (24 rounds to inductive, up to 11.1 s on a slow container) too near the cap, and once starved decentralized's sums-pass join. Reverted in 051d07c (e4a4602's message still lists it).
  - **What would help, not tried:** a smaller BFS share for an instance the BFS doesn't finish, and the caller goal's own cost.
- **Verdicts** (`r7`, all ten, 2 runs): sync 6–7 s, async 20–28, decentralized 25–29, 2PC 16–17, ticket 23–29, toy 14–19, all proven; distributed, ring, wo and sharded unknown. Nothing moved, so no bar.

**Since 673a262** (`runs/engine/r8`, 2 runs each)
- **Round 0** is the minimal cubes alone, at most 24, or the whole enumeration where it is 16 cubes or fewer (toy's 10, of which 7 minimal).
  - **ring:** round 0 is 9 cubes and ends at 7–10 s (was 24 s, with 7 padded 3-literal cubes unsure). Rounds 1–3 cost 2–5 s each. Growth then takes it to 21–28 cubes, and the set's proof over those costs 23–29 s, to the wall. The kernel side (gen/epr8) has the set-proof cost.
- **A small instance's BFS that won't finish** (a quarter of its share gone, 1 s at least, and its queue still a quarter of what it found) is cut there, and the walks get half a second.
  - **wo:** the instance takes 1.5 s (was 4 s), with 460–500 states (was 830–1050) and 290 cubes enumerated locally (was 210); the exact voting-quorum cube is still among them. The engine starts at 20–25 s (was 21–26). The caller's goal still costs 9–17 s a round; that is the kernel's side.
  - **Every BFS that finishes is as it was:** decentralized, distributed, ring, toy, sharded.
- **The joins:** 2PC's join reaches its proof in 24 rounds, at 5.2–5.4 s; decentralized's sums-pass join in 6 rounds, at 2.6–2.9 s. Untouched.
- **Verdicts:** 2PC 15–16 s, decentralized 26–31, toy 16–19, proven; wo, ring and distributed unknown.

**Since 4c80da4: gen/epr8 merged, 7 of 10** (`runs/engine/s1`–`s7`)
- **Merged:** gen/epr8 (rebased on 673a262; proveSetFast, keys matched as radix sums, EPR-first proveLaw) and research/protocols/epr/proveSetFast.patch (the set's proof loop asks `prove(..., true)`).
- **Proven:** sharded KV, in 25–44 s. **The seven** (2 runs at 60 s, s6–s7): sync 8–10 s, async 23–25, decentralized 13–16, 2PC 18–19, ticket 32–35, toy 10–16, sharded 27–44.
- **distributed's endless blocking:** it was one law re-blocked, not a variant. "never started is 0 and Ep[x] + 1 <= y and Ep[x] + 1 <= z" is false at a start, so it was struck at each round's start check, and then blocked again by the diagram fallback (which had no start check).
  - **The cause is general:** y and z are read only by order literals that bound them from one side. A large y always has `Ep[x] + 1 <= y`, so the cube is "never started is 0" in disguise. The small instance only holds it because y ranges over the epochs a state has. The same goes for the EPR agent's "42 of 94 false at large epochs".
  - **The fix (`oneSided`):** no cube, enumerated or diagram, with a key read only by order literals bounding it from one side (a key in a map's place or a function's argument counts as read). Diagrams are checked at a start too. Ring: 160 → 69 cubes; distributed: 178 → 140; the needed laws all stay.
- **Blockers** take the cubes that may be false where the model leaves cells unnamed (below the false ones), as relevance does.
- **distributed now:** its rounds converge by 14–24 s, set proofs about 1 s each. But true laws (a live transfer above every epoch, a live transfer means nobody holds, a holder's epoch above every other) get dropped one at a time, as real counterexamples nothing blocks yet, and once dead they block nothing later.
  - **Tried and reverted:** keeping such a cube unsure instead (IC3 not pushing a lemma). The set's proof then dropped the same laws one by one.
  - **What it needs:** the support in the set together. The written laws as one set prove (README, given mode); the rounds don't assemble them. Next: block by the whole written-law-like antichain at a counterexample (several cubes, not two), or a drop that keeps a cube whose failure is a state that a dead cube's support would rule out.
- **wo's join** (step 3): its 10 rounds end by 3.4 s locally. The time is one query in its last round, "every k: Leader[k] <= VoteRequestMsg[k]", 6.3 s locally (about 14 s on Modal), unknown. A "set unchanged for N queries" rule would cut 2PC's join, whose set stays the same for 5–10 rounds before it closes.
  - **Tried and reverted:** a join query a quarter of its budget where the engine follows (the proving joins' longest queries are 24–333 ms locally). It cut wo's query to 3.9 s, but stopped decentralized's sums-pass join at round 5 of the 6 it needs (both runs unknown).
  - **Next:** cap only a query whose goal the join has asked unknown before, or run the engine's small instance and enumeration (no kernel) while the join's last query runs.
- **Checking a change to the join:** measure the first join and the sums pass's (decentralized proves in the second).
- **The bar** (569ed3b against 5d4da3f, full mode on rw, f1, f2, g332, suite, onecpu; Modal, 495 s, estimated $0.7; <main>/runs/bar/runs/569ed3bbf25b-vs-5d4da3f49013-full-2026-10-292350/REPORT.md): wrong 0 everywhere and nothing lost. f1 90/92 as the base; f2 32 against a base mean of 31.33 (one task, gained 0 after 3 reruns a side); rw 318/361 as the base; g332 332/332 with the same search on every goal (+3.4 s summed); the suite 227/227; onecpu no failures. core/ and kernel/ are 2.77 MB against 2.67 MB (+101 KB).

**IC3's frames, gen/epr9 merged** (`runs/engine/f1`–`f4`, `h1`)
- **Frames:**
  - a cube whose relative induction fails without a counterexample from a start is pending, not dropped: out of the set the others assume;
  - the pending cubes are pushed together each round once the set has changed: each is asked with the set and every other pending cube assumed (one frame); those with a model go out, and the rest are asked again until none has one (an undecided one stays, as Houdini keeps it);
  - what is left comes back into the set together, each cube twice at most;
  - the set's proof demotes rather than drops;
  - a start's counterexample still drops a cube for good;
  - 'join frames' (pending, pushed, promoted) is a progress event.
- **ring:** cubes come back. Round 4 promotes 1–2 of its 2–3 pending ones (the own-id and path laws). The sets still fail at the own-id and leader laws, with set proofs of 1–19 s at 9–21 cubes.
- **distributed:** 10–43 pending, every one with a model even with all the others assumed, none back. So its support was in neither the set nor the frame.
  - **The written laws prove as one set** (`epr/givenprobe.ts`: 0.8 s fast, 3.6 s usual), so the gap is the enumeration.
  - **"Two live transfers are one"** (4 literals over 4 keys, in a view of more than 40 literals) was missing. Now enumerated: "two of a pattern are one" (DuoAI's), a two-literal pattern some row has beside its image under a renaming of the view's keys within their sorts, 200 a view. Distributed 140 → 151 cubes, ring 69 → 78; toy, sharded and decentralized unchanged.
  - With it, pending falls to 10–12; still none come back, and the sets fail at "Held[x] ∧ Ep[x] + 1 <= z ∧ z <= Ep[y]", "Locked ∧ Locked", "Transfer ∧ started is 0".
- **Houdini over all the enumeration at once** (`h1`, distributed, 140 cubes, a 250 s budget): each fast set proof is about 10 s at 114–140 cubes. 30 drops in 190 s, no inductive set. Too costly as a start; dropped.
- **wo's join query:** the 6.3 s query is the first ask of "every k: Leader[k] <= VoteRequestMsg[k]" (rounds 1–9 ask other goals), so a cap on repeats saves nothing. Not built.
- **Verdicts** (`f4`, 2 runs): sync 11–13 s, async 23–26, decentralized 15–18, 2PC 18–20, ticket 29–34, toy 11–15, sharded 27–36, all proven; wo 64–68 (one run past the wall by 8 s), unknown.

**The expressibility map** (each written law in models.ts's `human`, against the engine's enumeration; `smallprobe.ts` with CUBES=made lists it, and 'join view' each view's literals)

| Protocol | Written law | In the candidate space? | Missing block or cause |
|---|---|---|---|
| wo | a vote message means voted | yes, selected | |
| wo | one vote message per voter | yes, selected | |
| wo | a counted vote was sent | yes, selected (two-literal first) | |
| wo | a leader has the voting quorum's votes | yes, not selected (3 literals, among 238; scores 0 against the caller's 2 counterexamples) | selection |
| wo | nothing before init | yes, selected | |
| wo | after init the voting quorum has a member (∃) | yes: the ∃ stage finds it, with its witness | |
| distributed | a holder's epoch is above every node's other | yes (`Held[x] ∧ Ep[x] ≤ Ep[y]`) | |
| distributed | two holders are one | yes | |
| distributed | nothing before init | yes | |
| distributed | a locked epoch is its node's epoch or below; a live transfer above every epoch; a live transfer means nobody holds; two live transfers are one | no | the views' rows have Transfer and Locked only at 0, so there is no `≥ 1` literal. The engine's small instance has 9 states (3 param vectors); a hand BFS with the same domains has 19 for one, Transfer and Locked set. A sampling bug (`hand-dl.ts`) |
| distributed | a locked epoch at a node's epoch is its own | implied by the caller's law | |
| ring | a leader's id is the largest | no | no Leader = 1 literal: the engine's small instance (25 states) has no leader. A hand BFS with the same domains (size 3, ids 5, 4, 7) has 30 states, 6 with a leader. The same sampling bug |
| ring | a node's own id pending at it is the largest | no | `Pending[idn(x)·64 + x] ≥ 1` never in the rows (the same bug: the max id never returns home) |
| ring | an id pending past a node is above it (btw) | no | the same bug. Also a disjunction of three cyclic orders: three cubes of 4 literals over 3 keys, in reach of the 4-literal limit of the (lo, lo, lo) view (36 literals) |
| sharded | all six (one owner per key, a table entry is its owner's, a key in transfer has no owner, one transfer per key, one value per owner and key, nothing before start) | yes: the 17 enumerated cubes are them, and their twins | the caller's law still fails from the set (no diagram). To check: the caller's law from those 17 alone, in a probe |

**The sampling bug, fixed** (`runs/engine/p35`, all ten, 2 runs):
- **The causes:**
  - Distributed's `e1`, an epoch value, was set to the epoch sort's size (4), above every request's epoch, so no grant ever fired.
  - Its `first`, a node, was drawn outside the node domain.
  - Ring's `size` was 4 while `n1`, in no template sort, was drawn over 0..2, so the ring never closed.
- **Now:**
  - A param that bounds keys (`k < p`) is the least size of the sorts it bounds.
  - A param a key equals or a read is at (`k = first`, `M[first]`) is an element of that sort, which is then not renamed (pinned).
  - An input that only a param bounds takes every value below it.
- **Small instances:** distributed 36 states over 4 param vectors (it was 9); ring 145 states with leaders (it was 25, none).
- **The enumeration:**
  - Ring has `Leader[x] ∧ idn(x) ≤ idn(y)` (with x ≠ y and idn injective, the written "a leader's id is the largest") and `Pending[idn(x)·64 + x] ∧ idn(x) ≤ idn(y)` (the own-id law).
  - Distributed has `Locked[y,x] ∧ Ep[x] + 1 ≤ y` (a locked epoch is its node's or below), and the Transfer/Locked cubes: 183 cubes, from 58.
- **Verdicts:** the six proven (sync 9–11 s, async 22–26, decentralized 26–29, 2PC 21–22, ticket 25–34, toy 24–29); the four unknown.
- **What holds them now: round 0's decisions.**
  - Ring's round 0 (64 cubes) ends at 59 s with 5 unsure.
  - Distributed's ends at 59 s with 10–11 unsure and 3–5 diagrams.
  - Next: a first round they can afford. Fewer places at first (the minimal cubes and a few turns), growing by relevance; or the EPR decision's cost in the stage (about 0.5–1 s a cube).

**What holds the four now**
1. **ring:** the between law isn't in the space. Its three cyclic cubes are 4 literals over 3 node keys plus a pending id: `x + 1 <= y and y + 1 <= z and Pending[64·idn[x] + z] and idn(x) <= idn(y)` and its two turns. None is among the 222 enumerated. Without it, the own-id law and the leader laws have no support. Also: 9–10 cubes per round that the EPR path can't decide within 2 s.
2. **distributed:** the rounds converge (the diagrams fall from 12 to 0 by round 4–5), but rounds 2–3 cost 10–24 s on Modal. Next: fewer goals asked again after a drop (cores from decideLaw would name a proof's support; kernel/), or a set's proof that blocks a failing goal's counterexample instead of dropping a true law whose support went.
3. **sharded:** the kernel's cost on 5-key laws (see the probe).
4. **wo:** the exact voting-quorum cube (rank it by the caller's model's own keys: x the new leader), and the costs before the rounds (the join and a 4 s BFS, 26 s in all) and of the caller's goal.

**Open costs**
- The EPR decision is 0.1–2 s a goal in the stage after epr7; ring's unsure cubes still run to the 2 s budget.
- The join before the engine: about 10 s on distributed and 26 s on wo.

**Probes** (research/protocols/engine/)
- `smallprobe.ts [id]` (MS, CUBES=1|made, EXIT): the small instance, round 0's cubes (CUBES=1) or every enumerated cube (made), the views.
- `woprobe.ts <dump>`: needs GDP_ENGINE_DUMP (689f492).
- `exprobe.ts`, `bfsprobe.ts`, `stepprobe.ts`, `preprobe.ts`, `hand-dl.ts`, `hand-ring2.ts`.
- Jobs are in jobs-*.json (q1–q16 this round). Run them with `modal run modal/run.py --jobs <file> --out runs/engine/<name>`.

**Rules**
- Local runs: ≤ 30 s, one at a time (there is no `timeout` on the Mac: `perl -e 'alarm shift; exec @ARGV' 30 bun …`).
- Modal: 60 s budgets with `timeout -s KILL 90` in the container, 2 runs a config.
- The six must stay proven.
- Before a merge, take out every diagnostic. Today none is in the code; the trace events are progress events.

## Status (checkpoints at 21692d8 and after steps 1, 2, 4; gen/enum4 from gen/rel8 9987874, gen/epr4 merged)

**Built** (core/infer.ts only; nothing trusted changed):
- **The enumeration stage from gen/enum3:** template views per keySorts sort (plain, composed, three-part keys, function-part places `Pending[idn(x)·N + y]`); literals: few-valued cells (the top value as "at least"), a value cell `= 0`, order literals between a sort's keys, its cells and function values (`t ≤ u`, `t < u`), two keys of one sort strictly ordered; the frame takes the caller's guards on one key (k < 64, k < size); minimal cubes ≤ 3 literals (4 where a view has ≤ 40 literals), canonical per renaming, contradictory orders out; cubes the caller's laws imply dropped; at most 32, those reading the caller's maps first. Houdini: the caller's laws first, a CDCL model or refutation first, else proveLaw within the search's end (`within`, counted clock); models judged by the interpreter (`realCti`); a real counterexample's cube weakened by one literal; the set proven whole with its trees kept. The stage runs after a join that found nothing or ran out of time; the first round has the whole kernel clock, later ones leave 21 s for a sums pass.
- **Also from enum3:** the join's runs scaled to the budget (`least`); no cell candidate mixes a composed map with a plain one.
- **Engine piece 1, the small instance:** in `enumerated()`, BFS over params and inputs drawn over each sort's first elements (`keyDom`, `fnDom`, a param compared with a sort set to its size), up to 20,000 states and a seventh of what is left; its states go first in `samples`, so the views' rows are read from them.
- **Engine piece 3, diagram blocking:** `diagrams(pre)` for a real counterexample's state (`lastPre`, set by `realCti`): per template view, a row of that state no small state's row is, as the literals true there over the cells the model names, generalized by dropping literals while no small state's row is inside; blocked as new cubes (`blocked2`), the round going on.
- **Tracing:** `GDP_ENUM_LOG=1` prints `[enum t]` and `[enum cube]` lines. Trace only; take it out before a merge.

**Measured** (Modal, 2 runs at 60 s, 90 s caps; `runs/engine/e2`–`e6` in this worktree):
- **toy_consensus_forall:** proven, 37–57 s.
- **distributed_lock:** small instance 20,000 states (the cap). Round 0 has 32 cubes: 12 real drops and 17 diagrams blocked. Round 1 has 37 cubes and is cut short by the budget, since the stage starts at about 26 s. Unknown, 43–51 s.
- **consensus_wo_decide:** the caller's counterexample is real (845 cells named), but in every template view its rows are rows of small reachable states. The bad pattern is wider than the views, so there is no diagram. Unknown, 62–68 s.
- **ring_leader_election:** the small instance has 868 states (size 3). The caller's counterexample is "real", but the model's `idn` differs from the interpreter's (`n XOR 5`): `stateOf` doesn't carry a model's function values, so its views' rows are computed with the real `idn`, and they read as reachable. Unknown, 19–22 s.
- **sharded KV:** the model's keys are huge (154,714,762), and the interpreter's write at every key refuses keys past a million, so the counterexample isn't judged. Unknown, 70–75 s.
- **The six already proven** (sync, async, decentralized, 2PC, ticket, toy): toy checked only. Re-check all six on this branch before any merge.
- **Size against 9987874:** not measured yet.

**Checkpoint after steps 1, 2 and 4, with gen/epr4 merged** (e8e3536 and on; the pilot `runs/engine/p10`, all ten, 2 runs at 60 s):
- **Step 1, the budget:**
  - The stage first, with half the budget (9471de9), lost 2PC (its join was left 15 s) and slowed the others by 10–18 s. It runs after the join again.
  - Its planned share is now the rest of the budget. The sums pass's reserve (min(21 s, a third of what's left)) holds only while the caller's law fails from the set: once it holds, the rounds are Houdini's and keep the reserve's time.
- **Step 2, ring:**
  - A model's function values are carried into the judged state (`withFnsOf`).
  - A model's values past the rule's constants are renamed onto small ones in order (`smallOf`).
  - The caller's law goes straight to the proof path (EPR, whose models are real).
  - A real caller counterexample's diagrams are blocked at once, and the caller is asked again before the cubes (IC3's order).
  - Result: ring's caller law holds from the set after 3 diagrams, about 9 s in. Houdini then stalls: 13–19 cube goals stay unsure (each up to a 2 s CDCL check and a 2 s proof), and the round doesn't finish in 60 s.
  - Halving those caps made more cubes unsure, and distributed_lock overran to the 90 s kill. Reverted.
- **Step 4, sharded:**
  - Its large keys are mixed-coefficient sums the kernel instantiates (`Table[k:262144,key$2#:64,…]`), not large values.
  - A model's cells past a million keys are now left out of the judged state.
  - The caller's counterexample is judged real (828–1,008 cells named), with 0 diagrams, as with wo.
- **Also:**
  - Houdini cores: a cube the CDCL search refuted is skipped while every law its core read stays in the set.
  - The implied filter is lazy (it stops at 32 kept; it was 7 s on distributed_lock).
  - Diagrams are deduped against every law's name. A duplicate name had thrown in the kernel and ended the join (`join failed`).
  - realCti stops at the wall.
- **Verdicts (p10):**
  - The six stay proven: sync 8–9 s, async 23–30, decentralized 19–22, 2PC 18, ticket 29–33, toy 55–60. Toy is near the edge; it was 42 s at 835ac18.
  - The four stay unknown: distributed 63 s, wo 59–62, ring 60–61, sharded 56–72.
  - Broken variants: the same.
- **Overruns left:** sharded 72 s (the caller's proof runs to the end, then 15–20 s after the search), distributed 63 s.
- **Size:** core/infer.ts is 184,749 bytes against 162,204 at 9987874. enum3's stage is +13.2 KB of that, the engine +9.3 KB, tracing included.

**Second checkpoint** (`runs/engine/p12`, all ten, 2 runs at 60 s):
- **toy's margin:** the 13–17 s over 835ac18 was the minimization after the proof: 9 whole-set re-proofs, 23–27 s. The engine's set is no longer minimized. Toy now takes 26–30 s, against 42 s at 835ac18. (A cone read off the Houdini cores didn't help: the caller's law goes to the proof path, which gives no core.)
- **All six proven, safely:** sync 8–10 s, async 25, decentralized 19–21, 2PC 16–22, ticket 31–35, toy 27–28. Broken variants are the same.
- **Taken out:**
  - the diagnostics (`GDP_ENUM_LOG`, `T(...)`; `GDP_ENGINE_SHARE` went with 9471de9's revert);
  - the one-literal weakening of a real counterexample's cube, which bought no verdict.
- **Size:** core/infer.ts is 182,318 bytes, +20.1 KB over 9987874 (enum3 +13.2 KB, the engine +6.9 KB).
- **Step 3 (wider patterns), measured before building:**
  - wo: its widest view, 3 nodes with 71 literals, holds the counterexample's rows as 24 literals over the cells the model names. Each such row, ungeneralized, is a row of a reachable small state (3 nodes).
  - sharded: the same at its widest view (5 keys, 21 literals): the rows traced were reached as they stand, so nothing is left to generalize.
  - So the two counterexamples' states agree with a reachable small state on every tuple the template's views cover (wo's width is 3). A wider view needs a small instance at least that wide: the 4-node wo BFS, past 3 nodes' 1,400–3,250 states in 30 s, is out of reach. Ivy's wo invariant also needs an ∃ (a leader has a quorum that voted for it), which the ∀ cubes can't say.
- **Overrun left:** sharded ends at 77 s. Its search ends near 59 s; the rest is after it, in core/dsl.ts's deeper bounded runs (`withWall(Infinity, …)`), which is outside core/infer.ts.

**∀∃ checkpoint** (gen/epr5 merged at 0b65591 and decideLaw applied; `runs/engine/p14`, all ten, 2 runs at 60 s):
- **Probe** (`exprobe.ts`, Modal):
  - wo's written laws prove the caller's law in 30 s, 20 s of it the cyclic certificate. That is with the ∃ law's witness given (`w`, set where `inits ∨ chooses`).
  - The same ∃ law with no witness given doesn't finish in 150 s: proveSome's own witness search is too slow here.
  - So the stage chooses the witness itself.
- **Built:**
  - **Gate:** the caller's law fails with no diagram.
  - **Candidates:** `A → ∃y. B(y)` over a one-key view, where A is a scalar literal or none, and B is 1–2 literals, at least one off its default. Each is true on every small state, with B not at every key. Up to 6, the weaker B first.
  - **Witness:** a ghost, starting at 0. After each step it takes an input where an update of a map B reads takes its branch, else keeps its value. The first that holds along random walks of the small instance is taken.
  - **Houdini:** the ghost is a state variable of the machine it reads (`withGhost`). Its law is a goal; if unproven, the next candidate is tried.
  - **Final proof:** the ∃ law with that witness, through proveSome.
- **On wo:**
  - The stage finds exactly the written ∃ law and its witness: `started = 1 → ∃x. VotingQuorum[x]`, ghost `if inits ∨ chooses then w`. It takes 0.2–0.5 s. With it, the Houdini rounds reach rounds with nothing dropped.
  - It stays unknown. At 60 s the rounds run out of time: the small instance ends near 17 s and round 0 near 37 s. At 120 s, the caller's law fails from the 48 cubes plus the ∃ law.
  - The written ∀ laws need cubes that compete for the 48 places: a 3-key cube (one vote message per voter) and the leader's quorum-votes cube.
- **The small instance, rebuilt for wo's depth:**
  - Its first leader is at depth 5 (`bfsprobe.ts`). The views' rows had come only from the first, shallow states, so no `Leader ≥ 1` literal existed.
  - The rows are now every small state's, at most 20,000 distinct.
  - When the BFS is cut short, its last quarter of the share goes to random walks from its last states.
  - The cubes are taken in turn by the maps they read: 96 a view, 48 in all.
- **Verdicts (p14):**
  - The six stay proven: sync 9 s, async 22–25, decentralized 24–27, 2PC 17–18, ticket 28–30, toy 30 and 87.
  - Toy's 87 s run was a slow container: its small instance ended at 30 s, against 8–14 s. Four more runs took 23–36 s.
  - The four stay unknown, with sharded's overrun gone (50–53 s) and distributed at 47–50 s.
- **Next, for wo:**
  - the ∀ side's selection: the cubes that the caller's counterexample with the ∃ law breaks, first;
  - the time: the small instance and round 0 take about 37 s of 60.

**Small-instance checkpoint** (`runs/engine/p15`, all ten, 2 runs at 60 s):
- **States are now canonical:**
  - cells off their map's default, in key order, the least text under each symmetric sort's renamings;
  - a sort is symmetric unless it is ordered, a function's argument, a param's bound, stored in a cell or written to a scalar.
- **The step is compiled once** (core/machine.ts's `loadJs`; its assumption refuses a request as `allowed` does). It costs 2.4 µs a call, against 13 µs for allowed() plus the interpreter.
- **What canonical states revealed:** the old state counts were mostly insertion-order and explicit-zero copies. Ring's 868 states are 25; distributed's 20,000 (the cap) are 9 under symmetry (33 without, for one param vector); toy's 2,365 are 15.
- **Small-instance times:**
  - Every protocol except wo now takes 8–271 ms to build its complete small instance.
  - wo's space is the large one: 3,800+ canonical states, still cut at 6.7 s on Modal. A cheaper wo needs fewer requests a state, not cheaper states: 2,048 requests a state at about 1.5–3 µs each.
- **Verdicts:**
  - The six stay proven: sync 8–9 s, async 17–24, decentralized 19–20, 2PC 18–19, ticket 30–33, toy 22–26.
  - The four stay unknown.
  - wo runs out of time: round 1 with the ∃ law (nothing dropped) is cut by the end at 48–52 s.
  - Ring and distributed have 5–17 unsure cubes in round 0, through 59 s.
- **Size:** core/infer.ts is 194,769 bytes.

**Obligations checkpoint** (`runs/engine/p17`–`p22`):
- **Built:**
  - PDR's obligation for a cube's model the interpreter doesn't confirm: its state's diagrams are blocked, and the cube is kept.
  - A cube the EPR path doesn't decide (`decideLaw` undefined) gets the CDCL search's answer alone, with no proveLaw fallback.
  - The round's progress event gives its time by part.
- **Tried and reverted:**
  - Dropping a cube whose state's rows are all reached: distributed dropped 29 cubes, and the caller's law then failed.
  - The join at a quarter of the budget on the engine's shape: it lost 2PC and decentralized. The join's clock is the counted one, faster than the wall.
- **Where a round's time goes:**
  - Distributed, before the fallback change: decideLaw 3.4 s for 48 cubes, judging and blocking under 0.1 s. The cubes decideLaw doesn't decide went through the CDCL search and proveLaw, 29 s.
  - Ring: decideLaw 7.6–8.9 s, the CDCL search for the undecided cubes 42–43 s.
  - wo: 20 s before round 0 (the join, then the stage's setup), and the caller's proof 17.5 s.
- **Verdicts:**
  - The six stay proven (p22, 2 runs): sync 9–11 s, async 22–23, decentralized 23, 2PC 19–21, ticket 37–38, toy 23.
  - The four stay unknown.
  - distributed now runs four rounds in 52 s: 9 real drops and 20 unsure in round 0. The unsure are the cubes no EPR decision covers. Dropped at round 3, they take the caller's law with them.
- **Next:** the EPR path for the cubes `decideLaw` leaves undecided (their shapes); the caller's proof on wo.

**wo's time** (`runs/engine/p23`, all ten, 2 runs):
- **Changed:** the small instance gets at most 4 s; the ∃ candidates come at the caller's first failure, with its diagrams; the round timings are out.
- **wo's 20 s before round 0:** the join takes about 10 s and the small instance 4 s. From there, round 0 takes about 21 s, most of it the caller's own proof (the CDCL check, then proveLaw at 10 s at most).
- **wo now:**
  - Round 1 starts at 35–37 s with the ∃ law and 4 diagrams.
  - The caller's law then fails with no diagram at 43–49 s.
  - So either the 52 cubes lack a ∀ law the written invariant has, or the caller's proof runs out within its 10 s.
- **Verdicts:** the six proven (sync 8–9 s, async 27–28, decentralized 14–32, 2PC 17, ticket 30–33, toy 16–29); the four unknown.

**wo's probe** (`woprobe.ts`, `runs/engine/wo2`, `wo3`):
- **Setup:** the stage's set at the caller law's failure in round 1: 52 cubes, the ∃ law as a ghost, and the kinds' laws.
- **The caller law from the set alone:** a model, in 65 s. That is far past the stage's 10 s cap, so in the stage it reads as no model.
- **Adding any one written ∀ law:** still a model, in 48–60 s.
- **Adding every written ∀ law:** proven, 22 s. So wo's gap is candidates, not time.
- **The written laws against the set:**
  - "a vote message means voted": the set has only `Voted[x] = 0 ∧ VoteMsg[x,x]`, not `VoteMsg[x,y]`, y ≠ x.
  - "a counted vote was sent": only `Votes[x,x] ∧ VoteMsg[x,x] = 0`, not `Votes[x,y] ∧ VoteMsg[y,x] = 0`.
  - "a leader has the voting quorum's votes": only `Leader[x] ∧ VQ[x] ∧ Votes[x,x] = 0`, not the y ≠ x one.
  - "one vote message per voter": only `VoteMsg[x,x] ∧ VoteMsg[x,y]`, not `VoteMsg[x,y] ∧ VoteMsg[x,z]`.
  - "nothing before init": present.
- **Why:** each missing law is the off-diagonal (distinct keys) twin of a diagonal cube the set has. The cubes are taken in turn by the maps they read, and the one-key (diagonal) cube of each map set comes first. The 48 places run out after the first turn, before any second cube of a map set. So the cause is the selection, not the width, the shape or the small instance.
- **Next:**
  - within a map set, the cube over more keys first (the general one before its diagonal);
  - or more places for the turns: a second cube of each map set.

**The selection fix** (`runs/engine/wo4`–`wo6`, `p24`):
- **Selection:**
  - Cubes are grouped by the maps they read, fewer literals first in a group, then more distinct keys (a law before its diagonal case).
  - The groups go in turns, ordered by their own first cube; there are 64 places.
  - The DFS keeps 400 cubes a view: at 96, wo's `VoteMsg[x,y] = 0 ∧ Votes[y,x]` was never enumerated, the cap cutting the two-literal cubes in literal order.
  - Of the written ∀ laws, the selection now holds "one vote message per voter", "a vote message means voted" and "nothing before init". It still lacks "a counted vote was sent" and "a leader has the voting quorum's votes": both are in the enumeration, past the 64 places.
- **The caller's goal:**
  - EPR decides it first (`decideLaw`, within a join query).
  - Its proof gets half the remaining wall, not a fixed 10 s.
  - A model of it the interpreter doesn't confirm is an obligation like a cube's, its diagrams blocked.
- **wo now runs IC3's loop:** the caller's models give diagrams in every round, and the ∃ law comes in at round 1 or 2.
  - At 60 s: round 0 ends at 25–28 s and the rounds run to 42 s, then the end cuts them.
  - At 120 s: five rounds; then the caller's law fails with no diagram at 90 s.
  - Still unknown.
- **Verdicts (p24):**
  - The six proven: sync 8–9 s, async 22–25, decentralized 28–29, 2PC 17, ticket 32–34, toy 18–25.
  - The four unknown: wo 57–65 (one run 5 s over), ring and distributed unchanged (waiting on epr6), sharded 29–30.
- **The dump hook is out.** `join cubes` and `join made` are progress events, read by `smallprobe.ts` with CUBES=1 or CUBES=made.

**Relevance** (`runs/engine/wo7`–`wo9`, `p25`):
- **Built:**
  - The caller's counterexamples (its judged models' states, from real ones and from obligations) accumulate.
  - Each round, the enumeration's cubes false at the most of them join the set: at least 16, deduped against the round's diagrams.
  - The places come from the round's cost a cube goal, 64 at least, 256 at most.
  - The caller's proof ends 2 s before the stage's end.
- **On wo:**
  - 13–17 relevant cubes join a round: 64 → 77–81 → 88.
  - The IC3 loop runs: diagrams, then the ∃ law, then the relevant cubes.
  - At round 2 (60 s) or 3 (120 s), the caller's law fails with no diagram: its proof or model doesn't come back within its window.
  - Unknown at 60 and 120 s.
- **The overrun:** one 60 s run ended at 68 s. The caller's goal began at 31 s and returned at 61 s, past the stage's end, with its window ending before that. The overrun is inside one decideLaw or proveLaw call on the caller's goal with 75 cubes.
- **Verdicts (p25):** the six proven (sync 8–9 s, async 23–25, decentralized 27–34, 2PC 19–21, ticket 25–34, toy 15–22); the four unknown.

**wo's set at the caller's failure** (`runs/engine/wo10`):
- At round 2 the set has 79 cubes, and the caller's counterexamples so far are one, round 0's.
- "a counted vote was sent" (`VoteMsg[x,y] = 0 ∧ Votes[y,x]`) and "a leader has the voting quorum's votes" (`Leader[x] ∧ VQ[y] ∧ Votes[x,y] = 0`):
  - both are enumerated (wo's enumeration holds 262 cubes);
  - neither is in the set;
  - neither scores: no cube outside the set is false at the one counterexample.
  - Later rounds' caller goals return no model within their window, so relevance has nothing to rank by.
- **Fix:** every cube of at most two literals goes first (DuoAI's minimal clauses: 24 of wo's 262), the turns after. "a counted vote was sent" is now in the set.
- **Still out:** "a leader has the voting quorum's votes" (three literals, among 238). It waits for the caller's models (epr6), whose states would rank it.
- **Pilot (p26):** wo unknown at 57 s (2 runs, inside the wall); the six proven once each (sync 8 s, async 25, decentralized 25, 2PC 18, ticket 40, toy 26).

**After gen/epr6** (merged at e47121a; `runs/engine/e6b`, `p27`):
- **distributed_lock:**
  - Round 0 decides all 49 cubes, with 17 unsure (models not confirmed, no diagram) and 3 diagrams.
  - Rounds 1 and 2 take under a second, settled by their cores.
  - The search's own end (about 45 s in, after proveRule's earlier work) comes before the set's proof.
  - The join takes the search's first 25–30 s.
  - Unknown, 43–53 s.
- **ring:** round 0 ends at 8 s with 4 diagrams. Round 1 has 13 unsure among 81 and runs to 59 s. Unknown.
- **wo:**
  - At 60 s: the ∃ law, then the caller's law fails with no diagram at round 2, 42–58 s.
  - At 120 s: five rounds; the set reaches 95 cubes; the caller's law fails with no diagram at 103 s.
  - Unknown, inside the wall at 55–64 s (one run 4 s over).
- **The six (2 runs):** sync 9–10 s, async 24–27, decentralized 36–41 (it was 19–34), 2PC 18, ticket 34–37, toy 21–22.

**Decentralized's margin, and the two fixes weighed** (`runs/engine/p28`, all ten, 2 runs):
- **Decentralized:**
  - Its engine pass (whose caller's law fails; the sums pass proves it) had grown from 12 s to 19–23 s after epr6.
  - The time was the caller's goal: the EPR path ran out of its window, then the CDCL search and the proof path ran after it.
  - Now the proof path is skipped where the EPR path ran out of time on the caller's goal. Decentralized takes 28–29 s.
- **Whole-state lookup (fix 1):**
  - A model's state over at most the widest view's keys is a row of that view. "Every row reached in every view" then includes that row, so the lookup among canonical small states gives what diagrams() gives (up to the cells the model leaves unnamed).
  - A state over more elements than the widest view also has more than the small instance's sorts hold, so it can't be looked up either: unsure both ways.
  - So the 17 unsure on distributed and 13–17 on ring are models over at most the view's keys. Their states are rows of reachable small states, but the interpreter's step from them doesn't confirm the model's step: the model's unnamed cells differ from the small state's.
  - Dropping those cubes was measured before, and it lost the caller's law. Not built.
- **Proofs reused (fix 2):** distributed doesn't reach the set's proof. Round 2 (37 cubes, nothing dropped) begins at 44–51 s, past the search's end. The search starts about 15 s in, after proveRule's own work, and its join takes about 25 s. The final proof isn't what it waits on. Also, decideLaw's answers carry no trees to assemble. Not built.
- **Verdicts:**
  - The six proven: sync 9–10 s, async 25–26, decentralized 28–29, 2PC 18, ticket 29–34, toy 17–21.
  - The four unknown: wo 59–61, distributed 52–61, ring 60, sharded 27–32.

**Optimistic Houdini, the profile, wo's listing** (`runs/engine/p29`, `p30`):
- **Optimistic Houdini:**
  - An unsure cube holds at every small state and every step from one: the cubes are read off the small instance's rows, and its steps stay inside it. So the concrete test always passes, and the cube is kept and not asked again.
  - The set's proof decides. A cube it fails at is dropped, and the rounds go on.
  - distributed now reaches the set's proof (52 cubes). It fails in 5 ms at a cube, which is dropped, and the next round is cut at 59 s. Unknown.
- **Profile:**
  - Before the search, proveRule's work takes 1.9–3.8 s (`preprobe.ts`: distributed 3.8, wo 3.7, 2PC 1.9, decentralized 1.9). Not 15 s.
  - On distributed, the join ends near 10 s and the selection at 16 s.
  - Round 0 (49 cubes and the caller's goal) takes 22 s and round 1 18 s: about 0.45 s a goal, where epr6's fixtures decide in 0.13 s.
  - On ring, round 1 (81 cubes) takes 51 s.
  - The rounds' goals are where the time goes, not the join or the start.
- **wo's listing:**
  - At the caller's failure the set holds "a counted vote was sent".
  - "a leader has the voting quorum's votes" is still out, scoring 0 against the 2 caller counterexamples: neither violates it.
- **Verdicts (p29):**
  - The six proven: sync 10 s, async 24–28, decentralized 24–35, 2PC 18–19, ticket 34–40, toy 16–22.
  - The four unknown: wo 63–64, distributed 63, ring 60, sharded 26.
- **GDP_ENGINE_LIST** (the listing at the caller's failure) is in: it comes out before a merge.

**The set's proof drop loop, proofs that stand, the per-goal cost** (`runs/engine/p31`–`p34`):
- **Drop loop:**
  - When the set's proof fails at a cube, the cube is dropped and the proof asked again at once, up to 24 times.
  - On distributed it drops 13 cubes in 2–63 ms each. Three fail at the start: order literals over epochs past the small instance's 0..3. Ten fail at a step.
  - Then the caller's law fails (1.6 s), and the rounds go on.
- **Proofs that stand:** a goal proven since the set last lost a law isn't asked again (a set that only grows keeps its proofs). On distributed, round 1 now takes 3 s, from 15 s.
- **Per-goal cost:** the round's machine and indices are built once a round now. The time measured was the EPR decision itself: on distributed, decideLaw took 25 s of round 0's 25 s (49 cubes and the caller's goal, about 0.5 s a goal). On ring, 14 s of decision and 36 s of the CDCL path for the cubes it leaves undecided.
- **The sums pass's reserve:** 10 s, or a quarter of what is left (it was 21 s or a third). Decentralized's sums pass, which proves it, takes about 3 s.
- **distributed now:**
  - After the drop loop, rounds 2 and 3 run to 49–52 s.
  - In one run the caller's law fails with no diagram at round 3; in the other, round 3 is cut by the end.
  - Unknown, 57–60 s.
- **The six (p34, 2 runs):** sync 8–11 s, async 16–27, decentralized 28, 2PC 18–20, ticket 31–35, toy 21.

**Next steps, in order:**
1. Start the stage earlier, with a planned share of the budget, not what's left after the join and the deep runs (distributed_lock's round 1 is cut short).
2. Carry the model's function values into the judged state (ring): `stateOf`/`realCti` read `idn[...]` cells of the witness into the interpreter's view of `idn`, or judge rows with the model's values.
3. Wider patterns for wo: views of four nodes, or a diagram across views (the conjunction of rows of several views over shared keys).
4. Rename sharded KV's model keys onto the small instance's (the model's distinct key parts mapped to 0..k−1, per sort) before judging and taking diagrams.
5. The four-literal ranking for ring (ring's btw cubes must survive the 32 cap).
6. Merge gen/epr4 (the kernel's wall-clock fixes) when it lands.
7. Re-run all ten, 2 runs at 60 s (`research/protocols/enum/jobs-pilot60.json`, adapted to 90 s caps), then the quick bar against 5d4da3f's cached baseline (`bun gates/bar.ts --base 5d4da3f --quick --only chc,rw`, never `--together`).

**Rules:** local probes ≤ 30 s, one at a time; Modal job caps of about 60 s budget + 30 s, killed in the container; 2 runs a config; about $25 for this round (spent about $0.1 billed by 15:00 UTC).
