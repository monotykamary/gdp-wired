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
