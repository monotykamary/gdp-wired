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
  - wo: the 3-node view (71 literals) holds the whole counterexample row, 24 literals over the cells the model names. That full row is a row of a reachable small state (3 nodes). The 4-node and 5-node views come out the same way.
  - sharded: the same at its widest view (5 keys, 21 literals). Down to one literal, every generalization is reached.
  - So the two counterexamples' states agree with a reachable small state on every tuple a view of ≤ 5 keys covers. A wider view needs a small instance at least that wide: the 4-node wo BFS, past 3 nodes' 1,400–3,250 states in 30 s, is out of reach. Ivy's wo invariant also needs an ∃ (a leader has a quorum that voted for it), which the ∀ cubes can't say.
- **Overrun left:** sharded ends at 77 s. Its search ends near 59 s; the rest is after it, in core/dsl.ts's deeper bounded runs (`withWall(Infinity, …)`), which is outside core/infer.ts.

**Next steps, in order:**
1. Start the stage earlier, with a planned share of the budget, not what's left after the join and the deep runs (distributed_lock's round 1 is cut short).
2. Carry the model's function values into the judged state (ring): `stateOf`/`realCti` read `idn[...]` cells of the witness into the interpreter's view of `idn`, or judge rows with the model's values.
3. Wider patterns for wo: views of four nodes, or a diagram across views (the conjunction of rows of several views over shared keys).
4. Rename sharded KV's model keys onto the small instance's (the model's distinct key parts mapped to 0..k−1, per sort) before judging and taking diagrams.
5. The four-literal ranking for ring (ring's btw cubes must survive the 32 cap).
6. Merge gen/epr4 (the kernel's wall-clock fixes) when it lands.
7. Re-run all ten, 2 runs at 60 s (`research/protocols/enum/jobs-pilot60.json`, adapted to 90 s caps), then the quick bar against 5d4da3f's cached baseline (`bun gates/bar.ts --base 5d4da3f --quick --only chc,rw`, never `--together`).

**Rules:** local probes ≤ 30 s, one at a time; Modal job caps of about 60 s budget + 30 s, killed in the container; 2 runs a config; about $25 for this round (spent about $0.1 billed by 15:00 UTC).
