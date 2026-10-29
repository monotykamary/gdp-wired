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
