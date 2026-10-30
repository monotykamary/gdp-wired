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

## Banked: the data filter and minimal implication ahead of the rounds, by default (gen/pool e353d4e; 8 of 10)

**What changed** (core/infer.ts; `GDP_POOL=0` turns it off)
- **The data filter runs on every enumeration.** It grows every sort by one, then each sort alone where there are
  several.
- **Its budget is its own:** at most 3 s and at most a tenth of what is left. Each instance gets half of its share for
  its BFS, uncut; the rest goes to reading the instance's states against the cubes.
- **Then minimal implication.** The rounds' `made` (round 0, blockers, relevance, the pool Houdini) is the filtered,
  minimal pool.
- **Taken out:** the top-down phase, the cone, `GDP_POOL_*`'s diagnostics, and decideLaw's `uses` (kernel/prove.ts is as
  at ff60d1c). They are kept at db6c00f, where exp/pool-z3 starts.

**All ten, twice at 60 s** (`runs/engine/pd2`, Modal 2 CPU; search ms; before is f9 and q15 at gen/enum4)

| protocol | run 1 | run 2 | before | filter (made → left, states, ms) |
|---|---|---|---|---|
| sync | proven 8.9 s | proven 10.0 s | 8–10 s | (no engine) |
| async | proven 22.7 s | proven 24.4 s | 24–25 s | (no engine) |
| decentralized | proven 20.4 s | proven 16.7 s | 13–32 s | 17 → 17, 88 states, 47–58 ms |
| 2PC | proven 18.7 s | proven 21.1 s | 18–20 s | (no engine) |
| ticket | proven 30.8 s | proven 41.0 s | 25–45 s | (no engine) |
| toy | proven 11.4 s | proven 14.9 s | 10–18 s | 10 → 10, 95 states, 0.3–0.5 s |
| sharded | proven 27.1 s | proven 32.1 s | 25–44 s | 17 → 17, 150 states, 1.7 s |
| **distributed** | **proven 35.5 s** | **proven 32.3 s** | unknown 63–65 s | 176 → 75, about 600 states, 1.3–1.5 s |
| ring | unknown 60.0 s | unknown 59.8 s | unknown 60 s | 145 → 94, 217–237 states, 3.0 s (the cap) |
| wo | unknown 69.0 s | unknown 65.5 s | unknown 63–68 s | 239 → 99, 412–442 states, 2.0–2.1 s |

- **The seven stay proven** in both runs. Every time is within the spread recorded before.
- **Distributed is proven in both runs** (and in pd1, the pilot).
- **The filter can't push a run past the wall.** It costs at most its cap (ring 3.0 s, wo 2.1 s), which is a tenth of
  what is left.
- **wo's overrun (65–69 s)** is the EPR side's, recorded under f5 (64–66 s there).
- **At 3 s, ring's filter leaves 94 cubes,** against 64 at 4 s an instance (pl4). Ring isn't proven either way.

**The corpus** (`bun gates/bar.ts --quick --cand gen/pool --base 5d4da3f --only rw`, against the cached baseline
5d4da3f49013-modal-r1; <main>/runs/bar/runs/pool-e353d4e-quick-rw/REPORT.md)
- 74 proven, 14 refuted, 3 unknown on the 91-task dev set, as the base's three runs.
- Gained 0, lost 0, wrong 0; predicted full-set delta 0.
- Wall 208 s, estimated $0.05.
- core/ and kernel/: 2,791,002 bytes against 2,672,441 (+118,561 since 5d4da3f).

## The shrunk pool with Z3 as the oracle (exp/pool-z3: db6c00f plus exp/z3's 4689c8f and 10f5aba code; not for merging)

**The test:** this branch's filtered, minimal pool (`GDP_POOL=ic3`, GROW 1, 2–4 s an instance) and exp/z3's oracle
(`GDP_Z3=td` or `ic3`), on ring and wo.
- `GDP_POOL_CMP` asks every top-down goal again with decideLaw (1 s) and prints each disagreement.
- Runs: `runs/engine/pz1`, `pz2` in ../gdp-wired-poolz3, Modal 2 CPU, one run each.

**The verdicts: still unknown, both protocols, both modes**

| run | pool | what happened | verdict |
|---|---|---|---|
| ring, Z3 top-down, 60 s (pz1) | 44 | round 0: 0 dropped, 15 unknown at 1 s, 20 s; the caller is proven; `prove()` of the 44 fails at the caller's start (16 s) | unknown, 59.7 s |
| ring, Z3 top-down, 300 s (pz2) | 44 | the same fixpoint; `prove()` at 44, 43, 42 cubes: 47 s, 28 s, 131 s, each failing (at two Leader/Pending cubes, then at a kind law's start) | unknown, 300 s |
| ring, Z3 IC3, 60 s (pz2) | 44 | **all 5 probe-proven cubes in the set** by round 4 (30 cubes); Z3's set check unknown at a 3-key cube; the pool Houdini's proofs (3.2 s, 10.1 s) fail at junk | unknown, 60.0 s |
| wo, Z3 top-down, 60 s (pz2) | 92 | rounds drop 31, 3, 0 (0 unknown; 15.5, 3.9, 2.6 s); fixpoint 58; "a leader has the voting quorum's votes" dropped; caller not proven | unknown, 64.1 s |
| wo, Z3 top-down, 300 s, with the comparison (pz2) | 83 | 23, 4, 1, 0 dropped; fixpoint 55; caller not proven | unknown, 303 s |
| wo, deep filter (GROW 3, 20 s an instance), 400 s (pz2) | 49 | 9 dropped, then none (3.0, 1.4 s); fixpoint 40 with all 5 picks; caller not proven; the IC3 rounds after it grow to 159 cubes | unknown, 404 s |
| wo, Z3 IC3, 60 s (pz2) | (filtered) | **all 5 picks in the set** (77 cubes) with the ∃ ghost; Z3's set check: a model of "one leader @step" (it leaves the ∃ law out); the kernel's proof fails at the ∃ law's goal | unknown, 64.1 s |

So the precondition for the record ("if they prove") is not met. The comparison was made anyway; it is what the
next oracle must decide.

**What Z3 decides that decideLaw leaves undecided** (top-down round goals, every cube's step with the whole pool
assumed, each asked by both)

| protocol, round | goals | both decide, agree | Z3 only | decideLaw only | neither | decideLaw's time when undecided |
|---|---|---|---|---|---|---|
| ring, round 0 | 44 | 1 | **28** (all proofs) | 0 | 15 | 1,000–1,140 ms: every one at its 1 s cap |
| wo, rounds 0–3 | 83, 60, 56, 55 | 0 | **all** (round 0: 60 proofs, 23 models) | 0 | 0 | 237–1,263 ms (median 1,003): gives up early or at the cap, on every goal |

No goal was decided differently by the two (0 "differ").

**What kind each is**
- **wo: request-carried sets with ∀ flags, on every goal.**
  - The step reads a carried set Q, the request's quorum: `.carries('Q')`, with ∀k. Q[k] ≤ 1 in the assumption.
  - Two ∀-quantified flags read it: `quorumVotes` and `votingQuorumVotes` (∀k. Q has k → Votes[src, k]).
  - VotingQuorum is written at every key from Q.
  - decideLaw decides none of wo's goals, the trivial ones included: "Leader ∧ started is 0" and "Voted is 0 ∧ VoteMsg
    at x, x" are undecided in 0.25–1.2 s. So the cube isn't what blocks it; the step's shape is (a carried set under a ∀
    flag, a write at every key).
  - Z3 decides all 254 at 61 ms mean.
- **ring: an injective function inside composed keys, an ordered sort, and a successor that wraps at a param.**
  - Each of the 28 Z3-only goals reads `idn`, known only by its fact (injective), at a composed key: Pending[64·idn(x) +
    y]. Or it orders node keys (x + 1 ≤ y ≤ z: the between turns), or both.
  - The step's `next` is n + 1, else 0 at n + 1 = size: an ordered-sort successor that wraps at a parameter.
  - decideLaw's EPR rounds run to the 1 s cap on all of them. Z3 (ordered sorts as a total order with ground
    successors, radix keys as digits) proves them in 0.27 s mean.
  - 15 goals are undecided by both at 1 s: the 3- and 4-key Pending/idn cubes.
- **∀∃: wo's "the voting quorum has a member after init",** with its ghost witness.
  - Neither oracle takes it. decideLaw's fast shape refuses "there exists". Z3's translator leaves ∃ goals and ∃ laws
    to the kernel, so its set check finds a model of "one leader" without it.
  - It is the law the caller's proof needs, and the one goal the IC3 run's kernel proof fails at.

**What that says**
- **The shrunk pool plus Z3 puts every target in the set:** ring in IC3, 5 of 5; wo in IC3 and in the deep top-down, 5
  of 5. So the pool and the oracle together fix the navigation.
- **What's left on each:**
  - **ring:** the final proof of a 30–44-cube set (3–131 s, failing at junk that Z3 couldn't decide at 1 s). The cone
    cut that proved distributed isn't in exp/z3's top-down; it needs Z3's proofs' cores, which Z3 doesn't return here.
  - **wo:** the ∀∃ law, which no oracle decides. The caller's proof goes through the kernel's ∃ path (core/exists.ts)
    alone.
- **What our own procedure must decide** (not built this round):
  1. steps that read a request-carried set under ∀-quantified flags, and write a map at every key (wo: every goal);
  2. an injective function's values inside composed keys, with ordered sorts and a successor that wraps at a
     parameter (ring: 28 goals at 1 s);
  3. ∀∃ laws with a ghost witness: Z3 doesn't take them either, so this one is ours alone.
  - And, besides the oracle: unsat cores from the oracle, so the fixpoint can be cut to its cone before `prove()`.

**Verified and not**
- **Verified:** the verdicts and counts above, one run each (Modal).
- **Not verified:**
  - second runs;
  - Z3's models and proofs on these goals: untrusted, and no verdict here rests on them;
  - whether the 15 goals neither decides at 1 s are decidable with more time.
- **Spend for both parts:** $0.24 of Modal billed so far for this session's 15 apps (the 06:00 UTC hour is still being
  billed); about $0.35 in all, against $3.

## The pool: data filter, minimal implication, top-down, cone (gen/pool from gen/enum4 ff60d1c; the hypothesis holds for distributed only)

**The hypothesis tested:** DuoAI's pool is small because junk is killed by data before any solver call, and ours isn't:
- (a) cubes true in our small instances but false at larger instances' reachable states;
- (b) cubes implied by other cubes (DuoAI's minimal-implication pruning);
- (c) the fixpoint, before the kernel's final `prove()`, cut to the caller's cone.

The oracle stays decideLaw throughout. The Z3 section ("Z3 as the oracle") is on exp/z3, not on this branch.

**What was built** (core/infer.ts, every piece behind `GDP_POOL`, off by default; kernel/prove.ts: one untrusted field)
- **The small instance as a function** (`instance(grow, share, rnd)`): the BFS of before, with `grow` more elements of a
  sort (an ordered sort 0..3+g), its own draws (a separate seeded generator, so the engine's own draws are unchanged), up
  to 8 param vectors, 16,384 input combinations a state, 2,000,000 states, no "won't finish" cut, and its queue read by
  index (it was `shift()`). The base call is the instance of before, unchanged (pl7 below).
- **The data filter** (`dataFilter`, in `enumerated()`): for g = 1 .. `GDP_POOL_GROW`, each sort +g alone, then every
  sort +g. Each instance gets `GDP_POOL_MS` for its BFS and as much again to read it. A cube is dropped when some row of a
  reached state lies in it (every row: a view's `rowsOf(…, full)` lifts the row cap; literals read by `valueOf` alone).
  `GDP_POOL_PICKS` names the probe-proven cubes; every drop of one is printed with its state.
- **Minimal implication** (`minimal`): cube B goes when a kept cube A's law implies B's. The test sends A's keys into B's,
  one to one within each sort, and needs each literal of A entailed by one of B's: the same literal, the same sum at a
  bound no larger, or a value at least A's bound. The cubes are taken fewest literals first. A dropped cube remembers its
  kept impliers (co-implication).
- **`decideLaw` returns its proof's support** (`uses`: the laws its goals' proofs read, from `settled`'s memo). It is
  untrusted, as before; `prove()` still makes the verdict.
- **`GDP_POOL=td`** (before the rounds): the pool is the filtered minimal cubes not given, not implied by the caller's
  laws and not false at a start.
  - **Houdini:** every cube's goal is asked with all the others assumed (`GDP_POOL_Q`, 1 s each), and every one with a
    model is dropped at once. An undecided cube is kept. A cube that a dropped one implied comes back where nothing kept
    implies it.
  - **The caller's goals from the fixpoint,** with the first ∀∃ ghost where they fail.
  - **The cone:** the caller's support, closed under each cube's own. A cube whose support is unknown is asked again
    with the cone alone assumed. A proof adds its support; a model's pre-state brings in the fixpoint's cubes false there.
  - **`prove()` of the cone,** a cube it fails at dropped. `GDP_POOL_HOUDINI=0` skips Houdini; `GDP_POOL_CONE=0` proves
    the whole fixpoint.
- **`GDP_POOL=ic3`:** the existing rounds with `made` = the filtered minimal pool.

**Step 1, the data filter** (`runs/engine/pl2`: 30 s per instance, g up to 3, Modal 2 CPU; wo again at 20 s in `pl4`)

| protocol (sorts) | made | instance: states (BFS), BFS ms → cubes left | probe-proven kept |
|---|---|---|---|
| distributed (lo nodes 2, hi epochs ordered) | 176 | lo+1: 102, 92 ms → 176; **hi+1: 168, 76 ms → 75**; all+1: 498, 0.5 s → 75; lo+2, hi+2, lo+3, hi+3 (144–1,068 states, ≤ 0.8 s) → 75; all+2, all+3: 4,360, 4,473, cut at 30 s → 75 | 12 of 12 |
| ring (lo nodes ordered, hi ids ordered) | 145 | **lo+1 (5 nodes): 1,180 (421), 8.7 s → 64**; hi+1: 388, 1.4 s → 64; all+1: 1,180 → 64; lo+2: 2,651, 30 s → 64; hi+2, all+2, +3 (cut) → 64 | 5 of 5 |
| wo (nodes) | 251 | +1: 1,590 (1,096), cut at 30 s → 108; all+1: 1,718 → 87; +2: 3,005 → 78, 2,834 → 75; +3: 4,352 → 73, 4,529 → 73 (every BFS cut) | 5 of 5 (pl4: 228 → 95, 80, 68, 68, 63, 58) |

- **No probe-proven cube died** on any instance, in any run.
- **wo's picks** are written here: research/protocols/engine/picks/consensus_wo_decide.txt holds the five ∀ written laws
  in the enumeration's text.
- **One more element is enough** where the BFS finishes:
  - distributed: 101 of 176 die at one more epoch, and nothing more dies to +3;
  - ring: 81 of 145 die at a fifth node.
- **wo keeps shrinking with depth,** and its instances never finish. So "true in every reached state" is weaker there,
  and some of its 58–73 may still be false.
- **The BFS is the cost only on wo.** Each state's successors are 16,384 input combinations, so 189–3,618 states take
  5–30 s.
  - The work is data-parallel: successors of different states, and over different inputs, are independent. Only the
    seen-set is shared, and it can be partitioned by hash.
  - Reading the states against the cubes is independent per state too. Ring's reading hit its own budget at 4 s (321–440
    of 712–852 states).
  - A GPU version through research/hw is the later option; not this round.
- **In the engine** (GROW 1, 4–5 s an instance; pl3–pl6):
  - distributed's filter takes about 1 s;
  - ring's and wo's take 10–12 s, which leaves the engine 34–37 s on Modal.

**Step 2, minimal implication** (pl3–pl6)

| protocol | after the filter | minimal | implied | then not given, not implied by the caller, not false at a start |
|---|---|---|---|---|
| distributed | 75 | 60 | 15 | 52 (4.5–5.0 s: `implied` and `atStart` are a solver query each) |
| ring | 64 | 44 | 20 | 42 (0.7–0.8 s) |
| wo | 105 / 96 / 58 | 105 / 96 / 58 | 0 | 104 / 95 / 57 |

Every probe-proven cube is among the minimal ones.

**Steps 3 and 4: top-down with decideLaw, then the cone** (Modal 2 CPU, `--ms 60000` unless said; search ms is run.ts's)

| protocol | Houdini (decideLaw, 1 s a goal) | caller | cone → `prove()` | verdict |
|---|---|---|---|---|
| distributed (pl3) | round 0: 52 cubes, 2 dropped, 0 undecided, 15.9 s; round 1: 50, none, 1.6 s | proven | 26 of 50 → proven in 4.6 s | **proven, 49.5 s** (td at 44.5 s on the wall) |
| distributed (pl6 r2) | round 0: 52, none dropped, 14.4 s | proven | 27 of 52 (11 of the 12 picks in it) → proven in 4.5 s | **proven, 43.8 s** |
| ring (pl4) | round 0: 42, 0 dropped, **36 undecided**, 35.3 s | out of time | | unknown, 59.6 s |
| ring, 250 ms a goal (pl6) | round 0: 42, **42 undecided**, 13.8 s | proven | 15 (2 of 5 picks, all undecided) → `prove()` 12.7 s, fails at the wall | unknown, 59.1 s |
| ring, Houdini skipped (pl5) | | proven from the 42 | cone 6 → 15 → 15 → 27 → 28 by blockers, its goals mostly undecided | unknown, 59.0 s |
| wo, +1 (pl4) | round 0: 104, **104 undecided**, 19.3 s | out of time | | unknown, 63.5 s |
| wo, +3, `--ms 400000` (pl4) | round 0: 57, **57 undecided**, 44.0 s | not proven | | unknown |
| wo, Houdini skipped (pl5–6) | | "one leader" has a model from the 95; with the ghost ("some VotingQuorum member"), the ghost's goal is undecided | | unknown, 59.7 s |

**The IC3 rounds over the filtered minimal pool** (`GDP_POOL=ic3`)

| protocol | rounds | verdict |
|---|---|---|
| distributed (pl6, pl7) | rounds 0–3 at 14, 19, 23, 27 cubes, all over by 21 s | **proven, 32.1 s and 30.6 s** |
| ring (pl6) | round 1 has 7 unsure; the pool Houdini at 29 cubes fails in 12.4 s | unknown, 59.8 s |
| wo (pl6) | | unknown, 62.5 s |

Without the filter, the same rounds leave distributed unknown at 63–65 s (f9, q15; pl7 below).

**The default path is unchanged** (pl7, all ten, GDP_POOL unset, one run): sync, async, decentralized, 2PC, ticket, toy
and sharded are proven; distributed (64.8 s), ring (60.0 s) and wo (64.2 s) stay unknown.

**Verdict on the hypothesis**
- **Distributed: it holds.**
  - Data from one more epoch kills 101 of the 176 cubes before any solver call. Minimal implication takes 15 more.
  - The rest proves inside 60 s two ways: top-down plus the cone (43.8–49.5 s), and the existing IC3 rounds (30.6–32.1
    s).
  - The three costs named under Z3 all fall:
    - one Houdini round is 14–16 s at 52 laws (was 39–71 s at 140–176 with Z3);
    - the rounds choose the missing cubes, because junk no longer outranks them;
    - the cone is 26–27 cubes, and its `prove()` is 4.5 s (was 43–89 s or unfinished at about 140).
- **Ring and wo: the pool shrinks with every target kept, and the frontier doesn't move.**
  - ring: 145 → 42; wo: 251 → 57–104.
  - What's left in the way is decideLaw's decisiveness, not the pool. At 42–104 assumed laws it leaves 86–100% of the
    cube goals undecided (ring 36 of 42 at 1 s, 42 of 42 at 250 ms; wo 104 of 104 and 57 of 57).
  - So Houdini can't drop and the cone can't be closed.
  - Z3 decided those goals on exp/z3 (wo 0 undecided), but with the unfiltered pools.
- **The hypothesis is confirmed as the cause of distributed's gap, and refuted as the whole gap.** Ring and wo need both:
  the small pool from here and an oracle that decides at about 40–100 laws.

**Not wired in at db6c00f.** The condition was all three inside 60 s, and one of the three was. The filter and the
minimal cut were then banked ahead of the IC3 rounds at the coordinator's request: see "Banked" above.

**The exact next step**
- **This branch's pool with exp/z3's oracle,** top-down and IC3: ring 42 and wo 57–104 cubes, where Z3 decided every
  goal at 0.1–0.4 s.
- **If that proves them,** wire in the filter (GROW 1, about 1–12 s) and the minimal cut ahead of the rounds:
  - `GDP_POOL=ic3` is the smaller change; it proved distributed fastest;
  - top-down plus the cone as the alternative.
- **For wo,** a deeper filter needs a faster BFS first (its instances never finish), and the ∃ ghost's goal needs a
  decision.

**Verified and not**
- **Verified** (Modal, `runs/engine/pl1`–`pl7`):
  - every table above, one or two runs each as listed;
  - no probe-proven cube dropped by the filter or the minimal cut;
  - distributed proven by top-down plus the cone twice and by the filtered IC3 rounds twice;
  - the default path's ten verdicts once (seven proven).
- **Not verified:**
  - **whether wo's survivors are all true:** its BFS never finished;
  - **the "two runs a config" rule:** ring's and wo's variants ran once each;
  - **the six's times and the corpus:** not measured with GDP_POOL on, since nothing is wired in;
  - **the implication test's soundness:** only by construction (literal entailment under a sort-preserving injection).
    A wrong drop would only have shrunk the pool, and `prove()` decides.
- **The diagnostics** (`POOL` lines on stderr, `GDP_POOL_LIST`, `GDP_POOL_PICKS`) are in the code behind GDP_POOL. Take
  them out before any merge.
- **Spend:** $0.09 of Modal billed for this round's apps so far. The current hour is still being billed; about $0.15 in
  all, against $3.

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

**The leave-one-out probe** (`looprobe.ts`; the picks by a temporary hook, at 2bd8806 plus the probe)
- **ring:** all three written laws are essential. All are in the space: the leader law, the own-id law, the three between turns.
  - **No shape is missing.** Those 5 cubes prove the caller by the usual proof (0.6 s), but `proveSetFast` reports a spurious model at the own-id law's step, on the EPR side.
  - **Guard:** the set-proof loop asks the usual proof where the fast one fails at a cube the rounds proved from that same set.
- **distributed:** essential are the 7 written laws other than "two holders are one" and "a locked epoch at a node's epoch is its own".
  - **12 enumerated cubes prove the caller** (0.8 s, fast): the 11 forms of the essential laws and "two transfers are never at one epoch", which covers the "two live transfers" case at one epoch (the 4-key form has z ≠ w).
  - **No shape is missing either,** once the one-sided cut is narrowed. It had struck "started is 0 and y + 1 <= Ep[x]", the only form of "Ep is 0 before init" (Ep has an `is 0` literal only). A key bounded from above alone is 0 there, and the cube a true one; the cut now strikes only keys bounded from below.
  - **The gap is navigation:** 7 of the 12 are minimal and in round 0; the 3- and 4-literal five must come as blockers, and don't.
- **The frames' fixpoint** grows by relevance while there is time (a demoted cube's model is a counterexample state). distributed and ring now end early, at 35–46 s, with nothing relevant left: the five never rank.
- **wo's overrun:**
  - **mine, fixed:** the engine's CDCL searches had a counted budget alone, which runs on past the wall (6 s of samples past 59 s in `growCdcl`, `pastwall.py` on bun's CPU profile); they now carry the engine's wall.
  - **what is left is the EPR side:** proveLaw's EPR-first `settle` → `epr.ts` `decide`, about 3.4 s of samples past 59 s. wo ends at 64–66 s (was 68).
- **The real-world corpus** (`bun gates/bar.ts --only rw`, f483a48 against 5d4da3f): 318/361 as the base, 0 gained, 0 lost, wrong 0. No piece since 3d5668a (two of a pattern, frames, the chains and tables, the one-sided cut) moves a corpus law. Not yet measured: how many of the 8 unknown corpus laws reach the engine at all.
- **Verdicts** (`f5`, 2 runs): sync 8 s, async 23–29, decentralized 13–16, 2PC 15–23, ticket 30, toy 15–16, sharded 30–32, proven; distributed 44–46, ring 35–44, wo 65–66, unknown.

**Checkpoint (verified: `runs/engine/f7`, all ten, 2 runs at 60 s, no 'join failed')**
- **The corpus's 8 unknown laws reach no engine** (`rw1`, `rw2`: no engine event in any). What keeps each out of the gate:
  - gitea's "two counted approvals are never by the same reviewer": only the counter `next` (6 values; keyed maps and a keyed caller's law both there);
  - tigerbeetle ×4: a counter `commit`, and caller laws not over keys;
  - medusa: amounts and sums, no keyed caller's law;
  - opossum and bullmq: no keyed maps.
  So the protocol work can't move the corpus by construction, except gitea's law if the gate let a counter through (leaving it out of the views).
- **A bug in the frames, fixed:** a cube could be both pending and in the set (a diagram or a promotion), so a push's law list held it twice. kernel's "laws and facts declares X twice" threw, and the engine with it ('join failed'): that, not the frames' fixpoint, was distributed's and ring's early end at 35–46 s. A cube in the set is now never pending, texts are once, and the set-proof loop's blockers skip pending and dead cubes.
- **A failed push's counterexample is blocked as an obligation** (IC3's): by the enumeration's cubes false at its state, so the next push has what it lacked.
- **Verdicts** (`f7`): sync 8–9 s, async 23–27, decentralized 14–15, 2PC 18–21, ticket 25–33, toy 12–16, sharded 29–36, proven. distributed 63, ring 60, wo 65–66, unknown; all use their full time now.
- **The exact next step:** find why distributed's probe-proven five (3–4 literals: a live transfer above every epoch; Held[x] ∧ Transfer[y, x] ∧ Ep[x] + 1 <= y; Held[x] ∧ Transfer[z, y] ∧ Ep[y] + 1 <= z; the two "two live transfers" forms) never enter the set.
  - **How:** a status at the engine's end of each picked cube (`research/protocols/engine` picks in the scratchpad's form: one cube text a line; the hook was never committed; rebuild it from this note) — not made, in the set, pending, dead (start check) or never chosen.
  - **If "never chosen":** rank blockers by the push's counterexamples (the demoted written laws' states) above the rest.
  - **If "dead":** the start check (`atStart`, a 250 ms CDCL model judged by the interpreter) is wrong on it.
  - **ring:** the same check with its 5 (`ring-pick`: leader, own-id, three between turns), then the guard on the fast proof (the usual proof where it contradicts the rounds).

**Since ff399ff** (`runs/engine/st1`–`st7`, `f8`, `g1`–`g3`; the typecheck now in the Modal batches, since the laptop's load forbade local runs)
- **Where the probe-proven cubes end** (an end-of-engine status hook, taken out):
  - distributed: 10 of 12 in the set; never chosen are "Held[x] ∧ Transfer[z, y] ∧ Ep[y] + 1 <= z" and the same-node "two live transfers".
  - ring: the own-id law in the set, the leader law pending, the three between turns never chosen.
- **Why never chosen** (each blocker call's ranking, marked):
  - distributed's needed blockers are usually among the candidates, at ranks 1–31 (often 2–4), and only the top two were taken. Now four: a different pair then enters (Held ∧ Transfer[z, y] in; a live transfer above every epoch and the same-node two-live-transfers out).
  - ring's between turns only ever *may* fail at a counterexample (cells unnamed), ranked about 53rd behind fewer-literal cubes of the same score, and are no candidate at most counterexamples.
- **A pool Houdini** (DuoAI's fixpoint of the relevant candidates): every cube ranked in a counterexample's top eight joins a pool. Once, when 40% of the engine's time is left (at a round's start, ahead of its early returns), one Houdini runs over the set, the pending cubes and the pool, the usual proof deciding where the fast one blames a kind's law or a cube the rounds proved.
  - distributed: the pool is 73–78 cubes, each fast set proof 1.6–10 s, out of time before it closes.
  - ring: its first call takes what is left.
  - Cheap re-proofs after a drop (proveSetFast's kept decisions, at this size) are the EPR side's.
- **Verified** (`f8`, b91d305's code before the status hook came out; one run each): the seven proven (sync 9 s, async 26, decentralized 13, 2PC 18, ticket 36, toy 14, sharded 31); distributed, ring, wo unknown; the pool Houdini fired only on distributed.
- **The gitea near-miss** (`g1`–`g3`, and tmp/few8w at 05ac413, not for merge):
  - a `few` limit of 6 or 8 alone doesn't bring it in: the join has spent the cost clock (22 s over), and the engine's entry checks `now() < until`;
  - with the limit at 8 and the entry on the wall, it reaches the engine (a small instance of 1009 states at 33.7 s), but the enumeration makes 0 cubes, so it stays unknown;
  - the ten are unchanged (the seven proven, one run each), and so is the real-world corpus (bar, 05ac413 against 5d4da3f: 318/361, 0 gained, 0 lost, wrong 0; $0.09);
  - so the raise is harmless and gains nothing until gitea's views make cubes (its counted approvals are over a key and a counter-assigned id).
- **The exact next step:**
  - distributed: make the pool Houdini affordable. Either a smaller pool (the top four, and only the counterexamples of laws the set's proof failed at), or proveSetFast's re-proof after a drop cheap at 70 cubes (EPR side).
  - ring: a ranking where a may-fail cube that reads the counterexample's named cells (Pending at the model's keys) outranks one that doesn't.
  - gitea: why its 5 views make no cube.

**Completing counterexamples, measured as an assumption check** (`runs/engine/a1`, distributed, one run at a 220 s budget, a temporary hook taken out)
- **Why not by naming cells:** a counterexample's unnamed cells are cells its goal never reads, so it holds for any completion of them. Naming them makes the solver fill them arbitrarily, and a candidate false at that one completion still doesn't block. The question that separates is one solver query per candidate: does the counterexample survive with the candidate assumed (IC3's inductive generalization)?
- **The check:** at each of 42 counterexamples (cube or caller goals with a model), the goal asked again with each of the top-6 ranked candidates and each probe-proven target assumed, 1.5 s each.
- **Assuming it proves the goal:**
  - top-ranked definitely false: 59 of 102 (58%); targets definitely false: 10 of 15 (67%);
  - top-ranked may-fail: 0 of 142; targets may-fail: 4 of 42 (10%);
  - targets neither false nor may-fail: 0 of 57.
- **So no real separation:**
  - where a target only may fail, it almost never removes the counterexample, so completing the state wouldn't make it a blocker;
  - definitely false junk blocks nearly as often as the targets do.
  - The counterexamples the rounds generate are mostly not ones the probe-proven set answers: the rounds take another route through the cubes, one that closes on junk. Not built.
- **What that leaves:** steering by the caller's own obligations rather than the cubes': ask the caller's goal with the set and each candidate assumed (the targets are the caller's support), or seed round 0 from a cheap whole-pool Houdini at small sizes. Not tried.

**Steering: the caller's goal, and DuoAI's top-down Houdini** (`runs/engine/td1`–`td4`, `d0`–`d1`; temporary experiment code, taken out)
- **The caller's goal has no signal:** on distributed and ring it is proven from the set in every round ("caller": 0 throughout). What fails is the support laws' own induction, so steering by the caller has nothing to steer by.
- **DuoAI's refiner** (github.com/VeriGu/DuoAI at ecd37c4, `src-c/InvRefiner.cpp`, `top_down_refine`): each round is one Ivy check of the whole candidate set. Ivy checks every candidate's induction with all the others assumed and reports every failure, and the round removes them all at once (with `co_implication`, replacing a removed one by weaker clauses it implies). A Houdini round drops every failing law, never one per proof.
- **The same here** (experiment): every enumerated cube not false at a start; each round each cube's goal by decideLaw with all the others assumed, 1 s each; every failure dropped at once, an undecided one kept.
  - **distributed:** 176 cubes, round 0 asks 129–176 at about 0.6–0.75 s each, 76–134 s on Modal; a 60 s budget doesn't finish round 0.
    - Reusing a model's successor (cubes true before the step and false after) drops 52 more in round 0; the fixpoint is 34 cubes at 90 s either way (without reuse, 145 s).
    - That fixpoint doesn't prove the caller. The cause, traced: in round 0 both "two live transfers" cubes get models that the interpreter doesn't confirm (with 176 laws assumed and a 1 s cap, decideLaw's model is spurious), and their dependents fall in rounds 1–2 to real ones.
    - With only confirmed counterexamples dropping: 23 dropped, 47 unconfirmed kept, a fixpoint of 153 at round 1, and the set's proof (7 s) fails at a false cube kept.
  - **ring:** every one of its 141 queries undecided at 1 s with 141 laws assumed; nothing drops.
- **So:**
  - per-law Houdini at the enumeration's full size costs 2–3× the budget on distributed and doesn't decide on ring;
  - its verdicts hinge on the EPR path's models at 100+ assumed laws: unconfirmed models drop true laws, and the interpreter's confirmation keeps false ones.
  - For the EPR side: decideLaw returning a model at its instance-round cap without confirming it, with many laws assumed.
  - Not built.

**Confirmed models and DuoAI-shaped batches** (`runs/engine/mq1`, `bt1`; temporary code in kernel/prove.ts and core/infer.ts, taken out)
- **Where an unconfirmed countermodel leaves `settle`** (kernel/prove.ts): three exits return the last model without confirming it:
  - on the deadline (`late()`);
  - where the EPR path can't decide a round;
  - past the instance rounds (4, up to 16 while a deadline allows).
  Only `modelInstances` returning nothing (no assumed law broken at the model over its own domain) is a confirmed model.
- **The strict rule tried:** a model only where confirmed, otherwise unknown, the rounds on while the deadline allows. Measured on distributed's round 0, every cube's goal with all 176 assumed, cold, 1 s each:
  - **before:** 116 proven, 60 models (30 the interpreter confirms, 30 it doesn't, the two "two live transfers" among them), 0.6 s a query;
  - **strict:** 103 proven, 9 models (3 the interpreter confirms), 64 undecided, 0.75 s a query. The two "two live transfers" cubes are undecided, no longer refuted, but at a 1 s cap the MBQI loop rarely confirms, so Houdini could drop almost none of the false cubes.
  - Not kept as the default.
- **Houdini batched by view:** a view's cubes share its keys, so their conjunction is one law; each round each view's law is asked with every cube assumed, a model's successor (the interpreter's) drops each cube of the view true before and false after, and the view is asked again. (A goal over all 176 cubes at once needs hundreds of Skolem keys, so this is the shared-reads batching.)
  - **distributed:** 26 queries in all (13, 7, 6 a round), 1.4–3 s each. 176 → 138 cubes, then stalled: groups end undecided, or with a model whose successor drops nothing. All 12 targets are kept, but the set's proof (7 s) fails at a false cube that stayed. 66 s.
  - **ring:** 51 queries over 4 rounds, 172 s; it loses the own-id and leader laws to the successor's reading (true laws; the model's unnamed cells are read at their defaults).
- **So:** neither reaches the probe-proven set inside 60 s. Not built.
  - **The two levers:** a cheaper confirmation of a model at many assumed laws (the MBQI loop converging within a second), and reading a model's successor only where the model names what the cube reads.

**Deferred: predicate abstraction against counters** (gitea's "two counted approvals are never by the same reviewer"). Its views relate no row key to the allocation counter `next`: keySorts never relates a state scalar to a key sort (`node` relates inputs and params only), and a view has no scalar atom to compare a key with. The fix is `key < next` order literals for search only (the final proof still over the concrete machine), and it touches the sort analysis for every rule, so it waits until the core ten are done.

**Since e1ae73d** (`runs/engine/c1`, `f9`; the replay offline, no solver call)
- **The effective few limit:** gen/enum4 has none of `GDP_FEW`: the limit is the literal 4 (core/infer.ts, `few`), and the engine's entry is on the cost clock. tmp/few8w (05ac413, not for merge) has `GDP_FEW` default 8 and the entry on the wall.
- **Per-obligation blockers, falsified offline:**
  - **The policy tried:** each counterexample its own quota of three, the false lane greedy for new coverage of the last 16 states, then a may-fail lane ranked by the literals the model names.
  - **The replay:** 39 captured counterexamples on distributed (`c1/dl-caps.json`), 11 on ring, replayed with no solver call. It selects the probe-proven cubes no better than the top-4 ranking: "Held[x] ∧ Transfer[z, y] ∧ Ep[y] + 1 <= z" 7 → 0, "a live transfer above every epoch" and the same-node "two live transfers" 0 under both.
  - **Why no ranking works:** the eligibility counts say why. distributed's targets are definitely false at 0–2 of the 39 counterexamples, but may-fail at 12–37 (the models leave most cells unnamed). On ring one between turn is definitely false at 4 of 11, the others only may-fail once each. The may-fail lane is diffuse, so any ranking over these models is near arbitrary.
  - **Not kept.**
  - **What it points to:** the counterexample states, not the ranking. Either complete a model's unnamed cells (from the small instance or a second, maximal model), or check a candidate by asking whether it unblocks the failing goal (IC3's inductive generalization by a solver call, a few per obligation).
- **gitea's no-cube diagnosis** (the limit 8 and a wall entry patched locally, uncommitted):
  - locally its views make 15 cubes (Modal's 0 was a cut instance), over map cells only (By, Off, Dis, Stale, Commit), and the caller's law fails at round 0 with no diagram;
  - no view relates a row key to the counter `next`: keySorts gives `next` a sort of its own (a state scalar is never related to a key sort; `node` relates inputs and params only), and a view has no scalar atom to compare a key with;
  - predicate abstraction (`key < next` literals against counters, search only) is confirmed as the missing piece, but it isn't small: it needs state scalars related in the sorts for every rule, and a scalar atom per view. Not built.
- **Verdicts** (`f9`, all ten, 2 runs, gen/enum4 at b91d305's code): sync 8–10 s, async 24–25, decentralized 17, 2PC 18–20, ticket 31–40, toy 15, sharded 31, proven; distributed 63–65, ring 60, wo 64–68, unknown.
- **The real-world corpus** (bar, 29ede5f against 5d4da3f): 318/361 as the base, 0 gained, 0 lost, wrong 0.
- **The exact next step:** for distributed, complete each counterexample's unnamed cells before blocking (the cheapest: the kernel's model asked again with every cell the cube candidates read named), and re-run the offline replay to see whether the targets become definitely false. Only then rank.

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
