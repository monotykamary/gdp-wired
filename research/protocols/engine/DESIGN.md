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

## gen/laneK2, step 2: the search over counts (untrusted; core/counts.ts)

**Built (general: nothing reads a protocol's name):**
- **Runtime** (core/machine.ts's `carriedView`, with the params): each count map at a request's view, a cell computed
  when read (`CountCells`): CountMachine.lean's CReach is what the interpreter runs. watch.ts's `allowed` and dsl.ts's
  cross-check pass the params.
- **DSL** (`.counts({c: env => ({below, body: (x, k) => …})})`): a map the flags, assumption and step read at the view, a
  law at the state; `Machine.counts` built from it (j `c$x`, key `c$k`).
- **Ports** (research/protocols/ic3syn): `majority()` is TLA+'s own `Cardinality(Q) * 2 > Cardinality(Node)`, Q within
  the nodes and its size the count `members` (no injective rank, no witness inputs); majorityset's row `voters[n]` a
  state count. Re-checked by BFS against TLC's states: quorum 94, toy forall 41, naive 55, simple election 66, toy epr
  41, toy 41, majorityset 400, each equal; consensus wo/forall/epr ran past the BFS's 60 s cap (as before).
- **The search** (`searchCounted`, proveRule's path for a rule with counts):
  - *the guard's shape*: a write P[t] under a quantified flag "every member of a set the request counts satisfies
    R(member, t)", with the assumption comparing that count with a bound, declares the state count
    c(x) = |{k < bound: R(k, x)}| and proposes P[a] ⇒ the same comparison with c[a]; a guard comparing a state count at
    the written key proposes P[a] ⇒ that comparison at a;
  - *supports*: each map's cells at most what the small instances reach; a relation over pairs at most one second key
    per first; one relation (pairs, or one key) inside another, same or swapped pair; every candidate kept only if true
    on every reachable state of the small instances (each param 2 and 3, inputs and sets below 3);
  - *each goal's certificate*: the count cells the goal reads (the conclusion's first, then each post-step read's twin
    before it, then reads at a constant or the law's own names; six at most), Count.lean instances over pairs with one
    bound (a count after the step at least each other one; two counts before it that meet), ten at most, each with a
    fresh witness; the laws over one key and the quantified flags at the witnesses and the request's inputs, the laws
    over two keys at pairs of the law's own names and inputs; the tree grown (10 s a goal);
  - *Houdini*: a candidate whose goal finds no tree is dropped, the set tried again; the kernel's checkCountedLaws
    checks the final set (the proof, not the search, is trusted).



**IC3Syn, the counting class, nothing written** (75ce118 and 0c39b23; one run each at 60 s and 300 s, Modal's 2-vCPU
containers; before: gen/laneA's table, main ae36917, two runs, the ports' majorities as injective ranks; seconds)

| # | protocol | before 60 s | before 300 s | after 60 s | after 300 s |
| --- | --- | --- | --- | --- | --- |
| 4 | quorum_leader_election | unknown | unknown | **proven 2.0** | **proven 2.4** |
| 5 | toy_consensus_forall | unknown | unknown | **proven 3.1** | **proven 3.3** |
| 23 | toy_consensus | unknown | unknown | **proven 2.0** | **proven 2.4** |
| 22 | toy_consensus_epr | unknown | unknown | unknown 16.4 | unknown 22.7 |
| 19 | naive_consensus | unknown | unknown | unknown 9.9 | unknown 11.2 |
| 21 | simple_election | unknown | unknown | unknown 36.3 | unknown 29.3 |
| 26 | majorityset_leader_election | unknown | unknown | unknown 60.0 | unknown 64.8 |
| 27 | consensus_epr | unknown | unknown | unknown 60.1 | unknown 300.0 |
| 15 | consensus_wo_decide | unknown | unknown | not run (unknown at 300 s) | unknown 200.4 |
| 16 | consensus_forall | unknown | unknown | not run (unknown at 300 s) | unknown 300.2 |
| 28 | mldr | killed | killed | killed (not ported to counts) | not run |

The suite's others at 60 s take the path they took before (no counts): consensus 0.3, tcommit 0.5, i4 lock server 8.3,
lockserv automaton 11.7, lockserv 10.4, simple decentralized 8.2, i4 two-phase commit 14.5 proven; the ∀∃ class and the
rest as gen/laneA's. **10 of 29 proven at 60 s** (gen/laneA: 7; 8 at 300 s with twophase, not rerun). The pilot's broken
variants: none proven.

**Why the others don't prove** (GDP_COUNTS_TRACE): toy epr, naive and simple election need supports no template states (a
relation over three keys, a message-to-state implication with a value); majorityset spends its budget on the
three-key "one per row" law's instances; the consensus ports' law sets outgrow the budget. core/infer.ts's enumeration
finds such ∀ laws: joining it to the counted goals (its EPR oracle given Count.lean's instances) is the next step. The
∀∃ class's ghost maps are not built.

**Gates (step 2):** the ten 200 of 200 at 60 s (pilot 10, then 190; median/max s: wo 39.5/51.1, decentralized 15.1/25.0,
distributed 32.5/37.8, async 23.4/28.3, sync 8.3/11.2, ring 37.4/43.2, sharded 29.0/38.6, ticket 31.9/38.8, toy forall
11.5/21.1, 2PC 16.0/20.4); the quick bar (75ce118; <main>/runs/bar/runs/75ce118b7b5c-vs-ae369178e65d-quick-2026-10-310213):
wrong 0 everywhere, one ITS task lost "solid" at the time limit (the base answers it at 50–60 s of 60; ITS reads no
count and no carried map), nothing else solid lost; tsc and oxlint (the suite's form) clean on the touched files; the
ports' state counts equal TLC's; the suites (`--only suite,suite-usual`, 75ce118): 240 of 240 in each, nothing lost.
Bytes (against cd97c61, both steps): core/ +20,038 (counts.ts 16,455, machine.ts 1,868, dsl.ts 1,696, watch.ts 19),
kernel/ +13,313.

**After the rebase onto main 078bd1d (0.34.0):**
- **Lean:** the three new proofs (toy_consensus 4 laws, quorum_leader_election 4, toy_consensus_forall 8, found with
  nothing written) exported by research/protocols/ic3syn/counted-lean.ts through cmachineToLean and checked: lean-exit 0,
  no sorry, each `ic*_laws` on [propext, Classical.choice, Quot.sound].
- **A second run** of every counting protocol at 60 s, broken variants included: the same verdicts (proven: toy 2.3 s,
  quorum 2.1, toy forall 3.1; the rest unknown); every broken variant unknown, none proven.

## gen/laneK2, step 1: counts in a machine's laws and steps, proven in Lean

**The ask:** win IC3Syn's counting (11) and ∀∃ (6) classes with nothing written: (1) a machine-level counting statement
in the trusted Lean kernel, ever so cautiously; (2) counts and ghost maps in the search. **Step 1 is built, proven,
twinned, tested, exported end to end and reviewed twice by terra; step 2 is not built** (below: why, and the plan).

**The statement (lean-kernel/CountMachine.lean, 97.6 KB, on Sets.lean and Count.lean, neither changed).**
- **Count declarations on SMachine, not a count term.** A count term `E.count key below body` would add a binder to E:
  every function and lemma over E in Kernel.lean, Sets.lean, Sums.lean and the rest (evalE, substE, substRE, occE,
  occME, inlineE, beqE, congrE, …: dozens, with capture-avoiding substitution under the binder) would change, and every
  trusted proof built on them with it. A declaration changes none of them: `CDecl ⟨mp, post, j, key, below, body⟩` names
  a map `mp` whose cell at x is Σ_{k < below} body(k), j at x and key at k; the machine stays an `SMachine`, with `mp`
  among the maps a request carries.
- **Semantics.** `CReach` is `SReach` with each request carrying each count map at its count at the request's view
  (`GHolds` at the inputs-set state over the state's and the carried maps; a count reads no flag, quantified flag or
  witness, so the view's flags don't change it). `creach_sreach`: every CReach state is an SReach state.
  `counts_exist`: at every state and request the count maps can be set to their counts, the other carried maps kept,
  so CReach is the rule's own runs (the runtime computes exactly cntOf). A law reads a count of the state
  (`stateOnly`: its bound and body read no request, flag or carried map), whose value at a state is `withCnt`.
- **Goals.** Sets.lean's own (`cStartGoal`/`cStepGoal` are sStartGoal/sStepGoal), the law proven read with each count map
  renamed to its post name (`renLaw`); each goal declares the counts it reads: at the start each state count read
  across the start, at a step each count as the request carries it and each state count read across the step
  (`afterDecl`: substituted by the step as the law is, j and key kept).
- **Certificate** (`CCert`, `checkMC`): the goal's hypotheses it names (each one Lean builds), the cells it reads (a
  fresh variable, a count map, a key term), Count.lean's instances, table and tree. It becomes Count.lean's counted
  goal (named hypotheses, each read variable equal to its cell, a count per read with j at the key term), checked as
  Count.lean checks it but with each instance's witness fresh for the counts and the instances' bounds only
  (`checkCountedW`): a machine goal must read the witness in its instances of laws and quantified flags (the voter of Q
  at the key two majorities share). `countedW_sound` asks the hypotheses at every value of the witnesses, and the
  machine supplies that: witnesses are variables no part of the machine or a law reads (`witsOk`), so the frame holds
  wherever they are (`setAll`, `sNext_setAll`, `sReq_setAll`).
- **Theorems** (each `#print axioms` = [propext, Classical.choice, Quot.sound], no sorry): `mc_sound` (an accepted
  goal's hypotheses don't hold at every witness value where each declared map is its count), `cmachine_sound` (every
  entry of an accepted proof holds in every CReach state, its laws reading each count map as the state's count, a law
  about several keys at every value of its further keys), `counts_exist`. The proof is smachine_sound's, with the post
  names set at the counts after the step in the goal's maps (`atPosts`; the machine reads them nowhere: `sNext_posts`).

**The TypeScript twin (kernel/kernel.ts, "counts in a machine"; core/machine.ts's `Machine.counts`).**

| Lean (CountMachine.lean) | kernel.ts | How they correspond |
| --- | --- | --- |
| `CDecl ⟨mp, post, j, key, below, body⟩` | `Machine.counts[mp] = {j, key, below, body}`, `CountDecl` | post = `postName(mp)` = `mp#`; the exporter numbers both |
| `cntOf`, `GHolds`, `withCnt`, `CReach` | (meaning; the runtime is not built) | |
| `toCount`, `toCounts`, `readHyp` | `toCount`, `toCounts`, `readHyp` | `substE(body, {vars: {[j]: t}})` is Lean's `substE [(j, t)]` |
| `readFresh`, `readsOk` | `readFresh`, `readsOk` (+ `readsTyped`, `safeTerm`: names are strings, terms over safe naturals) | same conjuncts; TS stricter |
| `witFreshW`, `countedOkW`, `checkCountedW` | same names | `typed` (safe-integer coefficients) as Count.lean's twin |
| `checkMC` | `checkMC` (+ instance bounds `safeTerm`) | Lean names the hypotheses (`namedIn`); TS reads its own goal whole |
| `stateOnly` | `stateOnly` | Lean: avoids extVars ++ flagVars, carried maps; TS: a count reads only params, inputs, state, j, key and declared maps (countsScope), so it avoids no input and no carried map |
| `renLaw` (`substRC [] (frameRd cren getRd)`) | `ren` in countedObligations (`get C k` ↦ `get C# k`) | the same renaming |
| `afterDecl σ rd` | `after(at)`: `substE(d.below / d.body, start.at / turn.at)` | the run's substitution, j and key unassigned |
| `cStartGoal`, `cStepGoal` | `countedObligations` (obligations' with the proven law renamed) | the exporter names TS's hypotheses; Lean checks each is one it builds |
| `cStartDecls`, `cStepDecls` | `after(start.at)`, `[...all, ...after(turn.at)]` | same order |
| `cDeclOk` (carried, j ≠ key, mFresh j and key, below avoids key, no flag/quantified flag/witness, no count or post map, no entry's skolem, key or further key) | `countsScope`: j, key plain, distinct, none of the machine's names, bound keys, quantified flags, witnesses, any law's or fact's key or `k#`; bound reads params, inputs, state, j; body those and key; maps, carried, functions only; naturals | TS stricter (reads only declared names) |
| `cApart` (post names read by nothing, none of the machine's maps) | posts `mp#`; `#` is reserved in every name (`plainName`) | nothing declared can be `mp#` |
| `cEntryOk` (law avoids carried but state counts, and posts) | `scope`: a law reads `[...maps, ...fns, ...stateCounts(m)]` | |
| `witsOk` | `witsOk` (+ fact keys) | TS stricter |
| `checkCMachine` | `checkCountedLaws` | every goal a certificate, witnesses fresh, each `checkMC` |

**Tests (kernel/countmachine.test.ts, 19 tests).** The hand-built toy consensus with its counts as TLA+ states them
(op 0 casts once; op 1 decides `val` with a request's set Q, `2·|Q| > size` its count `quorum`, all of Q having voted
`val`; laws: a decided value has `2·votes[a] > size`, `votes[a] = |{n < size: Vote[n] = a + 1}|`, and one value is
decided): accepted, and true by brute force on every reachable state at size 2 and 3 (count maps computed at the
view), false without the quorum guard. Refusals: obligations refuse a machine with counts; a law reading a request's
count; each declaration condition; each certificate guard on its own (pointed: a certificate whose regrown tree
checks against the goal mcGoal builds, the kernel refusing it), including a witness at a param (`size`: the instance
then claims the sum is not positive, an unsound acceptance the guard stops); a stale read (votes for votes#) of a
false law whose stale goal is a tautology; every term constructor of a certificate over safe naturals, edges accepted.
A fuzz: 60 mutated laws and certificates, trees regrown, 15 accepted, each true on the small instances.

**Mutation tests** (kernel/mutants.ts, `MUTANT_BATTERY=countmachine`, on Modal; the counted section, its scope lines and
`plainName`): **121 of 126 killed.** The first run left 45: the refusal tests failed for more than one reason, so a
weakened guard went unnoticed; the pointed tests (a certificate only that guard refuses, its tree regrown) kill them.
(A run while the battery's own file failed reported every mutant killed; it was discarded and rerun from a passing
baseline.) The 5 left are each a guard another check duplicates, in Lean as in TS: an instance's bound reading a
witness, or one not over the naturals (an instance's bound must equal its counts' bound, which reads neither:
`resolve`), a read named as a witness or reading one in its key term (`witFreshW`'s `c.v ≠ w` and its body check, with
the key term substituted in), a law about a request (`scope`: a law reads no input).

**End to end** (`lean-kernel/count-examples.ts`, the suite's `lean-count` job, which now compiles CountMachine.lean too):
the toy consensus exported by `emit.ts`'s `cmachineToLean` (the machine with its count maps carried, the declarations,
each law's entry with its two certificates), `checkCMachine … = true` by `decide +kernel`, `toyc_laws` by
`cmachine_sound`, and three tampered certificates Lean computes to false (a witness the law's skolem; the count after
the step read as before it; an instance's unit 0). Lean 4.34.0, lean-exit 0, every `#print axioms` the three.

**terra's two reviews (narrow prompts; each claim checked against the code).**
1. *Does cmachine_sound mean what the header claims?* (a) A count could read a plain flag variable in Lean (cDeclOk
   avoided quantified flags and witnesses only), so CReach's count (at the inputs-set state) could differ from the view
   sView decides: **real** (the header's "at the view" was false for such a count). TS already refused it (counts read
   no flag). Fixed in Lean: cDeclOk avoids flagVars; the header now says so. (b) A count could read a law's own key,
   which withCnt freezes at the state while MLaw.Holds varies it: **real as a qualification**, TS refused it. Fixed:
   cDeclOk avoids every entry's key. (c) counts_exist alone doesn't prove the runtime's runs are CReach's: true; the
   runtime that computes cntOf at the view is CReach by definition, and with (a) fixed the view and CReach's state read
   a count alike. Not built in this lane (no runtime yet). (d) keys2, post clashes, key in the bound: protected.
2. *Can checkCountedLaws accept what checkCMachine refuses, making a false law look proven?* (a) **A real kernel bug, on
   main too:** a law is proven at its key's fresh name `k#`, and nothing reserved `#`, so a further key named `k#`
   (∀ k, k#. k = k# read as k# = k#) or a state named `k#` captured it, and `checkLaws` (not only the counted path)
   accepted a false law. Lean refuses (key2Ok, skFresh). Fixed: `plainName` reserves `#` in every machine name and every
   law and fact key; tests show both captures refused. (b) A read's key term (and an instance's bound) was any object,
   0.5 accepted: TS-only mismatch, not shown unsound; fixed (`safeTerm`), tested per constructor. (c) Fact keys were
   not among the names a witness or a count's j and key must avoid: mismatch with Lean's skFresh, not shown unsound;
   fixed, tested.

**Gates** (Modal; nothing run on the laptop past git):
- **Lean:** the suite's `lean-count` job (CountMachine.lean compiled, its `#print axioms` and the exported toy consensus
  checked): lean-exit 0, every theorem on [propext, Classical.choice, Quot.sound], no sorry.
- **Tests:** countmachine.test.ts 20 of 20; count, kernel, refusals, tamper, sets, steplaw and history test files pass.
- **The quick bar** (c40136b against ae36917's baseline;
  <main>/runs/bar/runs/c40136ba76a9-vs-ae369178e65d-quick-2026-10-310115/REPORT.md, 365 s, estimated $2.8): wrong 0 and
  nothing solid lost in any group (CHC 518 against 518.3; ITS 362 against 361.7; SV, TIP, f1, f2, rw, g332 as the base;
  onecpu no failure; Lean's 6 recurrent sets checked).
- **The suites** (`--only suite,suite-usual`, 6321887; <main>/runs/bar/runs/63218877b230-vs-ae369178e65d-full-2026-10-310122):
  one loss in each, `check` (oxlint: two unused imports, emit.ts's MapRead and the test's `times`), fixed in the next
  commit; tsc clean there. The fixed `check` rerun on this worktree's mount: no error in a file this lane touched (the
  errors left are vendor/ imports, absent from the worktree).
- **The ten** (6321887; the gauntlet's jobs-g-pilot and jobs-g1–4, 60 s, Modal's containers; job seconds, a container's
  start included): 200 of 200 proven: consensus_wo_decide 20/20 (median 41.7, max 47.4), decentralized 20/20 (16.6, 19.4),
  distributed 20/20 (33.1, 37.0), lock_server_async 20/20 (22.8, 27.2), lock_server_sync 20/20 (8.9, 11.6), ring 20/20
  (41.5, 48.9), sharded 20/20 (28.2, 34.9), ticket 20/20 (33.2, 42.4), toy_consensus_forall 20/20 (12.0, 13.7),
  two_phase_commit 20/20 (18.0, 21.3). (The search is unchanged; the kernel's `#` reservation is the one change every
  machine meets.)
- **IC3Syn:** not rerun: nothing on the search side changed, so its table is gen/laneA's (7 of 29 at 60 s, 8 at 300 s).

**Bytes:** core/ +666 (machine.ts's `counts`), kernel/ +13,306 (kernel.ts: the counted section, `#` reserved, the
scope lines); lean-kernel/CountMachine.lean 97.6 KB (new), emit.ts's cmachineToLean, count-examples.ts's toy.

**Verified, not**
- **Verified:** cmachine_sound, mc_sound, counts_exist in Lean 4.34.0 (three axioms, no sorry); the toy consensus end to
  end (TS accepts, Lean checks, three tampers false in both); the TS twin's refusals and the fuzz; 121 of 126 mutants;
  terra's findings each reproduced in the code and fixed; the bar, the suites (after the lint fix), the ten 200/200.
- **Not verified:** any search use of counts (none built: no IC3Syn protocol gains); the runtime for counts (not built:
  CReach is the meaning a runtime must implement); the 5 surviving mutants are argued equivalent, not shown; terra's
  reviews read the code, they don't prove its absence of bugs.

**Step 2, not built: why, and what it needs.** Step 1's review found two real issues to fix first (one a kernel bug on
main), and the search side is larger than a lane's remainder: (1) the runtime (core/machine.ts's interpret, the
engine's compiled rows, compileJs) computing each count map at a request's view, and `Machine.counts` in the DSL
(`.counts(...)`); (2) the ports' majorities as counts (`Cardinality(Q) * 2 > Cardinality(Node)`, today common.ts's
injective rank) with check.ts's TLC agreement re-run; (3) a counted prover: for a goal, the cells it reads (each count
map read before and after the step) and Count.lean instances over pairs of cells with one bound, coefficients from
two shapes (+1, −1 for a count that doesn't drop; +1, +1 and unit −1 for two that meet), each witness fresh with the
laws and quantified flags instantiated there, then the EPR path decides the goal; (4) the engine's candidates: a
write `P[t] := 1` guarded by `2·C[_] > B` with C a set's count and a quantified flag `∀k ∈ set. R(k, t)` proposes the
state count `c_R(x) = |{n < B: R(n, x)}|` and the law `P[a] = 1 ⇒ B < 2·c_R(a)` (every counting protocol in the class
has this guard shape), and the ∀∃ class its ghost map (checkGhostedLaws exists; the choice of W is exists.ts's). The
toy consensus above is exactly the proof (3)–(4) would have to find.

## gen/laneA2: one incremental EPR encoder a sort of goal; the join counted; the ten 20 of 20 (branch gen/laneA2 from dd752f0)

**The ask:** "10 of 10, each inside 60 s" guaranteed: 20 of 20 for every protocol on Modal's 2-vCPU containers, ring with
margin. Ring was 17/20 and wo 19/20 at dd752f0 (above); ring needed about 35% less work.

**Where ring's EPR work went** (dd752f0, a probe on decide()'s meter; ring's 296 decisions, 15.3M units, 58% of its
engine clock): building the encoding 82% (each hypothesis' walk and Tseitin clauses, the order's transitivity over ~24
terms), propagation 5%. 63% of all units were the same goal asked again in settle()'s model rounds (a model breaks a law at
a new tuple, the goal is asked with a few more instances: 915 hypotheses, then 916), and 75% of a decision's hypotheses
were the previous decision's, by text.

**Built (kernel/epr.ts, untrusted):**
- **Facts by text:** each hypothesis' lifted form, its reads, comparisons and bounds, kept by its JSON text (a goal asked
  again is mostly the same texts); a goal's sorts (parts, caps, ordered maps and scalars, bounded terms: `stateOf`) from
  them, the comparisons' leaves and tuples memoized.
- **One encoder a sort of goal** (`encoder`, a pool of four by `State.sig`: the patterns, parts, caps, ordered maps and
  scalars; each finite variable a goal reads checked against its bound there, else an encoder of its own): every
  hypothesis encoded once, its clauses guarded by an activation literal (¬a ∨ clause; a Tseitin definition unguarded, it
  holds in every model); atoms, cells, ordered terms and the axioms over them all kept and extended as terms arrive
  (congruence, the order's totality, transitivity, discreteness, successors, Ackermann: each holds in every model of any
  goal); an exact variable's one value under each hypothesis that bounds it.
- **One CDCL under assumptions** (`cdclSolver`, growing as variables arrive): a goal is its hypotheses' activation
  literals, decided first in order; a refutation's origins are hypotheses of the goal (a clause of one not assumed is
  satisfied by its guard, never a reason), mapped back to the goal's indices as the core. A goal that isn't the one asked
  last searches fresh (learned clauses, activities, phases dropped: its refutation and model are a search of its own); the
  same goal asked again with more instances keeps its own. Theory lemmas and lazy transitivity stay (each holds always).
- **Read back over the goal's own terms:** its ordered terms, finite variables, cells, successors and theory rows only, so
  a model, its witness and its diagram are the goal's as before; judged on every hypothesis as before. `fill` and `fresh`
  (the retries) take an encoder of their own; GDP_EPR_INC=0 an encoder a goal.
- **The join's last wall counted** (core/infer.ts): where the engine follows, the join's grow is its tested order
  (joinQueryMs on the kernel's counted work) cut at 400k units of the cost model (kernel/prove.ts's `withWork`, exported)
  and 300k EPR units, in place of the 2 s wall. Decentralized's proving query takes 217k and 1.6k; wo's dead one (every k:
  Leader[k] <= VoteRequestMsg[k]) took 1.2M and 647k on the counted joinQueryMs alone (13 s, wo 44–47 s, the previous
  lane's variant). Tried and not kept: the query on the cost model's clock (counted(fullRate)) finds a model there and wo
  ends unknown; a cap on that clock alone keeps the order and the outcome but costs wo 5–7 s; a core shrink (re-solve with
  the core alone), and a retry alone where a shared encoder's core didn't prove (ring +4 v-s), both out for the fresh search.

**Verdict agreement** (research/protocols/engine/agree.ts: wodump.ts's decideLaw goals of a run, replayed by dd752f0's epr.ts
and by this one, 4 s a goal): ring 78 goals, 74 decided by both, 0 differ, 0 decided by dd752f0 alone, 4 by this one alone
(dd752f0's unsat-then-sat at its cap); wo 63 goals, 63 by both, 0 differ. Cores: 734 hypotheses against 810 (ring), 269
against 299 (wo). Models are confirmed as before (strict); a refutation is the kernel's proof of its core, as before.

**Work saved** (the engine's meters at the join's end, one path per protocol, dd752f0 → gen/laneA2):

| protocol | EPR units | engine clock v |
| --- | --- | --- |
| ring_leader_election | 15.26M → 4.75M (−69%) | 52,173 → 31,158 (−40%) |
| consensus_wo_decide | 4.65M → 1.56M (−66%) | 19,767 → 12,973 (−34%) |
| distributed_lock | 4.35M → 2.07M (−52%) | 28,798 → 24,188 (−16%) |
| sharded_key_value_store | 0.82M → 0.54M (−34%) | 14,146 → 13,600 (−4%) |
| decentralized_lock | 0.49M → 0.44M (−10%) | 7,831 → 7,730 |
| toy_consensus_forall | 89k → 70k (−22%) | 5,773 → 5,736 |
| the other four | no EPR decision | unchanged |

The kernel's own work (`full`) is as before (ring 2.64M against 2.63M). Per unit, the new path is slower in real time
(the texts, the sorts, the read-back's restriction, uncounted), so the wall saved is less than the clock's: ring's median
55.9 → 39.6 s (−29%) against −40% counted; wo's 41.7 → 41.3 s, its engine's 6.8 counted s saved about what the counted
join costs over the old wall (its dead query 4–7 s against 2.4 s).

**The gauntlet** (6c21ef2; the ten, 20 runs each at 60 s, one worker, Modal's 2-vCPU containers, four batches of 50, the
first the pilot; seconds, the search's own time; one value of the engine's clock per protocol across its 20 runs)

| protocol | proven | median s | p95 s | max s | v at the join's end |
| --- | --- | --- | --- | --- | --- |
| consensus_wo_decide | 20/20 | 41.3 | 49.4 | 52.4 | 12,973 |
| decentralized_lock | 20/20 | 15.6 | 18.3 | 18.3 | 7,730 |
| distributed_lock | 20/20 | 33.1 | 37.1 | 37.8 | 24,188 |
| lock_server_async | 20/20 | 23.3 | 27.1 | 29.4 | 5,090 |
| lock_server_sync | 20/20 | 9.5 | 11.2 | 11.2 | 3,768 |
| ring_leader_election | 20/20 | 39.6 | 43.9 | 44.6 | 31,158 |
| sharded_key_value_store | 20/20 | 30.1 | 34.3 | 39.0 | 13,600 |
| ticket_lock | 20/20 | 32.4 | 39.3 | 41.1 | 21,201 |
| toy_consensus_forall | 20/20 | 11.2 | 12.9 | 13.1 | 5,736 |
| two_phase_commit | 20/20 | 16.8 | 19.6 | 24.3 | 8,836 |

- **200 of 200.** Ring's p95 43.9 s (median 39.6, 29.4–44.6 across containers), under the ~45 s margin asked; wo's p95
  49.4 s, max 52.4 (28.4–52.4: wo's spread is the containers', its path one).
- **An earlier commit's batch** (0627ba1, before the fresh search; runs/laneA2/g0): 49 of 50, the miss two_phase_commit at
  75.7 s on a container about 7 times slower than the batch's others (the same path, v 8,836; its join alone 30 s against
  4–6 s; 2PC asks the EPR path nothing). A container that slow misses any protocol past ~8 s; none in the 200.

**Gates** (at 6c21ef2):
- **IC3Syn's 7** (jobs-ic7.json, 60 s, twice): 14 of 14 proven (0.3–16.4 s).
- **Lean re-check** (the suite's lean-protocols-wo job, and the same for ring): both found sets exported (ring 18 laws
  found, 1.85 MB; wo 18 with the ∃ law, 0.57 MB) and checked by Lean 4.34.0, lean-exit 0, no sorry.
- **The quick bar** (6c21ef2 against ae36917's baseline; <main>/runs/bar/runs/6c21ef201fb8-vs-ae369178e65d-quick-2026-10-301947/REPORT.md,
  551 s): gained 0, lost 0, wrong 0 in every group. f1 34 as the base; f2 25 against 24 (the one task noise after 3 reruns
  a side); rw 74/14/3 as the base; g332 the same search on 332 of 332 (291.1 s against 281.5); the suite 237 of 237, none
  failed; onecpu no failure.
- **Typecheck and lint:** tsc clean on kernel/epr.ts, kernel/prove.ts, core/infer.ts and the research files touched;
  oxlint --type-aware --deny-warnings clean on the same.

**Bytes:** core/ and kernel/ +9,551 against dd752f0: epr.ts +9,245, infer.ts +299, prove.ts +7.

**Spend:** $1.35 billed through the 19:00 UTC hour (still filling in): $0.58 for this lane's 30-odd batches (probes,
profiles, agreement replays, the 250 gauntlet runs, IC3Syn's 7 twice), $0.04 for the two Lean checks, $0.73 for the bar's
18 apps. Nothing of mine left running.

**Verified, not**
- **Verified (Modal):** the table (200 runs, one path per protocol); the agreement on ring's and wo's goals; IC3Syn's 7;
  Lean on ring's and wo's final sets; the bar.
- **Not verified:** agreement beyond ring's and wo's dumps (the other protocols' decisions only through their verdicts in
  the gauntlet and the bar); that the counted join's caps hold for rules outside the ten and the bar's corpora (where the
  engine follows, a proving join query past 400k units of the cost model now ends unknown where a fast machine's 2 s wall
  let it finish); containers far slower than these (the pilot's 7×).

## gen/laneA, determinism: the engine on a counted clock; the gauntlet (main a391a3d merged; branch fd06297)

**The ask:** "10 of 10 with nothing written" guaranteed, not usually true: every search decision on work counts, not
wall time; ring's margin; the ten 20 times each at 60 s.

**What depended on time** (core/infer.ts's engine, from the small instance on: 79 `performance.now()` reads and 24 of
the search's wall end): the small instance's BFS cut and walks, the filter's time share (six times the small
instance's own time, at most a sixth of what is left), each goal's cap (`within`: a wall end per goal, the EPR path
stopped only by that wall), the rounds' growth ("what a quarter of what is left affords"), Houdini's 40%-left switch,
the cone's and the set proof's loops. On a slow container the filter read fewer states (361–490 against 500–650), left
more cubes (ring's pool 47–61, not 44), round 0 took 24–36 s, and ring missed: research/protocols/engine/DESIGN.md,
gen/laneA's IC3Syn section.

**Built (untrusted; core/ and kernel/ +8,489 bytes against the merge base: infer.ts +3,348, machine.ts +2,810, epr.ts
+990, prove.ts +85, plus last round's dsl.ts +612 and exists.ts +644):**
- **An EPR meter and cap** (kernel/epr.ts): `eprMeter` counts each clause and hypothesis read and each literal the CDCL
  search propagates; `withEprCap(units, f)` caps it; `eprFirst` and `settle` stop at the cap as at the wall. A goal's
  EPR decision ends at the same place on any machine. Default cap: none, so nothing outside the engine changes.
- **The engine's clock** (`vnow`): from the engine's start, its own meters at fitted rates (BFS tries 80 a ms, EPR units
  500, view rows 100, the cost model's work 220), in place of `performance.now()` in all 79 decisions; the wall
  (`stop`, the search's 60 s) only ends it. Its budget `eUntil` = 0.95 × (ms − 0.3 × the join's count), fixed at the
  engine's start (GDP_ENGINE_SHARE).
- **A goal's cap** (`within`): the kernel's counted deadline and the EPR cap, both from the goal's share of the engine's
  clock; the per-goal wall is gone, only the search's wall stays.
- **The filter by kills:** its larger instances' states read as their BFS finds them (`instance`'s `visit`), until 150
  in a row kill nothing, 1,000 at most, the BFS ending there; a share of the engine's clock its outer bound.
- **The views' rows compiled** (core/machine.ts's `compileE`/`compileC`, closures over (env, state) with evalE's values
  and errors; one env per assignment instead of a copy per level): reverted last round because the time-boxed filter
  spent the time saved; with the filter by kills, it is time saved.
- **Short clauses without a Set** (kernel/epr.ts's `add`): the same literals in the same order.
- **Trace:** 'join meters' and the td events carry the meters (real, v, EPR units, rows, tries, work).

**Deterministic, measured:** across the gauntlet's 200 runs every protocol took one path: the engine's clock read the same
value at the join's end in every run (ring 52,173 in 19 of 20, the 20th stopped by the wall at 51,111; wo 19,767 in 19
of 20, the 20th at 15,593 by the wall; distributed 28,798 and sharded 14,146 in 20 of 20); ring at --ms 90000 and
120000 took the same path to the same proof at 52,173. A miss is now only the wall: a container too slow for the path.

**The gauntlet** (fd06297; the ten, 20 runs each at 60 s, one worker, Modal's 2-CPU containers, five batches of 10–50;
runs/det/g0–g4 in ../gdp-wired-laneA; seconds, the search's own time)

| protocol | proven | median s | p95 s | max s | misses |
| --- | --- | --- | --- | --- | --- |
| consensus_wo_decide | 19/20 | 41.7 | 50.8 | 66.1 | unknown 66.1 |
| decentralized_lock | 20/20 | 16.7 | 18.1 | 18.9 |  |
| distributed_lock | 20/20 | 34.5 | 39.3 | 40.9 |  |
| lock_server_async | 20/20 | 23.7 | 31.5 | 33.5 |  |
| lock_server_sync | 20/20 | 9.6 | 10.9 | 11.0 |  |
| ring_leader_election | 17/20 | 55.9 | 61.3 | 62.3 | unknown 60.1, unknown 60.1, unknown 60.7 |
| sharded_key_value_store | 20/20 | 30.2 | 36.8 | 36.9 |  |
| ticket_lock | 20/20 | 34.6 | 39.9 | 41.3 |  |
| toy_consensus_forall | 20/20 | 11.3 | 13.8 | 14.5 |  |
| two_phase_commit | 20/20 | 17.3 | 20.6 | 21.3 |  |

- **The claim doesn't hold for two of the ten.** ring 17/20 and wo 19/20; the other eight 20/20 with their p95 at most
  41 s. Each miss is the wall on a slow container: the same path took 37–62 s for ring and 31–66 s for wo across the
  batch (the containers' speed varied 1.6× within one batch of 50).
- **Ring's margin, not reached.** Its path needs 52.2 of its 54.1 budget units and runs a median 55.9 s: a container 1.5×
  slower would need ~84 s. Tried at fixed paths (one run each, now that one run is the path): per-goal caps 700, 1,500
  and 2,000 against 1,000, the filter's quiet window 300 against 150: each ran out of ring's 51.3 units unproven. What would: cut ring's work about 35%; round 0 (44 goals, 22 units, 7–12 left
  undecided at their cap) and rounds 1–4 (18 units) are the place, and the EPR decision is 37% of a ring run (bun's
  profile, runs/ic3syn/ringprof2).
- **Still on time** (not in the engine): the join's grow, where the engine follows, has a 2 s wall per query
  (`joinGrowWall`); the join's counted clock differs by about 2% between runs (wo's eUntil 42,768–43,165), so that wall
  changes some query's outcome now and then, and the engine's budget with it. Tried in a separate tree (not on the
  branch): the query on the counted joinQueryMs with an EPR cap of 2 s's units in place of the wall; the ten once, all
  proven (decentralized needs the counted joinQueryMs, not 2 s), wo 44–47 s. Not gated, so not merged in.

**Gates:**
- **The ten:** the gauntlet above.
- **The IC3Syn suite's 7** (60 s, twice; runs/det/ic7): consensus, tcommit, lock server, lockserv, lockserv automaton,
  simple decentralized lock, i4 two-phase commit, proven in both runs (0.2–18.4 s).
- **The quick bar** (fd06297 against ae36917's baseline; <main>/runs/bar/runs/fd06297ad933-vs-ae369178e65d-quick-2026-10-301836/REPORT.md;
  estimated /bin/zsh.62): f1 34 and f2 24 as the base; rw 73/14/4 against 74/14/3, the one task noise after 3 reruns a side
  (lost 0); g332 332 of 332 (296.2 s against 290.3); the suite 236 of 236; onecpu no failure. Gained 0, lost 0, wrong 0.
- **Typecheck and lint:** tsc clean on core/, kernel/ and research/protocols/ic3syn (on Modal; the errors left are
  vendor/ imports), oxlint clean on the same (without --type-aware, which needs node).

**Spend:** $1.21 billed through the 18:00 UTC hour for this task's 42 apps (the calibration runs, the experiments at
fixed paths, the 200-run gauntlet, the gates, the bar's 18); the 18:00 hour is still filling in, and the bar estimates
$0.62 of its own. Nothing of mine left running.

**Verified, not**
- **Verified (Modal):** one path per protocol across 200 runs (the engine's clock at the join's end, above); the table;
  the 7; the bar; tsc and oxlint on the branch's files.
- **Not verified:** the claim for ring and wo (17/20, 19/20); determinism of the join (its 2 s grow wall stays; the
  counted alternative ran once, not gated); that the rates hold on other hardware (they're fitted to Modal's containers:
  a much faster or slower machine takes the same path, but where its wall falls against the budget differs); the
  oxlint type-aware rules on the new code.

## gen/laneA: the IC3Syn suite, its failure classes, the ∃ laws' wall, counting designed (gen/laneA from main ae36917)

**The suite** (research/protocols/ic3syn/: README.md has every source, licence and commit, and each port's
correspondence). IC3Syn (arXiv 2605.24619) publishes no artifact; its 29 protocols are Endive's TLA+ benchmarks
(will62794/endive 8b6f2ab, no licence stated) and pyv-paxos-epr, whose TLA+ in Endive is faulty (`Next` calls
`Decide(n, v, r, Q)` for `Decide(n, r, v, Q)`, so no decision is ever made; `JoinRound` never leaves a round), so its
model is mypyvy's paxos_epr.pyv (MIT, 12a8f54). 26 are ported (models.ts) and 3 are not expressible in the model format
(below). Every port is checked against its source: its reachable states on a small instance, by BFS (check.ts), counted
as the spec's variables, beside TLC's distinct states on the same constants (tlc.py, TLC 1.8.0 on Modal), and its broken
variant reaching a state that breaks the property.

**Encoding findings** (README.md has them in full):
- **Quorums.** A quorum sort (Ivy's `member` with the intersection axiom) can't be written: a quorum's members read at a
  quantified key are a function read there, which kernel.ts's `keyOnly` refuses. So every quorum is a majority, stated
  exactly by counting (common.ts's `majority`: an injective rank below c on the nodes outside Q, 2c < size): every
  config's `Quorum` is the majorities of its nodes, and the ports check equal to TLC there.
- **Not expressible (3):** both learning switches (a write at every tuple of a row reads two other cells of the row: a
  join, so a key read as a function of the key, `k mod N`), and pyv-paxos-epr (`propose` reads `vote(N, MAXR, V)` with
  two of its coordinates quantified at once, which a flag's keys, each read on its own, can't). Both need keys that are
  tuples in the kernel's key rules: trusted, a Lean proof first.


**The suite, nothing written, one worker, Modal 2 CPU, the engine at ae36917** (`runs/ic3syn/a60`, `b60`, `b300` in
../gdp-wired-laneA; seconds; r1 / r2; "killed": no verdict, the job killed at 3.5 times the budget)

| # | IC3Syn name | 60 s | 300 s | class |
| --- | --- | --- | --- | --- |
| 1 | tla-consensus | proven 0.4 / 0.3 | proven 0.3 / 0.3 | |
| 2 | tla-tcommit | proven 0.6 / 0.8 | proven 0.3 / 0.6 | |
| 3 | i4-lock-server | proven 8.4 / 8.7 | proven 8.2 / 7.6 | |
| 4 | ex-quorum-leader-election | unknown 37.9 / 47.3 | unknown 48.2 / 43.2 | counting |
| 5 | pyv-toy-consensus-forall | unknown 36.2 / 44.4 | unknown 43.5 / 29.8 | counting |
| 6 | tla-simple | unknown 11.1 / 11.9 | unknown 9.4 / 11.8 | ∃ in the property |
| 7 | ex-lockserv-automaton | proven 14.9 / 10.8 | proven 11.2 / 12.0 | |
| 8 | tla-simpleregular | unknown 8.8 / 9.1 | unknown 9.1 / 10.3 | ∃ in the property |
| 9 | pyv-sharded-kv | unknown 68.0 / 68.9 | unknown 130.9 / 122.0 | the oracle's cost (5 keys, a function-valued table) |
| 10 | pyv-lockserv | proven 13.9 / 15.2 | proven 9.9 / 12.2 | |
| 11 | tla-twophase | unknown 31.6 / 31.8 | **proven 147.6 / 145.5** (9 laws) | budget |
| 12 | i4-learning-switch | not ported | | not expressible |
| 13 | ex-simple-decentralized-lock | proven 8.0 / 8.8 | proven 9.6 / 7.8 | |
| 14 | i4-two-phase-commit | proven 16.9 / 14.8 | proven 26.9 / 18.4 | |
| 15 | pyv-consensus-wo-decide | unknown 64.3 / 66.7 | unknown 283.5 / 268.1 | counting |
| 16 | pyv-consensus-forall | unknown 84.2 / 80.0 | unknown 320.6 / 320.8 | counting |
| 17 | pyv-learning-switch | not ported | | not expressible |
| 18 | pyv-sharded-kv-no-lost-keys | killed / killed | not run (the 60 s job capped) | ∃ in the property (∀∃) |
| 19 | ex-naive-consensus | unknown 65.1 / 64.6 | unknown 305.0 / 304.1 | counting |
| 20 | pyv-client-server-ae | killed / killed | not run | ∃ in the property (∀∃) |
| 21 | ex-simple-election | unknown 48.2 / 59.4 | unknown 71.0 / 53.6 | counting |
| 22 | pyv-toy-consensus-epr | unknown 53.3 / 61.2 | unknown 81.8 / 51.7 | counting |
| 23 | ex-toy-consensus | unknown 44.2 / 36.6 | unknown 43.4 / 37.0 | counting |
| 24 | pyv-client-server-db-ae | killed / killed | not run | ∃ in the property (∀∃) |
| 25 | pyv-firewall | killed / killed | not run | ∃ in the property (∀∃) |
| 26 | ex-majorityset-leader-election | unknown 58.3 / 58.9 | unknown 216.3 / 194.3 | counting |
| 27 | pyv-consensus-epr | unknown 77.0 / 74.6 | unknown 313.0 / 315.5 | counting |
| 28 | mldr | killed / killed | killed / killed (810 s) | counting (the encoding's size) |
| 29 | pyv-paxos-epr | not ported | | not expressible (and a quorum axiom) |

**Proven: 7 of 29 at 60 s, 8 at 300 s** (twophase), every proven run proven in both runs, no refutation of a port; every
broken variant the search ran on was refuted or left unknown, none proven. IC3Syn reports candidates for all 29 (its
invariants checked by TLAPS afterwards, at up to 600 s and 2 h on an M4 Pro); Endive, IC3PO, SWISS and DistAI each miss
several. So this round is not a lead: on this suite the engine trails, and the gap is two classes.

**The failure classes, by the phase that stalls** (the traces in each job's log; GDP_INFER_TRACE=2)
1. **Counting: 11 of 22 failures** (quorum leader election, the toy consensuses ×3, wo, forall, naive, simple election,
   toy epr, consensus epr, majorityset; and mldr). Each stops at the engine's round 0 with the caller's goal unsure and no
   diagram (`"caller":1,"diagrams":0`): the step goal "one leader / one value" needs "two majorities meet", which the
   oracle has no theory for (the request's majority is a rank and a bound, `2c < size`). The enumeration finds the ∀
   cubes ("a voter of a leader voted for it"), but nothing proves the pigeonhole. mldr never reaches the search: its
   first proof (proveLawsAsGiven, the kinds' laws) spends 99 s building instances of the counting witnesses' 20-odd
   quantified flags (`probe.ts mldr`: substC and stringify in flagsOf). The missing law in every case is a count: "the
   votes for v are a majority" (|{n: vote[n] = v}|·2 > size), or the ∃ form, "a decided value has a quorum all voting for
   it". The ten's toy_consensus_forall and wo prove only because their ports stand the axiom in for one stored quorum.
2. **An ∃ in the property: 6** (simple, simple regular; client-server ae and db ae, firewall, no lost keys).
   - **The top-level ∃** (PCorrect's prenex `\E i: pc[i] # "Done" \/ y[i] = 1`): the join refuses a caller law reading its
     bound value (`join failed: ... reads some$1, which it doesn't declare`), so the search runs nothing and ends in
     3–4 s; exists.ts's witness choice alone, with no ∀ support, finds none.
   - **∀∃** (`\A n, p: received => \E r: ...`): before this branch every run was killed at 3.5 times its budget: the runs
     that refute read a law with ∃ at every tuple of its keys at every state, and someHolds read the law's shape (its atoms,
     by `namesOf`'s JSON at every node) at every call (`probe.ts`, profiles in `runs/ic3syn/prof5`). Past that, the
     verdict is "no witness term found": under a `forall` exists.ts takes witness terms only, and here the witness is a
     function of the keys (the request that matched response p for n), which no term of the state names.
3. **Budget: 1** (twophase): proven at 147 s, unknown at 60 s (its join's 60 rounds at 1,996 cubes end on time).
4. **The oracle's cost on 5-key goals: 1** (sharded_kv, TLA+'s `table[n][k] = v` as a function-valued map): round 0's
   24 cubes cost 26 s and the caller's goal is unknown (the ten's relational sharded KV proves in 27–44 s).
5. **Not expressible: 3** (both learning switches, paxos), above.
- **Lane B's shape** (a map read at a key read from another map, `Tag[fp[t]]`): no measured failure here is that shape.
  mldr's counting witnesses are (`Config[i·N + In[r]]`, a carried rank read through), so with counting decided, mldr would
  meet it next; paxos's 1b messages carry a max vote read the same way.

**Attacked: the ∃ class's wall (built, general, untrusted; core/ +1,256 bytes: core/exists.ts +644, core/dsl.ts +612).**
- **someHolds reads a law's shape once** (its groups, atoms, linearity and whether it reads a map, by body and bound
  names, in a WeakMap): the runs' cost per tuple drops to the witness points' own (firewall's search, killed at 210 s
  before, ends at 149 s, unknown: "no witness term found ... under a forall").
- **The search's deeper runs stop at its wall** (`RunBudget.until`: the three deeper run sets get the search budget's
  wall time; their work cap counts a law's tuples, not the requests tried against a rule's assumption).
- **Not enough for the class:** client-server ae still ends past its wall at 60 s (a 5 s budget ends in 15 s, 60% of it
  in someHolds's witness points: every cell of every map is a candidate witness); simple and simple regular are as
  before. The class needs (designed, not built):
  - **∀∃: a ghost map,** a Skolem function the step keeps (W[n·N + p] := r where Respond(n, r, p) fires), chosen like
    exists.ts's scalar ghosts from the step's cases and the request's values; the kernel proves a plain ∀ law of the
    machine with W. Ghost.lean's `sghost_reach` is about scalar ghosts (ρ); a ghost map needs the same lemma over the maps
    (M): a lean-kernel/ statement, so it waits for a yes and its Lean proof.
  - **Top-level ∃:** the search to take such a caller law as its body over the machine with the ghost exists.ts chooses,
    chosen again with each round's found ∀ laws as support; the verdict proveRule's with the found laws, as wo's ∃ law.
- **Gates:** below.

**Ring's margin: no lever kept; the cause of its misses found (64 runs).**
- **Where ring's time goes** (bun's CPU profile, `runs/ic3syn/ringprof2`, proven at 47 s): decideLaw 37% (decide0's
  clauses: the order's transitivity triples up front and their `add`, a Set each; `hasIf`'s walks), the views' rows 13%
  (`rowsOf`, interpreted evalE), stringify 5%. By phase: the engine starts at 2.5–3.5 s, the pool's data filter ends at
  9–11 s, the enumeration at 13–16 s, top-down round 0 (44 goals) 18–22 s, rounds 1–3 10–15 s, the cone's proof 3–5 s.
- **What decides a miss** (64 ring runs at 60 s in nine batches, base and branch, and two profiled): the data filter's states. It is
  time-boxed (six times the small instance's search, at most a sixth of what is left), and a slow container reads 361–490
  states instead of 500–650; it then kills fewer cubes (left 71–88, not 68), top-down's pool is 47–61 cubes instead of
  44, and round 0 costs 23–36 s instead of 18–22: such a run ends unknown at the wall. With 44 cubes ring proves in
  39–60 s. **Main's ring today is 14 of 21 at 60 s** (ae36917, four batches: 4/4, 4/5, 5/6, 1/6), not the 51–57 s of the
  ten's earlier runs: the margin is gone on a busy day's containers.
- **Tried, not kept:**
  - the views' rows compiled to closures (`compileE`/`compileC`), the short clauses without a Set, the term walks
    without value arrays: the filter and enumeration 2–4 s sooner, but the time-boxed filter spends it reading more
    states; ring 7 of 10 proven against base's 8 of 9 in the same hours. Reverted.
  - a shorter top-down goal cap (`GDP_TD_Q1` 500 and 700 ms against 1,000): ring 0 of 12 (rounds keep 9–18 goals
    undecided, the cone never closes); distributed unchanged (4 of 4).
  - the filter's budget at ten times the small instance's search, 15 s and a quarter of what is left at most: the filter
    then reads 633–810 states and leaves 66 cubes (pool 43), but it doesn't stop once they are read: it spends its whole
    9.4–9.7 s on every container, and ring went 2 of 6 against base's 5 of 6 in the same batch (distributed 2 of 2 both).
    Reverted.
- **The lever this points to (not built):** read the larger instance's states until they stop killing cubes (a run of
  states that kill none), not until a time share, with a hard cap at three times today's: a slow container then reads
  the ~500 states ring's 68 survivors need, and a fast one stops as soon as the kills saturate. It is general (the filter
  is every engine protocol's), and the 36 runs above say which number it must reach on ring.

**Counting: a design note (nothing built).**

**The class.** A protocol's guard counts: a majority (`Cardinality(Q) * 2 > Cardinality(Node)`: quorum leader election,
the toy consensuses, majorityset, and, through the configs' Quorum, wo, forall, naive, simple election, toy epr and
consensus epr), a majority of a set that changes (mldr's `Quorums(config[i])`), two families of majorities that must
overlap (mldr's `QuorumsOverlap`), or, beyond this suite, a threshold (BFT's n > 3t, "at least n − t", "t + 1 echoes";
ByMC's threshold automata). Safety rests on one arithmetic fact, the pigeonhole: two sets each more than half of a set
meet (|A| + |B| > |U| with A, B ⊆ U ⇒ A ∩ B ≠ ∅), or its threshold forms (n − t + n − t > n + t ⇒ the overlap holds a
correct process). No EPR procedure has it; Ivy and mypyvy state it as an axiom of an abstract quorum sort, and the
ten's ports state it per protocol as one stored quorum and a witness the request names.

**What a decided theory needs.** BAPA, Boolean algebra with Presburger arithmetic (Kuncak, Nguyen, Rinard; QFBAPA is
NP-complete, Kuncak and Rinard CADE 2007): sets, their unions, intersections and complements, and linear arithmetic
over their cardinalities. A goal's sets (a request's Q, a state's row voters[n], a set comprehension `{k: P(k)}` over a
map's cells) become Venn regions, one natural for each region's size (k sets: 2^k regions, and QFBAPA's sparse models
keep that polynomial); every cardinality is the sum of its regions; the pigeonhole is then linear. Its bridge to EPR is
one rule both ways: a region of size at least 1 has a member (a fresh constant, a Skolem witness the EPR part reads), and
a member puts its region at 1 or more. Threshold automata (ByMC: Konnov, Veith, Widder) are the other road, for
counters of processes in local states with parameterized thresholds; this suite's counts are of sets, and BAPA is the
nearer fit.

**Where in the oracle.** kernel/epr.ts's decideLaw already has the parts: a CDCL search over the EPR abstraction, a
theory check by simplex (`theoryCheck`) whose refutations come back as lemmas (DPLL(T)), and the kernel's exact sums
(`M.sum()`, sumMachine, Sums.lean) for a map's total. The counting theory would be one more theory beside the order:
- **Recognise** a count: a sum over a 0/1 map's cells under a condition (`M.sum(c => ...)`), common.ts's injection
  witnesses (an injective rank below c bounds a set's size), or a new DSL form `Q.size()` for a carried set (no
  witnesses for the writer to give, the runtimes compute it).
- **Name** each set the goal reads and its regions; add each region's size as a theory term, each cardinality as their
  sum, the regions nonnegative.
- **Bridge** at the abstraction: a region asserted nonempty gets a witness constant whose membership literals join the
  CDCL clauses; a model's members lift the regions' lower bounds.
- **Check** the model in simplex with the order's and the counts' comparisons together; a refutation's lemma names the
  regions it reads.
- **The search side** needs nothing new to find the laws: the engine's small instances count exactly (they run the
  step), so the cubes "every voter of a leader is in its quorum" or "a decided value's quorum all voted for it" are
  enumerated already. What fails is the goal they lead to: the pigeonhole inside the step, which this theory decides.
- **The ∃.** The laws these protocols need are ∀∃ ("a decided value has a quorum all voting for it"): a quorum is not a
  state term. Two routes: the engine's ghost (core/exists.ts, as wo's ∃ law) keeps a quorum per decided value, its
  witness a set (a ghost map, not a natural); or a law over the counts instead ("the votes for v are a majority",
  |{n: vote[n] = v}| * 2 > size), which is ∀ only and BAPA-decidable. The second fits the oracle above with no ghost
  of a set and is the one to try first.

**Does it need a new certificate kind?** Yes. The kernel's certificates (kernel.ts, checked by checkLaws and by the
Lean twin) carry EPR trees and linear arithmetic over terms, and sums kept exact by the step (Sums.lean). A counting
step's proof is a Venn decomposition plus a linear certificate (Farkas coefficients over the regions), and its
soundness is a lemma about finite sets, not about the step: for 0/1 maps A, B ≤ U, Σ A + Σ B > Σ U ⇒ ∃k. A[k] = B[k] =
1 (Finset.card_union_add_card_inter), and its general form, a region's sum is the sum of its cells. Two ways in:
1. **A lemma kind:** the certificate cites a library lemma of the Lean twin (stated once, proven once, in lean-kernel/,
   say Count.lean), with its instance (which maps, which bounds); kernel.ts checks the instance's shape and the linear
   part as now. The trusted statement grows by one lemma and one checker case: its soundness proven in the twin first,
   and only after asking.
2. **No new kind, a ghost instead:** the engine adds, per protocol, the exact sums the pigeonhole reads as state
   variables (`Votes.sum(c => c.eq(v + 1))` per value is not one sum; a sum per value is a map of sums, which the
   kernel doesn't keep), and the linear certificate over them does the rest. That covers a fixed number of sets only
   (2PC's yes count, one leader's votes), not "every value's votes", so it is the narrower road.

**Order of work, when it is built:** (1) the `size()` form and its runtime, with the BFS check of this suite's ports
against TLC (check.ts) unchanged; (2) the theory in decideLaw behind a flag, measured on the majority protocols' goals
(their dumps, as wo's referee set) against Z3 with its cardinality encoding as the referee; (3) the lemma kind and its
Lean proof, asked for first; (4) the suite again.

**Gates** (the branch's engine change is core/exists.ts and core/dsl.ts above; the rest of the branch is research/):
- **The ten twice at 60 s** (`runs/ic3syn/ten-final`, beside main's `ten-base1`): nine of ten proven in both runs at
  main's times (sync 8.0 / 9.8 s, async 25.4 / 24.0, decentralized 17.2 / 18.0, 2PC 20.6 / 11.8, ticket 35.0 / 35.0, toy
  11.7 / 10.0, distributed 32.5 / 37.9, wo 45.2 / 40.6, sharded 27.0 / 32.1); ring 1 of 4 there, and across three batches
  paired with main in the same minutes 5 of 15 against main's 10 of 17: every miss on either side is a filter that read
  fewer than ~500 states (above), which neither change touches (no ∃ law in ring, and its deeper runs end well inside
  their wall), so I read it as the containers', not the change's; it is the weakest point of this gate.
- **The quick bar** (`--quick --cand gen/laneA --base ae36917 --only rw,f1,f2,g332,suite,onecpu` on d5a3e5d, against the
  shared baseline; <main>/runs/bar/runs/d5a3e5d55b61-vs-ae369178e65d-quick-2026-10-301731/REPORT.md, 649 s, estimated
  $0.63): f1 34 and f2 24 as the base (no task differs); rw 74/14/3 as the base; g332 the same search on 332 of 332
  (300.2 s against 286.6 s); onecpu no failure; the suite 234 of 235, **lost 1**: `check` (tsc and oxlint over the
  repository), from an unused binding in research/protocols/ic3syn/models.ts, fixed in 9f360d4 (oxlint clean on the
  branch's files); the suite group again on 9f360d4 (<main>/runs/bar/runs/9f360d480880-vs-ae369178e65d-quick-2026-10-301744): 235 of 235,
  lost 0. Gained 0, wrong 0; core/ and kernel/ +1,256 bytes.
- **Typecheck:** clean for every file the branch touches (`tsc -p .` on Modal; the errors left are vendor/ imports and
  research files the branch doesn't touch, as on main's tree there).

**Spend:** $2.25 billed through the 17:00 UTC hour for this round's apps: $1.18 for the 34 of the checks, the suite's runs,
  the probes and the ring batches, and $1.07 for the two bars' 20 (both sides); the last hour may still be filling in.
  Nothing of mine is left running. Two jobs were capped and not rerun (mldr at 300 s, twice, 810 s each: no verdict, as
  at 60 s; launched before the 60 s cap was seen).

**Verified, not**
- **Verified (Modal, as counted above):** the sources and their commits; 25 of 26 ports equal to TLC in states on their
  instances (consensus_wo_decide at its config's three quorums), their broken variants reaching a bad state where the
  BFS finished; the suite table (two runs each, 60 s and 300 s); the failure phases from each run's trace; the profiles;
  the ring measurements; the ∃ fix's effect on firewall.
- **Not verified:** mldr's port (README.md: its counts differ from TLC's and its broken variant finds no bad state);
  pyv-sharded-kv-no-lost-keys, client-server ae and db ae, firewall at 300 s (not run: their 60 s jobs were capped);
  that the 1,996-cube join of twophase or the ∀∃ ports' witness search behave the same on other instances; IC3Syn's own
  numbers (no artifact); the counting and ghost-map designs (nothing built); that the branch's ring misses are noise
  (5 of 15 against 10 of 17 is not significant, p ≈ 0.16, nor shown to be nothing).

## gen/lean10, the `found` fix: all ten verdicts checked by Lean (gen/lean10, merged with main f0526b6)

**Built (core/infer.ts, +0.6 KB, untrusted):** the engine's ∃ law (its ghost's, `ghost.some`) is reported in `found`
beside the cubes wherever the engine's final set proof read it: the top-down cone, the IC3 cone, the Houdini pass and
the set's proof (`enumSome`). A verdict's laws now prove again as they are.

**wo through Lean from its own verdict, no stand-in** (`runs/lean10/wo4`, `suitejobs`; three runs)

| run | search | found (∃) | proven again, search off | exported | Lean-checked |
|---|---|---|---|---|---|
| wo4 r1 | 41.0 s | 20 (1) | yes, fast set proof, 1.2 s | yes (fast trees, Ghost.lean), 78.6 s, 612 KB | yes, 71 s |
| wo4 r2 | 37.5 s | 24 (1) | yes, the default proof with its certificate, **779 s** | yes, 82.5 s, 774 KB | yes, 44 s |
| suite job pilot | 41.4 s | 20 (1) | | yes, 78.8 s, 626 KB | yes |

Every theorem (the laws and the ∃ statement `consensus_wo_decide.someN`) depends on [propext, Classical.choice,
Quot.sound] only; no sorry. So all ten protocols' verdicts are now checked by Lean (the nine of the table below, and wo).
- **A caveat, not fixed:** re-proving wo's verdict with `proveRule(r, [...laws, ...found], {search: false})` (the default,
  the usual proof and the cyclic certificate over the ghosted machine) proves it, but in 13 minutes; with `{fast: true}`
  in 1.2 s. It is the cost noted for the usual route on wo's sets (its exporter fallback above); the README's
  "pass it with the rule's laws" works, slowly, by default.

**The ten once at 60 s with the fix** (`runs/lean10/ten`, merged tree): all proven. sync 10.8 s, async 23.9, decentralized
18.8, 2PC 15.3, ticket 36.8, toy 12.2, distributed 39.8, ring 57.3, wo 47.7, sharded 27.6. No verdict moved.

**The quick bar** (`--quick --cand gen/lean10 --base 5d4da3f --only rw,f1,f2,g332,suite,onecpu`, on 7a96b6b: the found fix
merged with main f0526b6; <main>/runs/bar/runs/lean10-7a96b6b-quick/REPORT.md, 577 s, estimated $0.58): f1 34 and rw
74/14/3 as the base; f2 24 against 24.33 (no task differs); g332 the same search on 332 of 332 (299.0 s against 298.3 s);
the suite 233 passed, 0 failed; onecpu no failure. Gained 0, lost 0, wrong 0.

**Two suite jobs** (modal/suite.json, added after the bar's tree, piloted alone in `runs/lean10/suitejobs`):
`lean-protocols-sync` (28 s) and `lean-protocols-wo` (176 s): lean10.ts's search at 60 s (twice at most), export, `lean`,
failing on an export error, a Lean error, a sorry or an axiom past the core three. wo covers both new routes (the ∃ law in
`found`, the fast-proof fallback). The other eight run 1–20 minutes each (distributed 10, sharded 20): a separate gate,
`modal run modal/run.py --jobs research/protocols/jobs-lean10-final.json --out <dir>` (about 40 container-minutes).

## gen/lean10: the ten's final proofs through the Lean twin (gen/lean10 from main 4e9d7ec)

**The question.** The README says every proof is checked again by Lean. The engine's verdicts are the fast set proof's
(proveSetFast, its trees checked by kernel.ts's checkLaws), which no Lean job had read. So, per protocol: the search at
60 s, then its law set (the kinds', the caller's and every law in the verdict's `found`) exported through the suite's
Lean path (lean-kernel/emit.ts's `toLean`, cyclic certificates where the cyclic route covers the machine, else the usual
trees) and checked by `lean` against the twin (Lean v4.34.0, the library as `modal/run.py` caches it). The harness is
research/protocols/lean10.ts; runs are `runs/lean10/*` in ../gdp-wired-lean10 (Modal, 2 CPU, 8 GB).

**On main's exporter** (`runs/lean10/pilot`, `all`): 8 of 10 exported and checked; two not exportable.
- **ring:** `toLean` re-proves the set the usual way (proveStepLaws), and the usual proof fails on ring's found set
  (`smachineToLean`: "not proven", after 28 s). The verdict was the fast proof's (per-law instances of each law's sort);
  the usual instances don't prove it.
- **wo:** the verdict's `found` has the 19–25 cubes but not the ∃ law its proof used (the engine's ghost law,
  `ghost.some`): `chosen` holds forms only, and the ghost lives inside the engine. The found set alone is not inductive,
  so no prover can export it; this is the search's report, not the exporter.

**The exporter fix (lean-kernel/emit.ts only, +1.4 KB):**
- `proveStepLawsOnce`, with no step laws and no ∃ law: the usual proof within 60 s of wall (`GDP_LEAN_USUAL_MS`), then,
  where it fails, the fast set proof's own proof (its per-law instances and trees, checkLaws-checked) as the proof the
  export reads (`certReport.fast`). Lean checks those trees as it checks any; nothing trusted changes.
- An item with an ∃ law: its witnesses chosen with `proveSetFast` first (proveSome over the ghosted machine, as the
  search proved it), else proveStepLaws as before. (wo's ghosted set ran the usual proof 8 minutes and more.)

**Final, every verdict from main's search and the fixed exporter** (`runs/lean10/final`; search at 60 s, each proven at
its first try; Lean `decide +kernel`; every theorem's `#print axioms` is [propext, Classical.choice, Quot.sound]; no sorry)

| protocol | search | found | exported | route | export | Lean-checked | Lean |
|---|---|---|---|---|---|---|---|
| sync | 8.5 s | 1 | yes | cyclic certificate | 0.9 s, 120 KB | yes | 9 s |
| async | 22.9 s | 11 | yes | cyclic certificate | 7.0 s, 583 KB | yes | 50 s |
| decentralized | 15.2 s | 2 | yes | usual trees (sums) | 2.4 s, 525 KB | yes | 46 s |
| 2PC | 22.4 s | 14 | yes | usual trees | 18.3 s, 591 KB | yes | 46 s |
| ticket | 29.9 s | 12 | yes | cyclic certificate | 4.2 s, 384 KB | yes | 30 s |
| toy | 12.5 s | 6 | yes | usual trees | 26.5 s, 1.5 MB | yes | 114 s |
| distributed | 31.2 s | 27 | yes | usual trees | 31.9 s, 5.9 MB | yes | 564 s |
| sharded | 28.4 s | 16 | yes | usual trees | 69.9 s, 9.5 MB | yes | 1,189 s |
| ring | 57.1 s | 18 | yes (fix) | the fast proof's trees | 42.1 s, 1.8 MB | yes | 88 s |
| **wo** | 45.6 s | 24 | **no** | (the verdict's set lacks the ∃ law) | | **no** | |
| wo, with the written ∃ law as a stand-in | | 24 + 1 | yes | the fast proof's trees, Ghost.lean | 97.1 s, 757 KB | yes | 57 s |

("usual trees": the cyclic certificate past its 10 s deadline, so the usual trees are exported; a one-file `lean`
check, single-threaded.) The stand-in is the written "after init the voting quorum has a member", whose witness is the
engine's ghost (`(inits ∨ chooses) ? w : before`); it shows the Lean path covers the shape (Ghost.lean's ∃ statement
`consensus_wo_decide.some25` checked), not that wo's verdict is checked.

**What wo needs (proposed, not built: it is the search's report, core/infer.ts, not the exporter):** the ∃ law the
engine's final proof used in its `found`. About 0.4 KB: an `enumSome: Law[]` beside `enumProof`, set to `ghost ? [ghost.some]
: []` wherever the engine sets `enumProof` from a set with the ghost (the top-down cone, the IC3 cone, the Houdini pass,
the set's proof), and the return's `found` with `{law, text: law.name}` for each. Untrusted (a verdict's report); then
`proveRule(r, [...laws, ...found])` proves again, and the export above (the stand-in's route) applies as is.

**No regression:** the bar's suite group on 9bc1776 (`--quick --only suite` against the cached 5d4da3f, its 63 Lean
and ∃ jobs among the 233; <main>/runs/bar/runs/lean10-9bc1776-suite/REPORT.md): 233 passed, 0 failed; gained 0, lost 0,
wrong 0. lean-kernel/emit.ts is the only file of core/, kernel/ or lean-kernel/ changed (+18 −5 lines); no trusted
statement and no Lean file changed.

**Spend:** $1.13 billed by 14:03 UTC for this round's 10 apps (8 of the Lean runs, 2 of the bar; the bar's own $0.39);
the 14:00 hour is still being billed. Nothing left running.

**Verified, not**
- **Verified (Modal):** the table; 9 of 10 verdicts checked by Lean, with core axioms only.
- **Not verified:** wo's own verdict in Lean (it can't be exported until `found` carries its ∃ law); `native_decide`
  (not used: `decide +kernel` throughout); other runs' found sets (one run each here, ring's earlier run unknown at
  59.9 s and retried).

## gen/wo: wo proven with nothing written at 60 s (gen/wo from main 9c07baf; the ten proven in every run)

**Where it stands.** consensus_wo_decide is proven with nothing written at 60 s in 5 of 5 runs on the final code (35.6,
40.8, 52.3 s in `runs/engine/wo-w3`; 42.1, 48.5 s in `wo-ten`), and the ten are proven in both runs of `wo-ten`. All of
it is untrusted search: the verdict is still the fast set proof's (`prove(…, true)`: proveSetFast, its trees checked by
kernel.ts's checkLaws), now through core/exists.ts's ghost for the ∃ law. kernel/kernel.ts and lean-kernel/ are
untouched; no new certificate kind. Runs are `runs/engine/wo-*` in ../gdp-wired-wo (Modal, 2 CPU).

**The probes** (research/protocols/engine): `wodl.ts` (decideLaw on wo's written laws, `given`; the ∃ law's ghost form,
`ghost`; the written set's whole proof, `set`; a dump's goals again, `replay`, with `WO_Z3=1` asking Z3 too), `wodump.ts`
(a search run with every decideLaw goal written out, `decideLawHook`), `z3ref/` (exp/z3's translator, copied as a
referee only: added per job by `bun add z3-solver`, never imported by core/ or kernel/), `profwin.py` (a CPU profile's
functions between two times). `dumps/wo-td-base.jsonl.gz` (not committed) is the referee set: the 143 goals of a
`GDP_TD=1` run at 120 s on 9c07baf, each cube's step with 104–107 laws assumed.

**Pilot (3), the reason probe: the premise didn't hold on main.** On 9c07baf, decideLaw decides 10 of wo's 11 written
goals in 31–550 ms, "nothing before init" proven in 132 ms. The "every goal undecided" of the note was exp/pool-z3's
older decideLaw. What it got wrong or left open, each found by the probe and fixed (kernel/epr.ts, kernel/prove.ts,
untrusted):
1. **A diagonal key** (`VoteMsg[64·x + x]`, every cube over one node) was no tuple (`tupleOf` refused a name twice): the
   conclusion "not EPR-shaped". Now the tuple (x, x).
2. **A read at an if-key**: the ghost's law reads `VotingQuorum'` at the ghost's own next value, `(inits ∨ chooses) ? w
   : y`. Now `M[c ? a : b]` reads as `c ? M[a] : M[b]` (an if in the key's sum lifted first; at most 8 keys a read), by
   term equality, before the abstraction.
3. **The carried map in the model's state**: modelInstances built its state from the machine's maps only, so `Q` read 0
   and `quorumVotes`' ∀ (∀k. Q has k → Votes[src, k]) was never instantiated where the model breaks it. Now the request's
   maps are read too. This is the note's "a ∀ flag's true side at ground keys"; its 0 side (the witness `w?f`) and the
   pattern for `Q` ([1]) were already there, and the write at every key is already an if at each ground key in the
   kernel's goal; the missing piece was 2.
4. **A stale model**: a later round that refuted the goal (with the model's instances) but whose core the kernel's
   search didn't prove returned the earlier round's model ("a leader has the voting quorum's votes": a model, Z3
   proves it). Now no answer, and `decideNote.refuted` tells the caller (below).
5. **Whole keys of one shape sorted apart**: `bySort` took a composed term as the whole key of the first map with its
   pattern (`K:Votes`), so an instance of "every VoteRequestMsg cell is a value of its kind" there was filtered, and the
   model rounds asked for it again until the cap. Now two maps of one pattern whose parts are of one sort have one
   whole-key sort; and a model whose only broken instances are another sort's is no answer (not asked again).
6. **Unconfirmed models**: decideLaw is now strict always (a model only where its round found no instance to add;
   `GDP_STRICT=0` the old way). Decentralized lock, the case that kept it off, is 15.6–19.3 s with it.

**Pilot 1, measured on the 143 referee goals at 1 s** (Z3 at 2 s as referee; "wrong": decided otherwise than Z3)

| code | undecided | wrong | decided by both |
|---|---|---|---|
| 9c07baf (`wo-base`) | 98 | 21 | 45 |
| 1–4, non-strict (`wo-p5`) | 3 | 43 (unconfirmed models at the deadline) | 140 |
| 1–4, strict (`wo-p8`) | 94 | 1 | 49 |
| 1–5, non-strict (`wo-p10`) | 8 | 18 | 135 |
| final, 1–6 (`wo-p12`, `wo-final`) | 20, 22 | **0**, **0** | 123, 121 |

- The written set's 11 goals: 9c07baf 1 wrong (the voting quorum's law: a model); final 1 undecided, 0 wrong. That
  goal's EPR core is 14 hypotheses, and the kernel's search proves it in 10 s of counted work (2.1 s wall locally),
  past decideLaw's 2 s; Z3 decides it at once. It is the kernel's cost on radix-key congruence, not the oracle's.
- Mean decideLaw time 444 ms before, 559 ms after (the 2,400 hypotheses a goal it left out as unshaped are in now).
- **PASS** on the criterion (0 wrong; undecided 98 → 22).

**Pilot (4) and step 2, the ∀∃ law in its ghost form: PASS.** The engine already asks the ghost's plain law over
`withGhost` (`ghost.plain`); it was undecided (the conclusion not EPR-shaped, 8 ms). With 2 it is proven in 26–67 ms
with the written ∀ laws assumed (no model, so no witness gap), and the caller "one leader" proven with it in 126–178 ms.
Z3 agrees on both.
- **The set's proof with the ∃ law**, which was the 30.5 s wall: `proveSetFast` went to `proveLaws` for any ∃ law, so
  proveSome's whole set got the usual proof and the cyclic certificate. Now proveSetFast calls proveSome with itself as
  the whole set's prover (`whole`), over proveSome's ghosted machine. The written set: **1.8 s against 33.7 s** (7.4 s
  usual, 26.1 s certificate; `wo-p9`). The verdict is checked as every engine verdict is (checkLaws), with the ghost's ∃
  certificate as before.

**Step 3, wo end to end** (`wo-p3` … `wo-w3`; times are seconds into the run)
- **Before:** the engine starts at 31–40 s (the join 17 s, of it one query of 12–16 s: "every k: Leader[k] <=
  VoteRequestMsg[k]", unknown), the IC3 rounds' cube goals 0.3–2 s each, the set's Houdini drops one cube a proof.
- **The cone first (core/infer.ts, IC3 rounds):** once the caller's goals and the ghost's are proven in a round, the
  cubes their proofs read (decideLaw's `uses`), closed under each cube's own, are asked first, and the cone proven whole
  (fast). A cube with a model there, or the one the cone's proof fails at, is left out and the caller asked again
  (Houdini over the cone, 6 times); a proof ends the rounds. Its decisions stay in the memo for the round after it.
  `GDP_IC3_CONE=0` off. wo: proven at 46.9 s (cone 23 of 46) the first time; then 2 of 3 (62.1 s, past the wall; 59.0 s;
  unknown), the misses a cone cube with a model (now left out) and a late engine.
- **The join's usual search on the wall where the engine follows** (`joinGrowWall`, 2 s): the proving joins' searches
  take under a second (decentralized's sums pass needs 0.7–0.8 s; sync, async, 2PC and ticket prove with it on), and
  wo's unknown one ran 13 s. The engine then starts at 21–26 s. **wo: 3 of 3** (35.6, 40.8, 52.3 s).
- **Smaller:** realCti's pre-state rows once, not once per cube (16% of the rounds' profile); the rounds' CDCL search
  after an undecided cube on the wall too (a counted 2 s ran 8.8 s); a cube the abstraction refuted with a core the
  kernel didn't finish is unsure at once; `matched`'s wholeness once per match (the instances' 8%).
- **Where the time goes now** (`wo-p14` profile of the rounds): decideLaw 61% (its instances 27% of that), the CDCL
  search after undecided cubes 23%, the pool filter's tail 8%, blockers 6%. wo's margin is the cone's: 9–18 s from the
  caller's first proof.

**Step 4: the ten twice at 60 s** (`wo-ten`, final code f6a22a8)

| protocol | run 1 | run 2 | before (r7a: gen/ring3's wired tree, 9c07baf's code) |
|---|---|---|---|
| sync | 8.9 | 8.2 | 6.8 / 8.5 |
| async | 24.4 | 20.1 | 25.5 / 20.8 |
| decentralized | 15.6 | 19.3 | 18.2 / 18.3 |
| 2PC | 19.7 | 17.3 | 22.1 / 11.6 |
| ticket | 29.7 | 39.2 | 32.7 / 36.5 |
| toy | 12.1 | 10.3 | 12.1 / 11.7 |
| sharded | 31.5 | 34.8 | 27.3 / 26.0 |
| distributed | 35.6 | 34.5 | 42.2 / 30.6 |
| ring | 51.3 | 52.1 | unknown / 46.0 |
| **wo** | **42.1** | **48.5** | unknown 65.3 / 64.4 |

All proven, both runs (and `wo-t1`, one run with the join traces: nine proven, ring 53.2 s, wo unknown before the cone).

**The quick bar** (`--quick --cand gen/wo --base 5d4da3f --only rw,f1,f2,g332,suite,onecpu`, against the cached
5d4da3f49013-modal-r1, on f6a22a8; <main>/runs/bar/runs/wo-f6a22a8-quick/REPORT.md, 484 s, estimated $0.58)
- f1 34 and rw 74/14/3, the same as the base;
- f2 24 against 24.33 (no task differs);
- g332 the same search on 332 of 332 (282.1 s against 284.1 s);
- the suite 233 passed, 0 failed; onecpu no failure.
- Gained 0, lost 0, wrong 0.

**Bytes:** core/ and kernel/ 4,175,571 against 4,165,113 at 9c07baf (+10,458): kernel/epr.ts +3,259, kernel/prove.ts
+2,929, core/infer.ts +3,956, core/exists.ts +314. The typecheck has no error in core/, kernel/, research/protocols or
gates/ (the vendor modules the Modal image leaves out are the only errors, as before); lint clean but for
research/hw/run-more.ts (as on main).

**Verified, not**
- **Verified (Modal):** every number above; wo proven at 60 s in 5 of 5 final runs; the ten twice; 0 wrong on the 143
  referee goals and the written set.
- **Not verified:**
  - the Lean twin on these verdicts (the fast set proof's checked trees, as for ring's and distributed's; no cyclic
    certificate is made in the search);
  - "0 wrong" beyond wo's goals (the referee set is wo's alone);
  - the join's wall cap beyond the ten and the bar's dev sets;
  - wo past 60 s on slower containers (its latest finish 52.3 s);
  - the voting quorum's law's own step: still the kernel's 10 s counted core; the cone proves without asking it apart.

**Spend:** $0.85 billed by 12:18 UTC for this round's 35 apps (23 of the probes and runs, 12 of the bar); the 12:00 UTC
hour is still being billed, so about $1.4 in all with the bar's estimate. Nothing of mine left running.

## gen/ring: the two pilots for ring (from main a095ae3; nothing built)

The pilot code is on exp/pool-z3, since both pilots use its Z3 dump and replay. It adds `GDP_CONE_PILOT` and
`GDP_EPR_WHY` (each EPR decision's outcome, ms and size, and its ordered terms' classes), plus `withWallAt` for the
pilot's own wall. Runs are `runs/engine/rg1`–`rg4` in ../gdp-wired-poolz3, Modal 2 CPU.

**Pilot 1, cores for the cone cut: FAIL.**
- **The setup:** ring's IC3 set with the filtered pool and Z3 (`GDP_POOL=ic3 GDP_Z3=ic3`, 60 s) ended at 29 cubes,
  with all 5 probe-proven cubes in it.
- **decideLaw at 5 s per goal, the whole set assumed** (a wall of its own past the search's): 104 s for 30 goals.
  - 11 proven;
  - 6 models, 5 of them at the 5 s deadline;
  - 13 undecided.
- **The caller** ("one leader") is proven from 4 cubes. That is the cone, well under 30. But 3 of the 4 are undecided,
  so their own support never joins.
- **`prove()` of the 4-cube cone** fails in 1.35 s at "Leader[x] ∧ Pending[idn(y), y]" @step.
- **The caller's support isn't the probe-proven 5.** The proof routes through other true cubes whose own goals
  decideLaw can't settle.
- So the cone cut needs an oracle that decides ring's goals. It depends on pilot 2; on its own it isn't built.
- A first run of this pilot returned in 1–2 ms a goal: it ran after the search's wall, which `withWall` keeps (it takes
  the smaller of two walls). Rerun with its own wall.

**Pilot 2, ring's ordered successors and the injective `idn`: the goals become decidable with time (PASS on its
criterion); the mechanism I designed is falsified as the cause.**

**Replay of ring's 44 top-down goals** (round 0, the 44-cube shrunk pool assumed; `z3probe.ts replay`)

| per goal | decideLaw undecided | decideLaw mean | Z3 undecided | Z3 mean | decideLaw's model against Z3's proof |
|---|---|---|---|---|---|
| 1 s | 39 of 44 (40 in rg4) | 1.01 s | 15 | 0.52 s | 0 |
| 5 s | 11 (18 in rg3) | 3.2–3.6 s | 0 | 0.89 s | 4–5, all at the 5 s deadline |
| 20 s | 5 | 7.1 s | 0 | 0.90 s | 2, both at the 20 s deadline |

- **The unknown reason at 1 s:**
  - 35 of the EPR decisions end "past the deadline" (median 875 ms);
  - 53 are unsat, median 21 ms;
  - no goal is out of the EPR shape.
- **At 5 and 20 s:**
  - the sat decisions take 2.0–2.8 s at the median (up to 11.5 s);
  - 4 at 20 s end in "no values for the model's order";
  - the disagreements are decideLaw's models returned unconfirmed at its deadline (settle's late exit, recorded before).
- **So it's cost, not incompleteness.** By 20 s decideLaw decides 39 of 44 and Z3 all 44, at 7× decideLaw's speed.

**Where the time goes** (bun's CPU profile of the 5 s replay, 197 s, `rg3`)
- `decide0` is 92% of decideLaw's time; the core's proof by `grow` after an unsat, 3%.
- Inside `decide0`:
  - the theory check (`theoryCheck`, simplex) 30%;
  - the order's atoms 17% (`atom` self time, a Map lookup by text, from `le` in the order's axioms);
  - the CDCL search 15%;
  - the literals and comparisons 9%;
  - text keys (`stringify`) 7%;
  - building the solver 5%.
- **The order's axioms are cubic:** every pair of ordered terms is total, and below 65 terms transitivity is every
  triple up front (`!lazy`). Ring's goals have a median of 28.5 ordered terms (60 at most; up to 195,112 transitivity
  clauses).

**The follow-up (`rg4`): would sorts split that order?**
- The hope: Ivy's sorts, separate orders for node keys and ids, as Z3 had.
- **No.** In 86 of 88 decisions all non-constant ordered terms are one class: union over every pair the hypotheses
  compare or equate, and every successor. The median split of the transitivity triples is 1.0.
- The likely reason, not yet checked: `lawInstances` seeds each law's keys with every key the goal reads (`readKeys`),
  of any sort. An instance then puts a node where a law has an id (Pending's first part), and the comparisons it brings
  join the two orders.
- Z3 instantiated per sort (its quantified laws over uninterpreted sorts), which kept them apart.

**What it means for the plan**
- The successor and injectivity encoding I designed doesn't address the cost: neither appears in the profile.
- The cost is the one order over every ordered term, cubic in its axioms, with the theory check on top. It is that
  size because the instances aren't sorted.
- **The next pilot (cheap, not run):** in `lawInstances`, seed a law's key only with keys of its sort.
  - Use the union-find over key places that core/infer.ts's `keySorts` already does.
  - Count, on ring's 44 goals, the instances, the ordered terms, the classes and the 1 s and 5 s decisions.
  - **Passes if** ordered terms halve or split into two classes, and the 1 s undecided count falls below 15 (Z3's).
- **The risk:** in the kernel's semantics keys are naturals, so a proof may need an instance across sorts. As an
  untrusted oracle that only costs a decision, and `prove()` still checks the set over its own instances.
- Pilot 1 is worth rerunning only after that.

**The per-sort seeding pilot: FAIL** (`runs/engine/rg5` in ../gdp-wired-poolz3; the code is `bySort` in kernel/prove.ts on
exp/pool-z3, behind `GDP_SORTED=1`)
- **What it does:** each law's keys, and each quantified flag's, are taken only at keys of their sort. It applies to
  `lawInstances` and to the model rounds' `modelInstances`. Untrusted instancing; no checking touched.
  - The sorts are a union-find over:
    - each part of a map's key, by its pattern;
    - a map's whole key;
    - a function's argument and its value;
    - every name, with a law's own keys and a flag's bound keys local to it;
    - any two names one comparison relates.
  - A key term whose sort is anchored (to a map's part or key, or to a function) and differs from the law key's anchored
    sort is left out.
- **On the same 44 ring goals at 1 s, against the same dump run without it:**

| | instance keys | ordered terms (median, max) | decisions in one class | decideLaw undecided | against Z3 |
|---|---|---|---|---|---|
| unsorted | 684,228 | 24, 60 | 61 of 87 | 43 | 0 disagree |
| sorted | 313,388 (−54%) | 28.5, 60 | 62 of 88 | **29** (Z3: 15) | 0 disagree |

- **So:** fewer than half the instances, 14 fewer goals undecided, and no wrong verdict. But the ordered terms don't
  halve, the order doesn't split into classes, and 29 goals stay undecided, against the pass mark of 15.
- **The cross-sort instances weren't what joins ring's order into one class.** What does join it is not yet known. The
  next thing to read is one goal's comparisons: which hypothesis relates an id term to a node term (a frame's `x <
  size` at an unanchored key, the theory's rows, or the parts' equalities).
- **Not built, as the order said.** The strict deadline rule (unknown in place of an unconfirmed model at decideLaw's
  deadline) is not included either: timeouts are still the common case (29 of 44 at 1 s), and the order made it
  conditional on per-sort seeding making them rare.
- **Spend this round:** $0.07 billed for 5 apps; the hour is still being billed.

**The trace: what joins ring's order** (`runs/engine/rg6`–`rg8`; `GDP_EPR_TRACE` on exp/pool-z3. Each ordered term's
anchors are read from the goal's reads (a map's key part, `idn`'s argument or value), then the hypotheses' related pairs
are unioned in order. Goals 7, 11 and 16 of the 44, all undecided at 1 s, three of them Z3 proves.)
- **The first decision of each goal** (17–22 ordered terms) already has the two sorts apart: ids with `m`, and nodes with
  `size`. Goal 16 is the exception: a comparison in hypothesis 170, `idn(key1) ≤ key3`, where key3 is a law's key at
  Pending's id part.
- **The second decision** (44–59 terms, after a model round) has every term in one class. There, `idn(n)` and `m` are
  read at Leader's key, a node place, and `idn` is applied to whole Pending keys: `idn(64·m + n)`, nested
  `idn(64·idn(64·m + n) + …)`.
- **The source** (`KEEP` trace of `bySort`): node-keyed laws instantiated at whole composed keys. "One leader", the cubes
  and the kinds' laws were taken at `64·m + n`, `64·idn(n) + n1` and their nests.
  - The per-sort filter kept them, because a composed term that no read names literally had no sort (`of` returned
    nothing, and nothing means keep).
  - The candidates named earlier were a frame's `x < size` at an unanchored key, the theory's rows, and key-part
    equalities. It is the third: whole keys used as parts. The theory's rows and the frames follow from it.

**The narrowest fix** (untrusted instancing only): a composed term (several parts, or a part under a factor) is a whole
key, of the map whose pattern its factors are, or of no map. So it never takes a part's place.
- **Two bugs the regression check found in the sort analysis itself** (toy consensus lost its proof, then got it back):
  - a write's key wasn't read as a key (`Decided.set(v)`: v is a value);
  - a write at every key of a one-part map named its binder by the map's whole key, not its part.
- **Kept with it:** decideLaw's strict models. A model is returned only where confirmed: no model at the deadline,
  past the instance rounds, or when its only broken instances are another sort's.
- **Narrowed when built:** on gen/ring, the sorts apply to decideLaw's instances alone (`settle` with `usual` false).
  The usual path's `lawInstances` is unchanged: with it filtered too, toy's join (before the engine) slowed from 7 to 56
  s.

**The 44-goal pilot with it: PASS** (`rg9`, `rg11`, `rg16`; the same dump as rg5)

| at 1 s | instance keys | ordered terms (median, max) | decideLaw undecided | wrong against Z3 at 10 s |
|---|---|---|---|---|
| before (no sorts) | 684,228 | 28.5, 60 | 40–43 | 0 |
| sorts with the fix, not strict | 327,537 | 22, 25 | 2 | 1: goal 27, a model where Z3 proves it, from past the instance rounds (5.1 s at 10 s) |
| sorts with the fix, strict (final) | 310,893 | 22, 25 | **9** (Z3: 14) | **0** |
| the same at 10 s | | | 1 | 0 (34 proven, 9 models, all as Z3's) |

- **Against the pass mark:**
  - the largest goal's order halved (60 to 25 ordered terms); the median fell 23% (28.5 to 22);
  - the classes still don't split (one class in 118 of 144 decisions): ids and nodes share `size` and the comparisons
    between them;
  - 9 undecided against the mark of 15;
  - 0 wrong.
- decideLaw's mean at 1 s is 0.55 s against Z3's 0.51 s.

**Built** (gen/ring 63bed40, kernel/prove.ts only, +94 lines, about 7 KB; `GDP_SORTED=0` and `GDP_STRICT=0` turn
each off; untrusted, no checking touched)
- **The ten, once** (`runs/engine/gr6`): the eight proven (sync 8.5 s, async 23.7, decentralized 36.0, 2PC 21.9, ticket
  30.2, toy 14.7, sharded 33.2, distributed 33.9); ring and wo unknown.
  - decentralized's 36 s is above its earlier 13–32 s, one run. Not checked again.
- **Ring at 60 s, twice:** unknown (59.8 s, 60.0 s). Its rounds now finish their goals, but the pool Houdini's set
  proofs fail at cubes in turn until the wall.
- **Pilot 1 again** (the cone, with sorts and strict; `rg12`): FAIL.
  - 32 cubes, all 5 targets in the set;
  - at 5 s a goal: 15 proven, 2 models, 16 undecided (median 4.5 s);
  - the cone is 15 cubes, 4 of them undecided, and `prove()` fails in 0.1 s at a 4-key cube with no support.
  - At 5 s a goal the oracle still leaves half of the set's goals open with the whole set assumed (32 laws, against the
    pilot's 47 with fewer instances).
- **The quick bar** (`--only rw,f1,f2,g332,suite,onecpu` against the cached 5d4da3f; <main>/runs/bar/runs/ring-63bed40-quick):
  - f1 34 and rw 74/14/3, as the base;
  - f2 24 against 24.33 (no task differs);
  - g332 the same search on 332 of 332, summed 289.5 s against 283.3 s;
  - the suite 232 passed, 0 failed;
  - onecpu no failure.
  - Gained 0, lost 0, wrong 0. Estimated $0.57.

**What's left for ring:**
- the set's own goals at 30–47 assumed laws, about half still open at 5 s;
- the pool Houdini's one-drop-per-proof loop.

The order's size is no longer the cost on the round goals (mean 0.55 s, 9 of 44 open at 1 s).

**Rule breaks this round, recorded:**
- Two local commands ran with the 1-minute load over 12: a 1 s trace probe at load 15.9, and a typecheck and lint at
  load 13.8, with the load checked in the same command rather than before it.
- After that, the remaining traces and typechecks went to Modal.

**Spend this round:** $0.85 billed for 34 apps so far; the current hour is still being billed.

**Next round: decentralized, the memo bug, and ring top-down** (gen/ring 41f35a0; exp/pool-z3 for the top-down runs)

**Decentralized's 36 s was real, and strict models caused it** (`runs/engine/gr7`–`gr10`, 60 s, Modal)

| config | runs (s) |
|---|---|
| sorts and strict (as built at 63bed40) | 36.0, 29.6, 33.3, 32.8 |
| strict off | 17.0, 13.3, 15.7 |
| sorts off (strict on) | 27.4 |
| 41f35a0: sorts on (memo fixed), strict off | 18.4, 15.7 |

- **Why strict costs it:** where decideLaw used to return an unconfirmed model, the rounds now get no answer and fall
  through to the CDCL search and the proof path.
- **Strict is now off by default** (`GDP_STRICT=1` turns it on).

**A bug in the sorts as built: their memo was keyed by machine alone.** One machine is asked with many law sets, so the
sorts were the first set's, and the cubes' keys had no anchors.
- In the engine, decideLaw's instances went nearly unfiltered: 11,557 to 11,478 keys a goal, against 54% fewer in the
  replay.
- 63bed40's measurements (the ten, ring, the bar) were therefore mostly strict's.
- Fixed in 41f35a0: the memo is keyed by machine and by the law set's names.

**41f35a0, the ten once** (`gr10`):
- **proven:** sync 6.3 s, async 23.9, decentralized 18.4 and 15.7 (2 runs), 2PC 19.3, ticket 31.4, toy 12.1, sharded
  32.9, distributed 32.6;
- **unknown:** ring 59.7 s (twice) and wo 65.0 s.
- The typecheck and lint are clean (on Modal).

**Ring by top-down Houdini with the new oracle** (db6c00f's `GDP_POOL=td` on exp/pool-z3, with sorts (memo fixed) and
strict; `rg19`)

| round | cubes | failed | undecided | ms |
|---|---|---|---|---|
| 0 | 42 | 7 (2 back by co-implication) | 8 | 24,299 |
| 1 | 37 | 6 | 9 | 15,347 |
| 2 | 31 | 4 (6 back) | 6 | 9,734 |
| 3 | 33 | 7 | 5 | 12,956 |
| 4 | 26 | 0 | 5 | 6,094 |

- **The fixpoint:** 26 cubes, 5 of them undecided, **all 5 targets in it** (none failed in any round).
- **The caller and the cone:** the caller is proven from the fixpoint; the cone is 19 cubes with all 5 targets, 1
  undecided. **`prove()` of the 19 proves in 8.6 s.**
- **End to end: proven at 105 s** (`--ms 180000`). At `--ms 60000` it is out of time in round 1 (the engine starts at
  24 s, and round 0 takes 24 s).
- Before the memo fix the same run left 42 of 42 undecided in round 0 (`rg17`, `rg18`: every step goal past its
  deadline at 0.8 s, 49 ordered terms).

**So ring proves with the shrunk pool, the sorted oracle, top-down and the cone, but in 105 s, not 60.** Not wired in,
as the order said.

**What's left: time.**
- **Before the engine:** 24 s (the join, the small instance, the filter).
- **Houdini:** 68 s for 5 rounds; 0.25–0.6 s a goal, with 5–9 undecided a round costing 1 s each.
- **The cone and `prove()`:** 9 s.

**Levers, not tried:**
- the undecided goals' 1 s each;
- asking only the goals whose support a drop took away (DuoAI asks all; the memo's standing proofs would skip the
  rest);
- a smaller pool by a deeper filter (64 at +1);
- the join's share before the engine.

**The quick bar on 41f35a0** (`--only rw,f1,f2,g332,suite,onecpu` against the cached 5d4da3f;
<main>/runs/bar/runs/ring-41f35a0-quick)
- f1 34, as the base;
- f2 25 against 24.33: "gained 1", term/Piecewise. It is proven at 51–56 s in 3 of 4 runs against 3 of 6 for the base,
  a flip at the time limit;
- rw 74/14/3, as the base;
- g332 the same search on 332 of 332, summed 281.5 s against 280.6 s;
- the suite 232 passed, 0 failed;
- onecpu no failure.
- Lost 0, wrong 0. Estimated $0.58.

**Ready:** gen/ring at 41f35a0 (sorted decideLaw instances, strict off) is ready to merge on these numbers. Ring
and wo are unchanged at 60 s; the eight stay proven; decentralized is back in its spread.

**Not done this round, as the order said:**
- step 3 (ring twice, the ten, the bar), because 1 didn't land;
- wo's pilot, because pilot 2 didn't fail fast.

**Spend:** $0.06 billed so far for this round's 4 apps; the hour is still being billed, about $0.15 in all.

## Through the gate: gen/rel-pool (main 2fdc902 with gen/pool merged, d8a1966; then main 8fedbea, 7b5b6e8)

**The merge:**
- gen/rel-pool is made from main's head 2fdc902 (the inferred boundary, Java/Kotlin, the CLI), with gen/pool merged in.
- The merge also brings gen/enum4's commits since dfafb37: the frames crash fix, push blocking, epr's simplex theory
  check, and the rest.
- There were no conflicts. The typecheck and oxlint are clean.

**The ten once on the merged tree** (`runs/engine/rp1`, Modal 2 CPU, 60 s)
- **The eight are proven:** sync 10.8 s, async 21.9, decentralized 14.2, 2PC 18.9, ticket 34.5, toy 9.8, sharded 33.2,
  and distributed 27.4.
- **Unknown:** ring 60.1 s and wo 65.7 s.
- **The filter's cost:** distributed 1.2 s, ring 2.9 s, wo 2.0 s.

**The quick bar** (`bun gates/bar.ts --quick --cand gen/rel-pool --base 5d4da3f --only rw,f1,f2,g332,suite,onecpu`,
against the cached 5d4da3f49013-modal-r1; <main>/runs/bar/runs/relpool-d8a1966-quick/REPORT.md)

| group | candidate | base mean | gained / lost / wrong |
|---|---|---|---|
| f1 (48) | 34 proven | 34 | 0 / 0 / 0 |
| f2 (64) | 24 proven | 24.33 | 0 / 0 / 0 (no task differs; the base's own noise) |
| rw (91) | 74 proven, 14 refuted, 3 unknown | the same | 0 / 0 / 0 |
| g332 | 332 / 332, the same search on every goal | | summed 309.8 s against 273.7 s (p50 1.087) |
| suite | 232 passed, 0 failed | 226.67 of 227 | 0 / 0 / 0 |
| onecpu | no failure | no failure | |

- **g332's timing:** that run's +13% summed time was noise. g332 runs its two sides together, and alone again it read
  292.0 s against 301.8 s (p50 1.004; `relpool-d8a1966-g332-again`).
- **The suite's +5 jobs** are main's own new tests since 5d4da3f.
- **Size:** core/ and kernel/ are 3,020,982 bytes against 2,672,441. Most of the +348 KB is main's since 5d4da3f.
  core/infer.ts is 230,011 bytes against main's 216,168: gen/enum4 since dfafb37 adds 8.4 KB, gen/pool 5.4 KB.
- **Spend:** an estimated $0.55 for the bar and $0.05 for the g332 rerun.

**Main moved to 8fedbea** (gen/boundary3's soundness fix, a fast-forward of 2fdc902). It was merged into gen/rel-pool
(7b5b6e8: no conflicts, typecheck and oxlint clean), and both checks ran again there.
- **The ten** (`runs/engine/rp2`): the eight proven (sync 7.0 s, async 22.2, decentralized 15.1, 2PC 18.8, ticket 33.1,
  toy 13.3, sharded 34.6, distributed 29.7); ring 60.2 s and wo 64.8 s unknown.
- **The same quick bar** (<main>/runs/bar/runs/relpool-7b5b6e8-quick/REPORT.md):
  - f1 34 proven, as the base;
  - f2 25 against 24.33, one task differing on the first pass and noise after 3 reruns a side;
  - rw 74 / 14 / 3, as the base;
  - g332 the same search on 332 of 332, summed 299.3 s against 297.1 s (p50 0.998);
  - the suite 232 passed, 0 failed;
  - onecpu no failure.
  - Gained 0, lost 0, wrong 0 in every group.
  - Estimated $0.58.

**Ready to fast-forward main** to gen/rel-pool (7b5b6e8 and this DESIGN.md-only commit on top).

## The plan: our own procedure for the goals Z3 decides (design only, nothing built)

**What it answers.** These are the goals exp/pool-z3 found Z3 decides and decideLaw doesn't:
- wo's request-carried sets under ∀ flags: every one of wo's goals;
- ring's injective `idn` in composed keys, with a successor that wraps at a param: 28 of 44;
- the ∀∃ law that neither oracle decides;
- and the unsat cores the cone cut needs.

All of it is untrusted search. A verdict is still `prove()` of the final set, checked. No new certificate kind is
needed, because each piece below decides goals whose proof the kernel already makes.

**What the kernel already certifies** (`runs/engine/given1`, gen/rel-pool, Modal 2 CPU, given mode)
- wo's written invariant, with its ∃ ghost: proven in 30.5 s (8.2 s usual, 21.4 s cyclic).
- ring's: 3.4 s.

So both protocols are proof-shape-complete today. What's missing is finding the set: the oracle's decisions, and a set
small enough that `prove()` costs about what given mode does.

**Ranked by which closes a protocol soonest**

**1. Cores for the cone cut before `prove()`.** (Closes nothing alone; ring's last step in both oracles.)
- **Mechanism:**
  - decideLaw returns its proof's support: the union of `settled`'s proofs' `uses`, from `sourcesOf` over the
    refutation's used hypotheses. db6c00f had it: three lines in kernel/prove.ts.
  - The rounds keep each proven goal's support. A goal settled by the CDCL search already has its core (`settled`).
  - Before the set's `prove()`, the set is cut to the closure of the caller's support.
  - A cube in the cone whose support is unknown is asked again with the cone alone assumed. A proof adds its support; a
    model's pre-state brings in the set's cubes false there (db6c00f's `close`).
- **Where:** kernel/prove.ts (decideLaw's return, untrusted) and core/infer.ts (the rounds' final proof).
- **Bytes:** about 0.3 KB in prove.ts and 2 KB in infer.ts. db6c00f's version was 2.4 KB with diagnostics.
- **Evidence:** distributed's cone was 26–27 of 50–52 cubes, and its `prove()` 4.5 s (was 43–89 s at about 140 cubes).
- **Cheapest falsifying pilot:** ring's IC3 set at the end of pz2's `ring-z3ic3` run.
  - It is 30 cubes holding all 5 targets. Its texts weren't printed, so the run is repeated with the set printed
    at the end.
  - Ask each goal with decideLaw at 5 s, take the cone, and `prove()` it. One Modal job, about 2 min.
  - **Falsified if** the cone isn't well under 30, or its `prove()` fails or costs over 20 s.

**2. Ring: ordered-sort successors and an injective function inside composed keys.** (Closes ring with 1.)
- **What decideLaw does now:** all 28 goals run to its 1 s cap; none returns a model or an early give-up. So they are
  EPR-shaped, and the cost is the instance and lemma growth.
  - epr.ts notes that a goal's clauses are quadratic in its terms.
  - Each ground `n + 1` of the wrapping successor, each `idn(t)` and each composed key `64·idn(x) + y` adds terms, and
    the theory lemmas compare every pair.
- **Mechanism (Z3's encoding, the parts that mattered):**
  - **An ordered sort as a total order** with a least element and ground successors. `t + 1` is a successor term with
    only "nothing strictly between t and t + 1", and only at the goal's ground terms. No arithmetic on node keys; the
    wrap `n + 1 = size ? 0 : n + 1` becomes a case split on the one ground term.
  - **`idn`'s injectivity as distinctness among the goal's ground `idn` terms alone,** quadratic in those terms, not in
    every term.
  - **A composed key whose part is `idn(x)`:** a tuple whose first part is that term (the tuple abstraction of composed
    keys already compares parts by order and equality).
- **Where:** kernel/epr.ts (the abstraction and its lemmas), untrusted. An unsat answer goes back through prove.ts's
  core-and-widen path, which the kernel checks, so no new certificate.
- **Bytes:** 2–4 KB in epr.ts.
- **Cheapest falsifying pilot:** replay ring's top-down goals through decideLaw at 1, 5 and 20 s.
  - Dump them with `GDP_Z3_DUMP` on exp/pool-z3; replay with `research/protocols/engine/z3probe.ts replay`, which times
    both oracles per goal. One Modal job, about 5 min.
  - Before it, one local probe of 30 s or less: the `unknown` reason of one of the 28 (the deadline, the model's order,
    or the read-back).
  - If most decide by 5 s, the gap is cost. Profile `decide0`'s instance and lemma counts, and the mechanism above is the
    fix.
  - **Falsified if** they stay undecided at 20 s with no growth in conflicts: then it is incompleteness, and the
    successor and injectivity encoding must be rebuilt, not tuned.
- **Why ring is first:**
  - its written invariant proves in 3.4 s;
  - with Z3, IC3 over the shrunk pool already put all 5 targets in the set;
  - the engine starts at about 23 s.
  So 1 and 2 together are the whole gap.

**3. wo: a request-carried set under ∀-quantified flags, and a write at every key from it.** (Needed for any wo goal.)
- **What decideLaw does now:** wo's goals are undecided in 0.24–1.26 s (median 1.0 s), including trivial ones ("Leader
  ∧ started is 0"). Some give up well before the cap.
- **The suspicion** (not yet measured) is the shape, not the cube. wo's step has:
  - the carried set Q, read at a bound key under `everyKey` in the assumption;
  - two quantified flags (`quorumVotes`, `votingQuorumVotes`: ∀k. Q has k → Votes[src, k]), each a 0/1 variable with a
    witness key per flag in the kernel's goal (kernel.ts: `w?f`);
  - VotingQuorum written at every key from Q.
  `patternsOf` leaves out reads keyed by a write-at-every-key's own name, and `decide0`'s shape check needs every map
  read at its pattern. A carried map at a bound key, or a flag's witness key, may fail it, and the goal then reads as
  "not EPR-shaped" or breaks at read-back.
- **Mechanism (Ivy's shape):**
  - the carried map gets a pattern like any map;
  - a quantified flag's 1-side is a ∀ instantiated by the model-instance rounds at the goal's ground keys, as laws
    already are; its 0-side is its witness constant, a ground key;
  - the write at every key is, at each ground key read after the step, the if of the write's condition over Q's and the
    old map's cells there.
- **Where:** kernel/epr.ts (`patternsOf`, the shape check) and kernel/prove.ts (the flags' witness keys among the
  instances' ground keys), untrusted.
- **Bytes:** 2–3 KB.
- **Cheapest falsifying pilot:** one local probe of 30 s or less. `decide` on wo's trivial goal "never 1 <= Leader[x]
  and started is 0", every law of round 0 assumed, printing its `unknown` reason and which hypotheses aren't shaped.
  - **Falsified if** the reason is the deadline with every hypothesis shaped. Then it is cost, as for ring, and the shape
    work buys nothing.
- **Why it ranks behind ring:** wo needs this and 4, and its final proof alone is 30.5 s (given mode). With the join
  and the small instance at 21–26 s before the engine, wo doesn't fit 60 s on Modal even with a perfect oracle, unless
  that cost falls too:
  - the cyclic certificate's 21.4 s;
  - or the join, when the engine follows.

**4. The ∀∃ law ("after init the voting quorum has a member", with its ghost witness).** (Closes wo with 3 and a
cheaper final proof.)
- **The state:**
  - the rounds already find the right witness: the same ghost as the written one, `when(inits ∨ chooses, w, before)`;
  - the kernel proves the written ∃ law with that ghost through core/exists.ts (`proveSome`) and the Lean twin's Ghost
    module: the given-mode proof above;
  - so no new certificate kind is needed.
  - What no oracle decides is its goals. decideLaw's fast shape refuses any "there exists" law; Z3's translator leaves ∃
    goals and ∃ laws to the kernel. Z3's set check then finds a model of "one leader" without it.
- **Mechanism:** the oracle sees the ∃ law as its witness instance, `ghost.plain`, over the ghosted machine
  (`withGhost`). That is a quantifier-free law of one more state scalar, which the rounds already build. Two changes:
  - every set check and every oracle call assumes `ghost.plain` in place of leaving the ∃ law out;
  - the ghost's own goals (start and step) are asked like a cube's.
  Its step reads `chooses`, so deciding it needs 3 first.
- **Where:** core/infer.ts (what the oracle is asked), untrusted. The final proof stays `proveSome`'s.
- **Bytes:** about 0.5 KB.
- **Cheapest falsifying pilot,** after 3's local probe: decideLaw on `ghost.plain`'s step over `withGhost(m)`, with wo's
  written ∀ laws assumed (one local probe of 30 s or less).
  - **Falsified if** it has a model the interpreter confirms. Then the ghost needs support beyond the written laws, and
    the witness search, not the oracle, is the gap.

**The order to run them**
1. 2's local reason probe and 3's: two local probes of 30 s or less, one at a time, no code kept.
2. 1's cone pilot and 2's replay at 1, 5, 20 s: two Modal jobs, about $0.05.
3. Build 1, then 2. Measure ring at 60 s (2 runs), the seven, the bar.
4. Only then 3 and 4, with wo's final-proof cost measured beside them.

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

## gen/ring2: fitting ring in 60 s (WIP at the 15:40 checkpoint; nothing wired, ring not yet inside 60 s)

**Built:**
- **On gen/ring2 from main fc5611b, behind `GDP_TD=1` (off by default), core/infer.ts:** the top-down phase ported from
  db6c00f.
  - Houdini is incremental: after a drop, only the goals whose proof read a dropped cube are asked again (by decideLaw's
    used laws), plus new and undecided goals.
  - A first cap (`GDP_TD_Q1`, default 250 ms), and a second pass at `GDP_TD_Q2` (1 s), only when a round would end with no
    drop.
  - Then the cone and `prove()`.
- **Its decisions run strict (`withStrict`):** without it, unconfirmed models at the 1 s cap dropped 28 and 23 true cubes
  in one round each, and the caller was lost (`runs/engine/r2a`).
- **kernel/prove.ts:** decideLaw returns `uses`; `withStrict` is exported.
- **Timing events:** 'join engine' and 'join td'.
- **Checks:** typecheck and lint clean at 7933ce5 (on Modal). The later commits are not rechecked.

**Ring, phase times** (Modal 2 CPU, `--ms 180000`, one run each)

| config | before the engine (join, enumeration, filter) | filter left / pool | Houdini | cone + `prove()` | verdict |
|---|---|---|---|---|---|
| exp/pool-z3 rg19 (old filter 4 s an instance; full Houdini; strict) | 24 s | 64 / 42 | 68 s, 5 rounds | 1 + 8.6 s | proven 105 s |
| ring2, q1 1 s, filter 3 s (main's default) | 12.5 s (join about 4 s) | 94 / 66 | 153 s, 8 rounds (asked 66, 39, 27, 23, 14, 16, 14, 11) | 0.5 + 13 s, cut by the wall | unknown 180 s |
| ring2, q1 1 s, filter 8 s | 15.4 s | 68 / 44 | 77 s, 7 rounds | 0.7 + **66 s** | proven 160 s |
| ring2, q1 250 ms with the 1 s second pass, filter 8 s | 15.5 s | 68 / 44 | 128 s, 15 rounds | 0.7 + 30 s (cone 11) | proven 174 s |
| ring2, q1 500 ms with the second pass, filter 8 s | 16.1 s | 68 / 44 | 136 s, 12 rounds | 0.9 + 26 s, cut | unknown 180 s |

**What the levers did:**
- **The incremental Houdini** cuts the goals asked a round, to 6–39 after round 0. The proof memo was already cheap for
  standing proofs, so the time saved is small.
- **The short first cap with the second pass** is worse on ring. Most of its goals need 0.3–1 s, and since rounds keep
  dropping, the second pass rarely runs, so each round re-asks the undecided at 250 ms (15 rounds instead of 7).
- **The time before the engine** is 11–16 s on main, not 24. The join is about 3–4 s; the rest is the enumeration and
  the filter. Main's 3 s filter leaves a 50% larger pool (66 against 44), which costs more in Houdini than the extra
  filter seconds.
- **The final `prove()` of the cone** varies from 8.6 s to 66 s for 19 cubes. It is now the largest single cost.

**The exact next step** (none of this is verified):
1. a filter budget for the engine's pool that scales with the instance's BFS (ring's +1 instance needs about 8 s), with
   a general cap;
2. q1 at 1 s, no two-pass;
3. the cone's `prove()` cost: the fast set proof (`prove(…, true)`) on the cone first, timed against the usual one;
4. then ring at 60 s twice;
5. only then the wiring with a pool threshold, the ten twice, and the quick bar.

**Spend:** about $0.12 for this round's apps (estimated from job seconds; the hour is still being billed).

## gen/ring2, resumed: the cone's proof fixed, Houdini still too slow (ring 101 s; nothing wired)

**Changes** (e6397eb–704d482):
- **The pool filter's budget scales with the small instance's search:** six times it, 3 s at least, 10 s and a sixth of
  what is left at most. Ring gets about 8.8 s and reaches 68 cubes after the filter, 46 after the minimal cut;
  distributed keeps 3 s.
- **Top-down's cap is 1 s, with no second pass** (q2 defaults to q1).
- **The cone's proof** is timed fast against usual.
- **The fast set proof's instances are by sort too** (`settle` for both callers; proveLaw's and the join's instances as
  they were). The fast proof is checked over the tuples its proofs read, and the usual proof follows where it fails.

**Why the cone's proof cost 8.6–76 s** (`r3d`, bun's CPU profile from the cone's start):
- 94% of the fast set proof was `settle` → `eprFirst` → `decide`, re-deciding every cone law's goals with unsorted
  instances: the cubic order again (`atom`, `theoryCheck`, `propagate`).
- Houdini's proofs, made with sorted instances, weren't reused: the set proof asks its own machine.
- The undecided cubes weren't the cause. With none in the cone (`GDP_TD_DECIDED=1`) the proof still took 75.9 s, and
  with one, 61.4 s.

**Ring, phases** (Modal, `--ms 180000` unless said)

| run | before the engine | pool | Houdini | cone + `prove()` | verdict |
|---|---|---|---|---|---|
| r3a (scaled filter, 1 s cap) | 18.1 s | 44 | 87 s, 9 rounds (asked 44, 27, 14, 10, 12, 10, 6, 4, 3) | 0.8 + 73 s (fast failed at a between-turn cube; usual cut by the wall) | unknown 180 s |
| r3c r2 | 13.9 s | 44 | 66 s, 6 rounds | 0.7 + 61.4 s | proven 143 s |
| r3c, decided cubes only | 16.5 s | 44 | 80 s, 7 rounds | 0.1 + 75.9 s | proven 174 s |
| **r3e, fast set proof sorted** | 15.2 s | 46 | **77 s, 6 rounds** | 0.7 + **7.7 s** | **proven 101.5 s** |
| r3c at 60 s, twice | 10.6, 13.4 s | 44 | out of time in round 4 and in round 2 | | unknown 59.5, 59.7 s |

**The ten once with the sorted fast set proof** (`r3f`, GDP_TD off):
- **proven:** sync 8.8 s, async 30.7, decentralized 14.0, 2PC 20.3, ticket 30.4, toy 10.3, sharded 29.0, distributed
  27.0;
- **unknown:** ring 60.4 s and wo 66.1 s;
- the typecheck and lint are clean.

**What's left: Houdini, 66–87 s.**
- Round 0 asks all 44 goals at about 0.6 s each (26–27 s); the later rounds ask 3–27 goals at about 0.8 s.
- To fit 60 s, Houdini must come down to about 30 s, a factor of 2.5.
- **Levers, not tried:**
  - the per-goal EPR cost (`atom`'s text-keyed map is 16–20% of a decision; the theory check 30%);
  - Houdini's decisions sharing a machine across rounds, so that the memo's standing proofs are reused, not rebuilt;
  - two workers (Modal's containers have 2 CPUs).

**Not wired, as the order said:** ring doesn't fit 60 s. The sorted fast set proof is on the default path of
gen/ring2. It needs the ten twice and the quick bar before any merge; one run of the ten is done.

## gen/ring3: ring proven at 60 s (6 of 8 runs), top-down wired in at a pool-size threshold

**The three levers, one at a time at 60 s** (Modal, one worker; run 1, then run 2)

| lever | before the engine | Houdini | the cone's proof (memo hits / misses) | verdict |
|---|---|---|---|---|
| none (acb81a8) | 15.5 s | 42 s, 6 rounds | out of time | unknown |
| 1. near-miss order, failures dropped within the round (`GDP_TD_ORDER`) | 15.7, 14.2 s | 36, 32 s, 4–5 rounds | 5.3 s, failed at a cut; 0.5 s at the wall | unknown, unknown (the cone reached at 54 and 48 s) |
| 2. the filter stops after an instance that kills nothing (`GDP_POOL_STOP`) | 12.5, 14.1 s (filter 5.8, 6.5 s, against 7.4) | 39, 44 s | 5.4 s at the wall (0 / 22) | unknown, unknown |
| 3a. a larger memo (`GDP_MEMO_CAP=16`) | 14.5 s | 43 s | 0 / 2 | unknown: no gain, not kept |
| 3b. the memo up to fresh names (`GDP_MEMO_ALPHA`) | 17.2 s | 41 s | | unknown; at `--ms 180000` the cone's proof hits 19 of 22, 5.2 s against 7.8 |

- **Why the cone's proof missed every decision:** proveRule makes the rule's machine again with fresh binders (`k$16`
  against Houdini's `k$13`, and the kinds' laws' keys), so the memo's machine text and law texts never matched (0 of
  22).
- **The fix:** texts up to a renaming of fresh names (`x$N` named in order of appearance). With it, 19 of 22 are reused
  and the kernel's check of the set still passes.

**The three together** (`r6f`, 60 s, 3 runs): **proven 55.6, 48.7, 58.0 s.**
- Before the engine 14.3–16.1 s; Houdini 30–36 s in 3–5 rounds; the cone's proof 2.8–4.6 s.

**Wired in** (efefe58, 030d8a1):
- **Top-down runs by default** where the minimal pool is 25 to 64 cubes: past what the rounds' first round takes (24),
  and within what Houdini can afford. The IC3 rounds are the fallback with the time left.
- **The three levers are on by default.** `GDP_TD=0|1`, `GDP_TD_ORDER=0`, `GDP_POOL_STOP=0` and `GDP_MEMO_ALPHA=0` turn
  them off.
- **Which protocols reach top-down:** ring (made 46) and distributed (60). toy (10), decentralized and sharded (17) and
  wo (99–136) don't.

**The ten twice on the wired tree** (`r7a`; main acb81a8 is its base, nothing newer):
- **proven both runs:** sync 6.8 / 8.5 s, async 25.5 / 20.8, decentralized 18.2 / 18.3, 2PC 22.1 / 11.6, ticket 32.7 /
  36.5, toy 12.1 / 11.7, sharded 27.3 / 26.0, distributed 42.2 / 30.6;
- **ring:** unknown 60.2 s, then **proven 46.0 s**;
- **wo:** unknown 65.3 / 64.4 s;
- the typecheck and lint are clean.
- **Ring three more times** (`r7b`): unknown (the filter left 75 and the pool was 50: Houdini 41 s, out of time),
  proven 52.3 s, proven 37.2 s.
- **Ring at 60 s with this code: 6 of 8 runs** (3 of 3 behind the switches, 3 of 5 wired).
  - The misses are slow containers: 15–17 s before the engine, or a filter that leaves more cubes.
- **Distributed now goes through top-down,** and its time varies more: 30.6–42.2 s against 25–33 s.

**The quick bar** (`--only rw,f1,f2,g332,suite,onecpu` against the cached 5d4da3f, on 030d8a1;
<main>/runs/bar/runs/ring3-030d8a1-quick):
- f1 34 and rw 74/14/3, the same as the base;
- f2 25: "gained 1", term/Piecewise, a flip at the time limit (seen before);
- g332 the same search on 332 of 332 (280.2 s against 285.9 s);
- the suite 233 passed, 0 failed;
- onecpu no failure.
- Lost 0, wrong 0. Estimated $0.58.

**Verified, not:**
- **Verified:** all of the above (Modal; runs as counted).
- **Not verified:**
  - ring's 60 s margin on slow containers (2 misses in 8);
  - distributed's spread under top-down beyond two runs;
  - the threshold's effect on the corpus beyond the quick bar's dev sets.

## gen/ring2: the sorted fast set proof banked; Houdini from 77 s to 39–55 s (ring at 60 s still unknown)

**Part 1, the gate for the default path at a28e529** (the sorted fast set proof and the scaled filter; top-down off
behind GDP_TD):
- **The ten, twice** (`r3f`, `r4a`):
  - proven both runs: sync 8.8 / 8.9 s, async 30.7 / 24.9, decentralized 14.0 / 16.6, 2PC 20.3 / 20.6, ticket 30.4 /
    36.1, toy 10.3 / 11.6, sharded 29.0 / 26.0, distributed 27.0 / 26.5;
  - unknown: ring 60.4 / 60.0 s and wo 66.1 / 66.8 s.
- **wo's 66 s:** its filter now takes 3.2 s (the 3 s floor; its small instance's search is short), against 2.0 s
  before. The filter's budget is at most a sixth of what is left, so it ends well inside the wall. wo's 66–67 s is
  within its earlier 63.7–69.0 s across runs on main, which is the EPR side's overrun.
- **The quick bar** (`--only rw,f1,f2,g332,suite,onecpu` against the cached 5d4da3f;
  <main>/runs/bar/runs/ring2-a28e529-quick):
  - f1 34, f2 24 (base 24.33, no task differs), rw 74/14/3, the same as the base;
  - g332 the same search on 332 of 332 (summed 300.9 s against 283.5 s, p50 1.08; earlier bars on this base read
    +13% and then −3% on a rerun);
  - the suite 232 passed, 0 failed;
  - onecpu no failure.
  - Gained 0, lost 0, wrong 0. Estimated $0.56.
- **a28e529 is merge-ready on these.** The commits after it touch top-down (behind GDP_TD) and one default-path change,
  06263bb's epr caching: the same atoms and clauses, faster lookups. That change has had neither the ten nor the bar
  on its own.

**Part 2, ring's Houdini phase, per lever** (Modal 2 CPU, one worker; `--ms 180000` unless said)

| lever | before the engine | Houdini | ms an asked goal | cone + `prove()` | end to end |
|---|---|---|---|---|---|
| base: the sorted fast set proof (r3e; r3c r2) | 15.2 s | 77 s; 65 s | 577; 558 | 8.4 s | 101.5 s |
| + the atoms by term pair and the term texts once (06263bb; r4c, 2 runs) | 12.8, 16.6 s | 63, 67 s | 528, 561 | 7.5, 7.9 s | 85.4, 93.8 s |
| + decideLaw's first instances triggered (GDP_DLTRIG=1, off; r4d) | 14.7, 18.2 s | 60, 83 s | 529, 668 | 7.6, 10.5 s | 84.2, 114.3 s: no gain, left off |
| + undecided goals kept, asked again only after a round with no drop (caef10e; r4e) | 19.9, 10.5 s | 55, 39 s | | 9.2, 6.4 s | 86.4, **57.6 s** |
| the same at `--ms 60000` (r4e, 2 runs) | 11.8, 12.7 s | 42, 41 s | | the cone reached at 55 s; `prove()` cut by the wall (4 s) | unknown, unknown |
| + each undecided goal asked again once (b019a0a; 60 s, 3 runs) | 14.8, 14.9, 16.9 s | out of time in round 4 at 59 s | | | unknown ×3 |

- **The biggest lever** was the undecided goals: 4–9 of them re-asked at 1 s every round had been 25–35 s of the
  phase. Keeping them (optimistic Houdini) and asking them only when a round drops nothing brought Houdini to 39–55 s.
- **The epr caching** gives about 5–10%, within the run-to-run noise.
- **Ring now fits 60 s in one run of five** at a 180 s budget's pace (57.6 s), and in none of five at `--ms 60000`.
  - The run-to-run spread is wide: before the engine 10–20 s, Houdini 39–55 s.
  - The 60 s runs end in round 4 or 5, or at the cone's proof.

**What's left:** about 5–15 s.
- **Candidates:**
  - round 0, which asks all 44–46 goals at about 0.55 s (24–27 s);
  - the 15 s before the engine on slower containers (the filter's 7–9 s for ring);
  - the cone's proof (6–9 s).
- **The next levers, not tried:**
  - round 0's goals in an order that drops early (the cubes with the most literals first);
  - stopping the filter once a full pass over the BFS kills nothing new;
  - the cone's proof reusing Houdini's settled proofs: it already does where the machine's text matches. Check that it
    does here.

**Spend this part:** $0.69 billed for 18 apps so far (the hour is still being billed).

**Merged with main 7f5d3de (Swift) as 0cebaac, and gated there.** The tree carries everything above: the epr caching
on the default path, and top-down behind GDP_TD.
- **The ten** (`r5a`):
  - proven: sync 9.3 s, async 24.8, decentralized 16.9, 2PC 17.8, ticket 33.0, toy 15.3, sharded 33.3, distributed 30.9;
  - unknown: ring 59.8 s and wo 63.2 s;
  - the typecheck and lint are clean.
- **The quick bar** (<main>/runs/bar/runs/ring2-0cebaac-quick):
  - f1 34 and rw 74/14/3, the same as the base;
  - f2 25 against 24.33: one task differs on the first pass, noise after 3 reruns a side;
  - g332 the same search on 332 of 332 (291.4 s against 297.6 s);
  - the suite 233 passed, 0 failed;
  - onecpu no failure.
  - Gained 0, lost 0, wrong 0. Estimated $0.59.
- **gen/ring2 at this merge is merge-ready.**

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

## gen/laneK: counting and ghost maps in the trusted kernel (Lean first; the search not wired)

Two certificate kinds for the IC3Syn classes gen/laneA's design note left out (its "Counting" and "∀∃: a ghost map"
paragraphs), each proven in the Lean twin first, then checked by kernel.ts as Lean states it, mutation-tested, and carried
end to end on hand-built examples. Nothing in kernel/prove.ts, kernel/epr.ts or core/infer.ts changed: the search side
waits for gen/laneA.

**Counting (lean-kernel/Count.lean, on Kernel.lean alone).**
- **The lemma.** `exists_lt_of_sumBelow_lt`: sums over the keys below n are monotone and linear, so if g sums below f,
  some key below n has g k < f k. Corollaries over sets of keys (`card p n`, the keys below n where p holds):
  `pigeonhole` (A, B ⊆ S, |A| + |B| > |S| ⇒ some k ∈ A ∩ B), `majorities_meet` (2|A| > |S|, 2|B| > |S|),
  `quorums_meet_outside` (|A| + |B| > |S| + |F| ⇒ some k ∈ A ∩ B outside F: f + 1 of 2f + 1, and n − t of n with
  n > 3t and at most t faulty).
- **The kind.** A counted goal is a goal and its counts (a variable v naming Σ_{k < below} body(k), the body read with its
  key variable at k). A certificate is a list of instances and a tree; an instance is a fresh witness, the bound its
  counts share, integer coefficients on counts and one on the constant 1. Lean builds each instance's hypothesis
  (`countHyp`: the combination's sum is not positive, or the witness is a key below the bound where its value is),
  checks the witnesses fresh (`countedOk`) and the tree against the goal's hypotheses followed by the instances'.
  `counted_sound`: no naturals and maps where every count is its sum satisfy an accepted goal's hypotheses.
- **Why this shape, and why it is the smallest.** A BAPA refutation is a Venn decomposition plus Farkas coefficients over
  the regions; what the regions buy is a linear combination of set sizes whose pointwise value is never positive. One
  instance carries exactly that combination (its coefficients on the counts are the Farkas multipliers), and the
  pointwise half (which regions the witness lies in) is the tree's ordinary case split over the cells it reads at the
  witness. So the kind adds one lemma and a hypothesis builder, no region variables and no new term form. Majorities
  (+1, +1, unit −1), f + 1 of 2f + 1 (the same) and more than two thirds with faults (+1, +1, −1 on the faulty, unit −1)
  are one instance each; a count of a compound body (A ∩ B) gives the numeric forms (|A ∩ B| ≥ |A| + |B| − |S|).
- **What is not built.** Counts in a machine's laws and steps: the goal builders (obligations, Sets.lean's goals) would
  make a counted goal per step, and Lean's machine twin would need a count term or count declarations on SMachine.
  That is the machine-level kind, the next Lean statement, after gen/laneA lands; this phase's kind is goal-level.

**Ghost maps (lean-kernel/GhostMap.lean, beside Ghost.lean).**
- `SGhostedM`: the original SMachine, ghost values (as SGhosted's), ghost maps (a start), and their writes at one key
  (`gwrites`) or at every key (`gevery`). `full` appends the ghosts after the original's lists. `smghostOk`: ghost names
  new and distinct, ghost writes only of ghost maps, and no part of the original (pre, assume, flags, quantified flags'
  bodies, start, step, writes, every-key writes, facts) reads a ghost variable or map.
- `smghost_reach` (`sghost_reach` from ghost values to ghost maps): every reachable state of the original is, outside the
  ghost variables and maps, a reachable state of the ghosted machine. `smghost_laws`: a law of the ghosted machine that
  reads no ghost holds of the original. `some_of_ghostmap`: at every reachable state of the original there are ghost
  values and ghost maps (Skolem functions of the keys) where every law holds. `forall_some_of_ghostmap`: a law about
  every kv that reads the ghost map W only at one key term gives ∀ kv ∃ x, the law with W's reads replaced by x.

**The correspondence, TS to Lean (each kernel.ts function is the Lean definition of the same name; the review's table).**

| Lean (Count.lean) | kernel.ts | How they correspond |
| --- | --- | --- |
| `Count ⟨v, key, below, body⟩`, `CInst ⟨wit, below, terms : List (Int × Nat), unit : Int⟩` | `Count`, `CountInst` (names, numbers) | emit.ts's `countedToLean`: each name its variable index, each term `leanTerms`, each coefficient an Int literal |
| `beqE` (structure) | `sameE`: JSON with keys sorted | equal TS terms print equal; TS is stricter where n-ary and/or nest differently |
| `findCount`: the first count with v | `cs.find(c => c.v === v)` | first match |
| `resolve`: per term, its count and `beqE c.below B`, else none | loop, `!c ‖ !sameE` → undefined | same order, same refusals |
| `sumE`: `[] ↦ .const 0`, `e :: es ↦ .add e (sumE es)` | `reduceRight` from `{const 0}` | same nesting |
| `posP z = z.toNat`, `negP z = (−z).toNat` | `Math.max(z, 0)`, `Math.max(−z, 0)` | equal on integers; TS refuses others (`typed`) |
| (a witness is a variable, a coefficient an Int, by type) | `typed`: each witness a string, each coefficient a safe integer | the certificate is input from outside: a number 5 as witness would pass `reads` (which holds names) and be read as the variable "5" by the linear forms; refused (a test shows the unsound acceptance it stops) |
| `side part rd one u rs = .add (sumE (rs.map (.mul (part c) (rd count)))) (.mul (part u) one)` | `side` | same term |
| `atCount c = .var c.v`; `atWit w c = substE [(c.key, .var w)] c.body` | `atCount`; `substE(body, {vars: {[key]: var w}})` | Lean's single substitution; TS's on var, get (key), if; counted bodies have no quantifier in Lean |
| `countHyp = .or (.le P N) (.and (.lt (.var wit) below) (.lt Nw Pw))` | `{or: [<=, {and: [<, <]}]}` | binary and/or print as `.or`/`.and` (lean-terms.ts) |
| `countHyps`: each in order, none if one is none | loop | same |
| `witFresh`: no hyp reads w; no count has v = w or reads w in below or body; no instance's below reads w | `reads(t).vars.has(w)` in the same three conjuncts | TS's `reads` leaves out keys an `all` binds; an `all` is opaque to the tree check and has no Lean form |
| `countedOk = cDistinct wits && all witFresh` | `new Set(ws).size === ws.length && every witFresh` | same |
| `checkCounted = countedOk && (countHyps → checkGoal ⟨tab, hyps ++ hs⟩ t)` | `countedOk && typed && check({hyps: [...hyps, ...hs]}, tree)` | the tree check is the existing twin (Kernel.lean's checkGoal, kernel.ts's check) |

| Lean (GhostMap.lean) | kernel.ts | How they correspond |
| --- | --- | --- |
| `SGhostedM ⟨orig, ghosts, gmaps, gwrites, gevery⟩` | `Ghosted {orig, vars: {start, step}, maps: {start, write}}` | emit.ts (`ghosted`): vars → ghosts, maps → gmaps, point writes → gwrites, every-key writes → gevery |
| `full`: the original's lists, then the ghosts' | `ghostedMachine`: records spread, the original's first | the names are apart (below), so no entry overrides another |
| `distinct vars`, `distinct maps`, ghost writes of ghost maps only | (record keys; a ghost map's write is its own) | hold by construction |
| vars ∉ extVars ++ init ++ step ++ flagVars ++ bkeys | `varNames`: inputs, each quantified flag `?f` and its witnesses, state (start and step), every flag `?f`, every-key and quantified keys | the same names (machineLit numbers them) |
| maps ∉ origMaps (maps0, writes, every, carried) | `mapNames`: `maps`, `step.maps` (point and every-key), `inputMaps` | the same maps |
| apartC/apartE of pre, assume, flags, quantified bodies, init, step, writes' keys and values, every-key values, facts, pfacts | `parts.every(apart)`: pre, assume, every flag (a quantified one whole), start, step, writes' keys and values, every-key values, facts (with keys: pfacts) | TS's `reads` leaves out a quantified flag's keys and reads flags as flags; those names are in `varNames`, so TS's verdict implies Lean's |
| (SMachine has none) | refuses `history` and `sums` | TS stricter |
| `smghostOk ∧ checkSMachine full` | `checkGhostedLaws = ghostedOk && checkLaws(ghostedMachine)` | the laws' check is the existing twin |

Every export also asserts the builders agree: `countHyps goal.counts insts = some [kernel.ts's hypotheses]` by `decide`.

**Mutation tests** (kernel/MUTANTS.md's operators, kernel/mutants.ts with `MUTANT_BATTERY=counts`, on Modal): the 40
mutants in kernel.ts's new lines (lines 1582–1703) are all killed by kernel/count.test.ts. One survived the first run
(`ms.every → ms.some` in ghostedOk: the test's clashing map was also read, so the parts' check refused it too); the test
now names a declared map the original never reads.

**End to end** (`lean-kernel/count-examples.ts`, the suite's `lean-count` job): the majority step (toy consensus's
Decide keeps agreement: two instances, cV + cB − N and cA + cV − N), f + 1 of 2f + 1, and the byzantine thresholds, each
`counted_sound` by `decide +kernel`, with three tampered certificates each computed to false (a witness that is a count's
variable, an instance dropped, the unit 0); and grants with a ghost map (W[k] := t where Grant(k, t) fires), its laws
through `smachine_sound` of `full`, `smghost_laws`, `some_of_ghostmap`, and `forall_some_of_ghostmap` read as
"every granted k has some x < T with valid[x] = 1", with a tampered original (its assumption reads W) whose `smghostOk`
computes to false. Every theorem's `#print axioms` is [propext, Classical.choice, Quot.sound].
