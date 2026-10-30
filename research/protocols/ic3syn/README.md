# The IC3Syn suite: 29 distributed protocols, ported

IC3Syn (Cao, Wu, Yao, Wei, Chen, Ma, "Synthesizing Inductive Invariants for Distributed Protocols via IC3 and Large
Language Models", arXiv 2605.24619, May 2026) reports candidate invariants for 29 TLA+ protocols, against Endive,
IC3PO, SWISS and DistAI, on an Apple M4 Pro, 600 s a tool (2 h for mldr and pyv-paxos-epr). The paper publishes no
artifact. Its suite is Endive's benchmark collection (28 of the 29, by their Endive names) plus "a hard Paxos variant
sourced from the IC3PO repository" (pyv-paxos-epr).

    models.ts   the ports (each with its correspondence, a broken variant, its instance and TLC cfg)
    common.ts   what they share: majority() by counting, the check's types
    check.ts    a port's reachable states on a small instance, by BFS, as the spec's variables
    tlc.py      Modal: TLC on the Endive spec beside check.ts's BFS, per protocol
    run.ts      Modal jobs: the search with nothing written, per protocol

## Where each comes from

| Source | Repository | Commit | Licence |
| --- | --- | --- | --- |
| Endive's benchmarks | github.com/will62794/endive, `benchmarks/` | 8b6f2abd1988eeb308f965813635e9871f253e2d (master, 2022-08-22) | none stated (no LICENSE file; GitHub reports none) |
| mypyvy's paxos_epr | github.com/wilcoxjay/mypyvy, `examples/pd/paxos_epr.pyv` | 12a8f5434a25587c56814d090b6ab7fa95851e71 | MIT |
| IC3PO (checked, not used) | github.com/aman-goel/ic3po | 026d4da27051eff3106b7e92d33ddbc862b14e5b (2024-09-10) | GPL-3.0 |
| IC3PO's ivybench submodule (checked, not used) | github.com/aman-goel/ivybench | 5db7eccb5c3bc2dd14dfb58eddb859b036d699f5 (as pinned); master d2c9298 | none stated |

Nothing of these sources is copied here: the ports are written from them by hand, and tlc.py fetches Endive at the
commit above in its container. IC3PO's repository (and its ivybench, at the pinned commit and at master) has no
paxos_epr in any form; Endive's `benchmarks/paxos_epr.tla` is the suite's only TLA+ of it, and its header cites SWISS's
`paxos_epr_missing1.ivy` and mypyvy's `paxos_epr.pyv` (commit above) as its model. That TLA+ has two faults, read off
the file: `Next` calls `Decide(n, v, r, Q)` but the action is `Decide(n, r, v, Q)`, so Decide reads `<<m, v, r>> \in
vote` for a value v and a round r and is never enabled (no decision is ever made: safety holds vacuously); and
`JoinRound` keeps `left_rnd' = left_rnd`, so no node ever leaves a round. So pyv-paxos-epr is ported from mypyvy's
paxos_epr.pyv, the model the TLA+ transcribes; IC3Syn's 1806 s and 9 invariants can't be from the file as committed.

| # | IC3Syn name | Source file | Port (models.ts) | Quorums | Instance checked (both sides) |
| --- | --- | --- | --- | --- | --- |
| 1 | tla-consensus | Endive Consensus.tla | consensus | | Value 3 |
| 2 | tla-tcommit | Endive TCommit.tla | tcommit | | RM 3 |
| 3 | i4-lock-server | Endive lockserver.tla | lock_server | | Server 2, Client 2 |
| 4 | ex-quorum-leader-election | Endive quorum_leader_election.tla | quorum_leader_election | majority | Node 3 |
| 5 | pyv-toy-consensus-forall | Endive toy_consensus_forall.tla | toy_consensus_forall | majority | Node 3, Value 2 |
| 6 | tla-simple | Endive Simple.tla | simple | | N = 4 |
| 7 | ex-lockserv-automaton | Endive lockserv_automaton.tla | lockserv_automaton | | Node 3 |
| 8 | tla-simpleregular | Endive SimpleRegular.tla | simple_regular | | N = 3 |
| 9 | pyv-sharded-kv | Endive sharded_kv.tla | sharded_kv | | Node 2, Key 2, Value 2 |
| 10 | pyv-lockserv | Endive lockserv.tla | lockserv | | Node 3 |
| 11 | tla-twophase | Endive TwoPhase.tla | twophase | | RM 3 |
| 12 | i4-learning-switch | Endive learning_switch_i4.tla | (not ported, below) | | |
| 13 | ex-simple-decentralized-lock | Endive simple_decentralized_lock.tla | simple_decentralized_lock | | Node 3 |
| 14 | i4-two-phase-commit | Endive two_phase_commit.tla | two_phase_commit | | Node 3 |
| 15 | pyv-consensus-wo-decide | Endive consensus_wo_decide.tla | consensus_wo_decide | Quorum: majorities | Node 3 |
| 16 | pyv-consensus-forall | Endive consensus_forall.tla | consensus_forall | Quorum: majorities | Node 3, Value 2 |
| 17 | pyv-learning-switch | Endive learning_switch.tla | (not ported, below) | | |
| 18 | pyv-sharded-kv-no-lost-keys | Endive sharded_kv_no_lost_keys.tla | sharded_kv_no_lost_keys | | Node 2, Key 2, Value 2 |
| 19 | ex-naive-consensus | Endive naive_consensus.tla | naive_consensus | Quorum: majorities | Node 3, Value 2 |
| 20 | pyv-client-server-ae | Endive client_server_ae.tla | client_server_ae | | Node 2, Request 2, Response 2 |
| 21 | ex-simple-election | Endive simple_election.tla | simple_election | Quorum: majorities | Acceptor 3, Proposer 2 |
| 22 | pyv-toy-consensus-epr | Endive toy_consensus_epr.tla | toy_consensus_epr | Quorum: majorities | Node 3, Value 2 |
| 23 | ex-toy-consensus | Endive toy_consensus.tla | toy_consensus | majority | Node 3, Value 2 |
| 24 | pyv-client-server-db-ae | Endive client_server_db_ae.tla | client_server_db_ae | | Node 2, Request 2, Response 2, DbRequestId 2 |
| 25 | pyv-firewall | Endive firewall.tla | firewall | | Node 3 |
| 26 | ex-majorityset-leader-election | Endive majorityset_leader_election.tla | majorityset_leader_election | majority | Node 3 |
| 27 | pyv-consensus-epr | Endive consensus_epr.tla | consensus_epr | Quorum: majorities | Node 3, Value 2 |
| 28 | mldr | Endive MongoLoglessDynamicRaft.tla | mldr | majority of a config, overlap of two | Server 3, MaxTerm 2, MaxConfigVersion 2 |
| 29 | pyv-paxos-epr | mypyvy paxos_epr.pyv (Endive paxos_epr.tla, faulty) | (not ported, below) | quorum sort (axiom) | |

## The encoding, beyond ../README.md's

- **The spec's variables, one for one.** A set variable is a map of 0/1 cells; a function into a sort with Nil a map
  of naturals (v + 1, Nil 0); an enumeration (`"working"`, `"prepared"`, ...) a map of few values (`few(k)`); a scalar
  a state variable. A sort the spec reads whole (`\A rm \in RM`, `tmPrepared = RM`, a majority of `Node`) is 0 .. size
  − 1 for a param `size`; every other sort is the naturals below N = 64.
- **Init that chooses.** `owner \in [Node -> SUBSET Key]`, `match \in SUBSET (Request \X Response)`, `internal \in
  [Node -> BOOLEAN]`, `\E start: has_lock = {start}`, `voting_quorum \in Quorums`: requests before `start` (or one
  `init`) set them, any of the spec's choices reachable; the states before project to no TLA+ state.
- **Majorities (`Cardinality(Q) * 2 > Cardinality(Node)`).** Stated exactly by common.ts's `majority`: the request
  carries Q, within 0 .. size − 1, and an injective rank `Out` on the nodes outside it below its input c, with 2c <
  size. For every majority Q, c = |Node \ Q| and a numbering of Node \ Q make it hold; wherever it holds, |Node \ Q| <=
  c < size / 2. That is counting, the pigeonhole reason two majorities meet, which no EPR prover has.
- **Quorums as a set (`CONSTANT Quorum`), as majorities.** Every config's Quorum is the majorities of its nodes
  ({{n1,n2},{n1,n3},{n2,n3}}, with {n1,n2,n3} in two), so these ports take the majorities too, by `majority`. That is
  narrower than the TLA+ (any family of sets; the specs of consensus_wo_decide and consensus_forall don't even state that
  two quorums meet, without which the property is false), and the same on every config's instance. The general form,
  Ivy's `sort quorum` with `member(N, Q)` and the axiom `forall Q1, Q2. exists N. member(N, Q1) & member(N, Q2)`, can't
  be written in the model format: a quorum's members would be a function read at a quantified key (`\A n:
  member(n, q) => ...`), and kernel/kernel.ts's `keyOnly` refuses a function there ("a function's values don't stop
  where a map's cells do"); as a map keyed by (quorum, node), the axiom's witness map is read at a key built from the
  quantified quorum twice, which `keyOnly` refuses too. The ten (../models.ts) stand the axiom in for one stored quorum
  and a request-named witness; that is a modelling choice per protocol, not the spec, so it isn't used here.
- **mldr's counts.** `Quorums(config[i])`, `ConfigIsCommitted` and `QuorumsOverlap(config[i], newConfig)` by exact
  counts with injections as witnesses (a lower bound by an injection into the set, an upper bound by one out of it):
  Q is in Quorums(X) iff Q ⊆ X and |Q| > |X \ Q|; X's and Y's quorums overlap iff two disjoint majorities can't be cut
  from them, i.e. iff (|X|/2 + 1 ∸ |X \ Y|) + (|Y|/2 + 1 ∸ |Y \ X|) > |X ∩ Y| (halves rounded down). Init's single
  `initConfig` copied to every server is a setup phase (`pick`, `copy` per server, `start`).
- **A guard that reads a relation along its first coordinate.** A quantified flag reads its key only as the last
  coordinate (../README.md), so where a guard ranges over one coordinate and another guard over the other (naive
  consensus's `\A x: <<n, x>> \notin vote` beside `\A n \in Q: <<n, v>> \in vote`), the relation is laid out for the
  second, and the first reads `Voted[n]`, a map every write keeps equal to `\E x: <<n, x>> \in vote` (votes are only
  added). naive_consensus (Voted) and simple_election (Promised) have one; no other port adds a variable.
- **Safety with an existential.** PCorrect (`(\A i: pc[i] = "Done") => \E i: y[i] = 1`) is written as its prenex form
  `\E i: pc[i] # "Done" \/ y[i] = 1`; the others (`ResponseMatched`, firewall's, no-lost-keys') as they read, with
  `exists`.

## Not ported, and why

- **i4-learning-switch, pyv-learning-switch.** Both update `route_tc` / `table` at every tuple of a row by a join of
  two other cells of that row: `(pa, x, y)` becomes `tc(pa, x, y) \/ (tc(pa, x, sw1) /\ tc(pa, sw0, y))`. A write at
  every key reads its key only plainly (k, or k plus a term that doesn't read it; kernel/kernel.ts's `keyOnly`), and
  `tc(pa, x, sw1)` at the key `pa·N² + x·N + y` needs y (`k mod N`), a function of the key. No layout of the three
  coordinates avoids it: each read changes a different coordinate. Porting them needs a write over a tuple of keys
  (`M.each((pa, x, y) => ...)`), a change to the kernel's key rules (trusted: a Lean proof first).
- **pyv-paxos-epr.** Its quorums are a sort with the intersection axiom (above: not writable here), and `propose` reads `\A N, MAXR, V: member(N, q) /\ MAXR < r /\ vote(N, MAXR, V) => MAXR <= maxr`:
  a guard quantified over two coordinates of `vote` at once (N and MAXR). A quantified flag over several keys reads
  each on its own (kernel.ts's `apart`), so `vote(N, MAXR, V)` at `N·N² + MAXR·N + V` is out. The same kernel change
  (keys that are tuples) would admit it; so would a log of votes (a list read at one position), at the cost of a
  variable the spec doesn't have and ∀∃ invariants linking it to `vote`.

## Checked against TLC

Each port's reachable states on its instance (check.ts, the BFS of the port, read as the spec's variables) against TLC's
distinct states on the same constants (tlc.py: TLC 1.8.0 on Endive 8b6f2ab, `-deadlock`), and `bad`: the port's
reachable states that break the property (0 for each port; above 0 for the broken variant, so the property is not
vacuous there). `runs/ic3syn/check*.jsonl` in ../gdp-wired-laneA.

| port | TLC | port | broken variant reaches a bad state |
| --- | --- | --- | --- |
| consensus | 4 | 4 | yes |
| tcommit | 34 | 34 | yes |
| lock_server | 9 | 9 | yes |
| quorum_leader_election | 94 | 94 | yes |
| toy_consensus_forall | 41 | 41 | yes |
| simple | 193 | 193 | yes |
| simple_regular | 109 | 109 | yes |
| lockserv_automaton | 80 | 80 | yes |
| sharded_kv | 121 | 121 | (the BFS of the broken variant ran past its cap; the search refutes it in 7 s) |
| sharded_kv_no_lost_keys | 100 | 100 | (ran past its cap) |
| lockserv | 80 | 80 | yes |
| twophase | 288 | 288 | yes |
| simple_decentralized_lock | 12 | 12 | yes |
| two_phase_commit | 1,064 | 1,064 | yes |
| naive_consensus (TLC's VIEW: decide by value) | 55 | 55 | yes |
| client_server_ae | 4,504 | 4,504 | yes |
| client_server_db_ae | 56,416 | 56,416 | yes |
| simple_election | 66 | 66 | yes |
| toy_consensus_epr | 41 | 41 | yes |
| toy_consensus | 41 | 41 | yes |
| firewall | 68 | 68 | yes |
| majorityset_leader_election | 400 | 400 | yes |
| consensus_epr | 110,464 | 110,464 | (ran past its cap) |
| consensus_wo_decide (all four majorities) | 102,912 | 135,872 | |
| consensus_wo_decide (the config's three) | 102,912 | 102,912 | |
| consensus_forall (the config's three) | @FA_T@ | @FA_P@ | |
| mldr | 5,362 | 1,596 inside the constraint, 2,966 past it | **no**: not verified (below) |

- consensus_wo_decide stores the quorum it chose; its config lists the three 2-sets and not the full set, a majority too,
  so the port with every majority has states the config doesn't (a stored full set). At the config's three it is
  checked again.
- **mldr is not verified.** TLC's 5,362 against the port's 1,596 states within `StateConstraint` and 2,966 past it
  (4,562; TLC counts a state past the constraint as found and explores none), and its broken variant (BecomeLeader
  without a majority) reaches no state with two primaries in one term on the instance, which the spec's does: the port
  likely enables too few BecomeLeader steps (its counting witnesses, or the copied initial configs). Its measured
  verdict (no verdict: its first proof never finishes building instances) doesn't rest on it, but no claim about mldr's
  semantics does either.
- consensus_epr's `SendVote` write was later rewritten as one write of the relation (`requests or votes with nondet` to
  1, `votes` without it to 0): the same cells, not checked again.
- The depths differ by one (TLC counts the initial state as level 1) and by a setup phase's length where the port has
  one; only the counts are compared.
