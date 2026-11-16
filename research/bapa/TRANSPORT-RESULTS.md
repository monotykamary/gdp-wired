# Per-case transport results

This is a status report, **not a checked fragment recognizer**. The original
`cutoff-inventory.json` is unchanged (29 cases, 67 declarations, 897 indexed
obligations). No per-obligation membership or cutoff is inferred from names,
counts, successful finite checks, or these rows.

| Case | New all-size result |
|---|---|
| consensus | Not established |
| tcommit | **Direct no-search certificate lift**, every natural RM size, including zero |
| lock_server | Not established |
| quorum_leader_election | Not established |
| toy_consensus_forall | **Direct no-search certificate lift**; all 16 obligations and family checked, surviving-bound mutant rejected |
| simple | Not established |
| simple_regular | Not established |
| lockserv_automaton | Not established |
| sharded_kv | Not established |
| sharded_kv_no_lost_keys | Not established |
| lockserv | Not established |
| twophase | Not established |
| simple_decentralized_lock | Not established |
| two_phase_commit | Not established |
| consensus_wo_decide | Not established |
| consensus_forall | Not established |
| naive_consensus | Not established |
| client_server_ae | Not established (both retained subfamilies) |
| client_server_db_ae | Not established |
| simple_election | Not established |
| toy_consensus_epr | Not established |
| toy_consensus | Not established |
| firewall | Not established (both retained subfamilies) |
| majorityset_leader_election | Not established |
| consensus_epr | Not established |
| learning_switch | Not established |
| learning_switch_i4 | Not established |
| paxos_epr | Not established |
| mldr | Not established |

The tcommit result is about the emitted numeric machine with only its size cap
removed; its request and transition evaluators are definitionally unchanged.
Both certificate tables/trees are unchanged. The old source was rechecked,
then the transported checker result and all-size safety were checked in Lean.
It is **not** a new search, a source/TLA+ correspondence proof, a positive
relational-recognizer decision, or a cutoff-based family lift.

The toy_consensus_forall result erases size/value bounds consistently and
prunes obsolete bound-case splits, then rechecks the kept subtree from an empty
path for all target values. All count definitions, request evaluation and state
transition evaluation are unchanged. Its surviving-bound-row mutant is rejected
both as an individual step and as a complete family. This is another direct
numeric certificate lift, not a generic cutoff or source-projection result.
See `TOY-TRANSPORT.md` and `toy-transport.tsv`.

The generic development proves a finite many-sorted, nonempty, function-free
countermodel language, its representation in existing numeric kernel semantics,
and the abstract per-sort small-satisfiability bound
`constants + existential witnesses + 1`. Fixed-64 sorts and empty sorts are
excluded from this initial fragment. No generic family has been lifted using
that theorem: the exact obligation elaborator and retained-certificate coverage
bridge remain unproved. See `TRANSPORT-OBSTACLE.md`.

No new axiom beyond `propext`, `Classical.choice`, `Quot.sound`; no trusted kernel
or canonical protocol edit; no proof search; no push. All Lean checks ran only
through supercomputer with both requested controller/no-build environment flags.
