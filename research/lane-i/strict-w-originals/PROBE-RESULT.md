# Non-MLDR strict-W: first observed crossings

All16 baseline runs were captured and their work exactly matches the original
cap-negative census. Probe runner v1 stayed RED because its finalizer assumed
absolute endpoint15000000, rather than start13 + allowance15000000.
Offset-aware analysis recovered the SAME files; no reproof or source fix.

15 cases cross in evals; sharded_kv crosses in tableCells. These are first
observed budget-check sites, not yet the exact first over-budget AST node.

| Case | Overshoot | First observed site | Charged delta |
|---|---:|---|---|
| lock_server | 120.6860 | core/watch.ts:113:43 | {"evals":315} |
| lockserv_automaton | 12.0997 | core/watch.ts:113:43 | {"evals":196} |
| sharded_kv | 18.2817 | core/prover-row-budget.ts:50:3 | {"tableCells":42} |
| sharded_kv_no_lost_keys | 76.4294 | core/dsl.ts:2855:26 | {"evals":140} |
| lockserv | 178.2075 | core/watch.ts:113:43 | {"evals":210} |
| simple_decentralized_lock | 75.5540 | core/watch.ts:113:43 | {"evals":210} |
| twophase | 59.8476 | core/dsl.ts:2855:26 | {"evals":73} |
| two_phase_commit | 200.9145 | core/watch.ts:113:43 | {"evals":243} |
| consensus_forall | 47.4800 | core/infer.ts:1530:11 | {"evals":74} |
| client_server_ae | 15.1800 | core/watch.ts:113:43 | {"evals":112} |
| client_server_db_ae | 194.8333 | core/watch.ts:113:43 | {"evals":238} |
| firewall | 222.9840 | core/watch.ts:113:43 | {"evals":238} |
| learning_switch | 129.5555 | core/watch.ts:113:43 | {"evals":411} |
| learning_switch_i4 | 58.0140 | core/watch.ts:113:43 | {"evals":90} |
| consensus_epr | 62.3800 | core/infer.ts:1530:11 | {"evals":74} |
| paxos_epr | 1010.0000 | core/infer.ts:813:7 | {"evals":1054} |

Full raw-before/after vectors and stacks: FIRST-CROSSINGS.json.
Fix scope: keep f81c/d105 frozen; patch and gate a separate strict-W branch.
No cap compliance or 1G execution claim.
