# Thirteen overrunning originals: measured loop attribution

Baseline: `646811df`. Positions below are on that baseline, not on the patched
source. Every diagnostic preserved the baseline raw vector and complete verdict
(byte-for-byte structured equality), checked independently on Boat.

The gap is exact counted work **between two endpoint reads**. Sparse evaluation
stack samples locate the loop bodies in that interval; their per-site sample
weights are not presented as exact per-loop counts. Full intervals, stacks and
first-over-endpoint observations are retained in `results/` and `loops.json`.

| Original | Total work before fix | Largest interval between endpoint reads | Loop body in that interval |
|---|---:|---:|---|
| lock_server | 38611286.018 | 10887776 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| lockserv_automaton | 26677468.6517 | 3872036 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| sharded_kv_no_lost_keys | 30652019.2006 | 8524418 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| sharded_kv | 29809816.2944 | 9416656 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| lockserv | 26755652.0715 | 3937184 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| twophase | 28493397.6996 | 2949638 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| simple_decentralized_lock | 34925852.65 | 10904643 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| two_phase_commit | 29761075.4265 | 3786262 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| client_server_db_ae | 28612381 | 1016813 | core/infer.ts:2327–2364 (instance BFS/steps) |
| client_server_ae | 38485136 | 11259763 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| firewall | 29868514.944 | 13475276 | core/infer.ts:1515–1528 (rowsOf.go view bindings) |
| learning_switch | 24293246.629 | 659399 | core/fresh.ts:32–53 (trial/step loops) |
| learning_switch_i4 | 29868571.014 | 419843 | core/infer.ts:305 and 2327–2364 (relation tuples/instance) |

For the view-binding cases the surrounding reads are `core/infer.ts:1433`
and `core/infer.ts:3259` via `stop` at `:689`; neither polls inside the
Cartesian binding loop. Separately, preflight `core/watch.ts:110` polls every
256 bindings, but `core/dsl.ts:2841,2894` discarded BudgetExpired and later
phases continued. Some refutation loops read an expired endpoint and returned
normally; the caller then entered a new phase. These mechanisms can compose.

`CHECKPOINTS.md` gives each new check in the fixed source. Existing local
deadlines and their normal-return/fallback behavior remain unchanged; only
the enclosing counted endpoint causes the new cancellation outcome.
