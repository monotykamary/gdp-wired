# Item 3 — fresh TLC correspondence audit (final bounded results)

Baseline: `claude/verify-all`, `6a3874d3f2c6febe40bb14775884cb327a2cce3c`.
Only audit scripts/report under `research/verify-all/`; logs `runs/verify-all/tlc-*`. No source/harness changes.

## Commands

```sh
supercomputer run --jobs research/verify-all/tlc-jobs-20261109.json --out runs/verify-all/tlc-20261109-first --class submission --vm-type large --timing --backend boat
supercomputer run --jobs research/verify-all/tlc-source-jobs-20261109.json --out runs/verify-all/tlc-20261109-sources --class submission --backend boat
supercomputer run --jobs research/verify-all/tlc-retry-jobs-20261109.json --out runs/verify-all/tlc-20261109-retry --class submission --vm-type large --timing --backend boat
```

First command launches 29 jobs running `python3 research/verify-all/tlc-audit-run-20261109.py ID [MS]`: unchanged `check.ts --cfg`, pinned Endive download, harness-declared fixes in isolated copy, fresh TLC 1.8.0 with DOT, unchanged `check.ts --edges` and `--broken`. Finite child process deadlines; exclusive large placement requested; affinity recorded. Each `RESULT` records source/config/JAR/DOT hashes and counts, while `RECEIPT` records full command/exit/wall. Compressed evidence contains full logs/config and pre/post TLA. `tlc-decode-20261109.py` only decodes returned evidence locally, never runs models. Graph hashes returned, full graph remains ephemeral on boat.

Initial-wrapper failure to retain: it tried reading `PaxosEprPyv.tla` before the harness fix creates that module. Wrapper fixed to allow missing original. Initial Paxos attempt and subsequent fresh retry must be distinguished. No correspondence success until completion receipts arrive.

## Scope/limitations

Counts are not bisimulation: `check.ts:25-29` projects raw interpreter states to source states; `:34-47,57-62` collapses phase paths and counts non-self distinct edges. Phase traversal silently caps at 10,000 states (`:37`); exceptions are treated as refused transitions (`:41,56`). The elapsed budget is checked once per frontier (`:52`); `done:false` or killed jobs are incomplete. Constraint-boundary states are recorded separately (`:65`). `c.states` is only an optional historical output (`:74`), not evidence used by this audit. Equal cardinalities can hide different state/edge sets. This is a check on the specified small instances, not all parameters, and not the production proof.

Some quorum families are restricted to majorities (`README.md:122-133`); consensus-with/without-decide checks the config's three pairs, not the full majority also permitted by the port (`models.ts:940-945`). Naive consensus adds a quotient VIEW (`models.ts:950-952`). Learning-switch and MLDR have state constraints (`models.ts:1008-1010,1034-1036`).

Source inspection confirms the two documented Endive Paxos errors: `runs/verify-all/tlc-20261109-sources/endive-paxos_epr.tla:80` keeps `left_rnd` unchanged, and `:102,125` transpose the r/v arguments of Decide. There is also a separate apparent transcription error at `:88`: the quantifier ranges over `mr` but membership reads `<<n,maxr,mv>>` instead of `<<n,mr,mv>>`. This third observation is source inspection, not a measured counterexample.

The pinned mypyvy source uses an arbitrary total round order and intersecting quorum sort (`mypyvy-paxos_epr.pyv:15-21`), while the port/transcribed TLC restricts them to bounded natural order and majorities. Its five transition clauses (`:38-77`) match the intended Send1a, JoinRound (including left-round update), Propose, CastVote and Decide shapes in `models.ts:734-759`; its safety is `:81`. The source’s five additional invariant declarations (`:84-97`) are not part of the TLC Init/Next used here.

Paxos TLC source is a second hand transcription (`models.ts:725-762,1020-1028`), not the faulty committed Endive `paxos_epr.tla`. Thus finite agreement against it shares author/translation assumptions. The independent pinned mypyvy source and original Endive source were fetched by the source job for clause inspection, not generated from the port.

## Invariant-aware representations

Read-only handoff `private/handoff/claude-tracks-20261107/AFTER-MLDR.md:39-41` identifies MLDR's arithmetic QuorumsOverlap and “the P* port” as chosen knowing the invariant. MLDR implementation is identifiable (`models.ts:764-797,813-814`): dx=|X\\Y|, dy=|Y\\X|, m=|X∩Y| and half sizes yield `max(0,floor(|X|/2)+1-dx)+max(0,floor(|Y|/2)+1-dy)>m`. Source job independently exhausts nonempty subset pairs on universes 1..6: **5,214 pairs, zero mismatches** against the all-majority-pairs definition. This is finite arithmetic corroboration, not an all-size proof or removal of hindsight bias.

**P* remains unresolved.** Audit supplies no ID mapping; the Main coordinator also had no mapping. Do not guess it means Paxos. Finite TLC agreement cannot establish that any representation was chosen blindly.

Source job complete on boat, exit 0 (0.67 seconds job time); retained `runs/verify-all/tlc-20261109-sources/tlc-source-audit.log`:
- mypyvy 12a8f5434a25587c56814d090b6ab7fa95851e71 `examples/pd/paxos_epr.pyv`: SHA-256 `b19d164c17601768b12342573256e5b802c9b30b5b2ec62e1679ffefe49f8ebd`.
- Endive 8b6f2abd1988eeb308f965813635e9871f253e2d `benchmarks/paxos_epr.tla`: `f466e55f144a8660d3372f4e9d109e46c2b0e3f0e12d3f1e0294638c098312d5`.
- same Endive `MongoLoglessDynamicRaft.tla`: `c09dd60a54f2dc66c2f58087bbeb49b7686be0425f8af3eb1f10a9299ae73e8e`.

## Correspondence results — terminal, bounded

**28/29 ports have completed fresh TLC and unchanged port BFS with equal state AND non-self directed-edge counts. No completed count mismatch was found. `learning_switch` remains NOT ESTABLISHED:** TLC completed (43,672 states, 258,084 edges), but the port process emitted no result and was killed at both the initial 180-second and retry 660-second outer deadlines. This is not a measured count mismatch and must not be reported as 29/29 correspondence.

Both evidence-producing batches terminated: first batch 29/29 scheduler jobs exit 0, 510.8 seconds wall; retry 5/5 scheduler jobs exit 0, 798.8 seconds wall. The wrapper catches errors and still exits 0, so these scheduler exit counts are NOT model-check completion counts. The table below uses inner TLC/port results. All TLC checks in the final per-ID table completed successfully with exit 0 and no invariant violation; all 28 completed normal port runs have `bad=0`.

Initial incomplete attempts, retained without overwriting:
- `paxos_epr`: initial wrapper FileNotFoundError before running TLC (it tried to hash the not-yet-created `PaxosEprPyv.tla`). Fixed wrapper retry completed **7,377 states / 23,578 edges** on both sides. Initial script is preserved as `tlc-audit-run-initial-20261109.py`, retry script as `tlc-audit-run-retry-20261109.py`.
- `consensus_forall`: initial `done=false`, 111,669 states / 628,704 edges at 121,024ms, not a mismatch; retry completed **112,128 / 633,024**.
- `learning_switch`: port exit -9/no JSON at both 180s and 660s. Fresh TLC on each attempt completed 43,672 / 258,084. No dependency failure was involved; this is the named execution wall.
- Broken `consensus_epr`: first result `bad=0,done=false`; retry killed at 660s/no JSON. Broken `consensus_forall`: `bad=0,done=false` even in the 600,000ms retry. Nonvacuity from these two broken BFS runs is **not established**. Broken `consensus_wo_decide` recovered in retry (`bad=2,done=true`). Across all attempts, 27/29 broken variants reached bad states. Broken `done=true` means stopped after discovering bad states, not exhaustive completion.

Every retry re-ran fresh TLC; the longer budget did not change the source, inputs, constraints, projections, or port harness. The first 29 and retry 5 jobs were exclusive large placements, zero co-tenants, all 8/8 vCPUs pinned; per-job CPU model and VM are retained in each batch's `placement.json`. Hardware includes Ryzen 9 9950X, EPYC 4585PX, and EPYC 9455: these are not controlled cross-hardware timing comparisons.

Complete table and all 34 attempts (including failures), effective-source/config hash table: [tlc-results-20261109.md](tlc-results-20261109.md). Machine-readable full receipts, original/effective source hashes, DOT hashes, timings, command arrays and cwd: [tlc-evidence-20261109.json](../../runs/verify-all/tlc-evidence-20261109.json). Full decoded logs and actual source/config text: `runs/verify-all/tlc-20261109-first-decoded/tlc-<id>/` and `runs/verify-all/tlc-20261109-retry-decoded/tlc-<id>/`. Raw returned log envelopes, `summary.tsv`, and placements remain in corresponding first/retry directories.

### All 29 final bounded rows

| ID | TLC states | TLC edges | TLC complete / exit | port states | port edges | port done / exit | port bad | broken bad / done / exit |
|---|---:|---:|---|---:|---:|---|---:|---|
| client_server_ae | 4504 | 15824 | true / 0 | 4504 | 15824 | true / 0 | 0 | 2 / true / 0 |
| client_server_db_ae | 56416 | 220128 | true / 0 | 56416 | 220128 | true / 0 | 0 | 4 / true / 0 |
| consensus | 4 | 3 | true / 0 | 4 | 3 | true / 0 | 0 | 3 / true / 0 |
| consensus_epr | 110464 | 717504 | true / 0 | 110464 | 717504 | true / 0 | 0 | — / — / -9 |
| consensus_forall | 112128 | 633024 | true / 0 | 112128 | 633024 | true / 0 | 0 | 0 / false / 0 |
| consensus_wo_decide | 102912 | 585792 | true / 0 | 102912 | 585792 | true / 0 | 0 | 2 / true / 0 |
| firewall | 68 | 102 | true / 0 | 68 | 102 | true / 0 | 0 | 1 / true / 0 |
| learning_switch | 43672 | 258084 | true / 0 | — | — | — / -9 | — | 1 / true / 0 |
| learning_switch_i4 | 240 | 300 | true / 0 | 240 | 300 | true / 0 | 0 | 1 / true / 0 |
| lock_server | 9 | 24 | true / 0 | 9 | 24 | true / 0 | 0 | 1 / true / 0 |
| lockserv | 80 | 204 | true / 0 | 80 | 204 | true / 0 | 0 | 1 / true / 0 |
| lockserv_automaton | 80 | 204 | true / 0 | 80 | 204 | true / 0 | 0 | 1 / true / 0 |
| majorityset_leader_election | 400 | 993 | true / 0 | 400 | 993 | true / 0 | 0 | 8 / true / 0 |
| mldr | 5362 | 18327 | true / 0 | 5362 | 18327 | true / 0 | 0 | 5 / true / 0 |
| naive_consensus | 55 | 106 | true / 0 | 55 | 106 | true / 0 | 0 | 9 / true / 0 |
| paxos_epr | 7377 | 23578 | true / 0 | 7377 | 23578 | true / 0 | 0 | 137 / true / 0 |
| quorum_leader_election | 94 | 201 | true / 0 | 94 | 201 | true / 0 | 0 | 25 / true / 0 |
| sharded_kv | 121 | 440 | true / 0 | 121 | 440 | true / 0 | 0 | 2 / true / 0 |
| sharded_kv_no_lost_keys | 100 | 400 | true / 0 | 100 | 400 | true / 0 | 0 | 4 / true / 0 |
| simple | 193 | 388 | true / 0 | 193 | 388 | true / 0 | 0 | 1 / true / 0 |
| simple_decentralized_lock | 12 | 18 | true / 0 | 12 | 18 | true / 0 | 0 | 2 / true / 0 |
| simple_election | 66 | 144 | true / 0 | 66 | 144 | true / 0 | 0 | 9 / true / 0 |
| simple_regular | 109 | 216 | true / 0 | 109 | 216 | true / 0 | 0 | 1 / true / 0 |
| tcommit | 34 | 93 | true / 0 | 34 | 93 | true / 0 | 0 | 5 / true / 0 |
| toy_consensus | 41 | 80 | true / 0 | 41 | 80 | true / 0 | 0 | 11 / true / 0 |
| toy_consensus_epr | 41 | 80 | true / 0 | 41 | 80 | true / 0 | 0 | 9 / true / 0 |
| toy_consensus_forall | 41 | 80 | true / 0 | 41 | 80 | true / 0 | 0 | 11 / true / 0 |
| two_phase_commit | 1064 | 2736 | true / 0 | 1064 | 2736 | true / 0 | 0 | 1 / true / 0 |
| twophase | 288 | 653 | true / 0 | 288 | 653 | true / 0 | 0 | 5 / true / 0 |


### Canceled extra recovery — NOT a check failure or mismatch

Two additional learning-switch recovery jobs were launched just before Main requested final bounded integration, then explicitly canceled at Main's direction. They are **excluded from the correspondence counts**. Batch `20261109-091520-1u673h`, job names `tlc-learning_switch-states` and `tlc-learning_switch-edges`; proposed budgets 600s states-only and 1800s edges. No results from these jobs are claimed.

Cleanup used `kill -TERM 16905` on the exact owning supercomputer coordinator, not a broad kill or another client's process. Supported handler: installed `supercomputer/boat.py:2642-2651` converts SIGTERM into KeyboardInterrupt; `:2951-2956` runs session close; `scheduler.py:1302-1329` closes only that batch and kills its owned runs. Coordinator terminated exit 130. Scheduler log confirms **both exact remote runs killed** at 09:17:12: states on `bx_2uat3ctg`, edges on `bx_395wpmqp`.

Retained cancellation receipts:
- `runs/verify-all/tlc-20261109-learning-recovery/cancellation-coordinator.log`, SHA-256 `9a73f94cb0bfb9bb4b9236df81a8e8a14bc424cf8373fecc57bafa2fe55065d6`.
- `runs/verify-all/tlc-20261109-learning-recovery/cancellation-scheduler.log`, SHA-256 `deaf1bc98008eb049e56d4a6ab65e42e7e111c25b2a6740d6d9961f9eea46c05`.

No audit task remains running. No commits, pushes, branch switches, source/harness edits, worktree recreation, ignored/untracked cleanup, cache clearing, or external solvers were used.

### Fixed source/tool hashes

All evidence-producing jobs report the same five baseline SHA-256 values:

| Path | SHA-256 |
|---|---|
| `research/protocols/ic3syn/models.ts` | `5d61b846a8331a9b7978b4809d53b88e5918135ded0fc6d527f2a6dc8fb3a601` |
| `research/protocols/ic3syn/common.ts` | `d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324` |
| `research/protocols/ic3syn/check.ts` | `bd864cae07b3f864ae3b6b34d454bba8b8699c84d5e679170c8c5b8458cf9161` |
| `research/protocols/ic3syn/tlc.py` | `a6090247849581aa479f4b1ef96d1d71d314e2c1402a5ec3c5e7de045a2f93a3` |
| `research/protocols/ic3syn/README.md` | `5c480248781ca6717958529234d17023a3f6303289f67cb51f617c5f17ae68e2` |
| downloaded TLC 1.8.0 JAR | `e1f11b75c4b5bc4478ba0ac5cb6ae28e40a01b0016bc33e0aa97da22dfdbcd7f` |
| initial audit wrapper | `5533c1142360837d8b83033a4832eec211a6b6ca031ed23a4307490c16e7555e` |
| fixed evidence-producing retry wrapper | `abb36ae0972fbb97fa62a70efe3f72960818667b9f7b6c073943935cc8ee78dc` |

### Verdict

Finite state/edge cardinality agreement is independently reproduced for **28 models**, including MLDR and the hand-transcribed Paxos TLC model. **Learning-switch correspondence remains incomplete**, and none of this is a proof of state/edge-set isomorphism, arbitrary-size translation correctness, blind representation selection, or the production proof path. MLDR hindsight is explicitly identified; P* remains an unresolved label. Those qualifications must accompany the measured count.
