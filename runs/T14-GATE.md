# T-14 lane-local iteration evidence (before Section 16)

Not a Lane D one-command final-gate receipt; this evidence alone does not authorize a merge.

Implementation: `1681e8e5` plus the test-only deterministic packed-domain route check.
Baseline: `b788e195`. All original-harness verdicts use `--ms 60000` under `timeout -s KILL 60`.

## Verdicts

- IC3Syn: 28/28 already-proven protocols retained in each of three paired repeats; MLDR unknown on both sides.
- DuoAI: 10/10 proven on both sides in each of three repeats.
- Broken variants: none proven; 11 refuted, 17 unknown, one strict kill on each side.
- Generation: 87 pairs, zero solver queries, all other 28 canonical lists identical x3; MLDR 34 to 35.
- Tests: six shards pass in `t14-gate-v1`; the repaired shard 2 and type/lint/commitlint pass in `t14-capture-v2`.
- Quick bar: `t14-bar/runs/t14-post-recovery/REPORT.md`: wrong 0 and solid losses 0; three non-solid CHC losses remain reported there.

## Every changed counted-work row

`full` is the harness raw weighted counter; `work` is its scalar work counter. These are not wall seconds.
The JSON summaries retain full precision, complete harness outcomes, helper attempts, and CPU provenance.

| pair | baseline full | candidate full | baseline work | candidate work | verdicts |
| --- | ---: | ---: | ---: | ---: | --- |
| broken-learning_switch_i4 | 909331 | 899896 | 407578 | 406984 | unknown / unknown |
| broken-paxos_epr | 12999248 | 15002920 | 145967329 | 96053925 | unknown / unknown |
| duo-distributed_lock-1 | 974781.5015 | 978420.2686000001 | 1466334 | 1469172 | proven / proven |
| duo-distributed_lock-2 | 974781.5015 | 978420.2686000001 | 1466334 | 1469172 | proven / proven |
| duo-distributed_lock-3 | 974781.5015 | 978420.2686000001 | 1466334 | 1469172 | proven / proven |
| duo-ring_leader_election-1 | 2242375.0865999996 | 2242686.2766 | 2061954 | 2062066 | proven / proven |
| duo-ring_leader_election-2 | 2242375.0865999996 | 2242686.2766 | 2061954 | 2062066 | proven / proven |
| duo-ring_leader_election-3 | 2242375.0865999996 | 2242686.2766 | 2061954 | 2062066 | proven / proven |
| safe-consensus_epr-1 | 1488593 | 3251570 | 7364433 | 10307227 | proven / proven |
| safe-consensus_epr-2 | 1488593 | 3251570 | 7364433 | 10307227 | proven / proven |
| safe-consensus_epr-3 | 1488593 | 3251570 | 7364433 | 10307227 | proven / proven |
| safe-consensus_forall-1 | 2665853 | 4557617 | 14498189 | 13236043 | proven / proven |
| safe-consensus_forall-2 | 2665853 | 4557617 | 14498189 | 13236043 | proven / proven |
| safe-consensus_forall-3 | 2665853 | 4557617 | 14498189 | 13236043 | proven / proven |
| safe-consensus_wo_decide-1 | 1365323 | 3256966 | 6321466 | 8144267 | proven / proven |
| safe-consensus_wo_decide-2 | 1365323 | 3256966 | 6321466 | 8144267 | proven / proven |
| safe-consensus_wo_decide-3 | 1365323 | 3256966 | 6321466 | 8144267 | proven / proven |
| safe-majorityset_leader_election-1 | 594997 | 583488 | 2007722 | 1951109 | proven / proven |
| safe-majorityset_leader_election-2 | 594997 | 583488 | 2007722 | 1951109 | proven / proven |
| safe-majorityset_leader_election-3 | 594997 | 583488 | 2007722 | 1951109 | proven / proven |
| safe-mldr-1 | 921136 | 4293541 | 2657026 | 22654814 | unknown / unknown |
| safe-mldr-2 | 921136 | 12441878 | 2657026 | 44752739 | unknown / unknown |
| safe-mldr-3 | 921136 | 8605456 | 2657026 | 35929674 | unknown / unknown |
| safe-naive_consensus-1 | 221514 | 2643797 | 693719 | 2168401 | proven / proven |
| safe-naive_consensus-2 | 221514 | 2643797 | 693719 | 2168401 | proven / proven |
| safe-naive_consensus-3 | 221514 | 2643797 | 693719 | 2168401 | proven / proven |
| safe-paxos_epr-1 | 1135224 | 1048638 | 8719080 | 7063901 | proven / proven |
| safe-paxos_epr-2 | 1135224 | 1048638 | 8719080 | 7063901 | proven / proven |
| safe-paxos_epr-3 | 1135224 | 1048638 | 8719080 | 7063901 | proven / proven |
| safe-quorum_leader_election-1 | 68379 | 68971 | 77815 | 80240 | proven / proven |
| safe-quorum_leader_election-2 | 68379 | 68971 | 77815 | 80240 | proven / proven |
| safe-quorum_leader_election-3 | 68379 | 68971 | 77815 | 80240 | proven / proven |
| safe-simple_election-1 | 158981 | 2626155 | 332692 | 2195137 | proven / proven |
| safe-simple_election-2 | 158981 | 2626155 | 332692 | 2195137 | proven / proven |
| safe-simple_election-3 | 158981 | 2626155 | 332692 | 2195137 | proven / proven |
| safe-simple_regular-1 | 7031328 | 6915743 | 3002537 | 2951343 | proven / proven |
| safe-simple_regular-2 | 6557540 | 7062125 | 2794730 | 3014455 | proven / proven |
| safe-simple_regular-3 | 7022347 | 6533083 | 2997886 | 2779878 | proven / proven |
| safe-simple-1 | 8034081 | 7600881 | 3609053 | 3414060 | proven / proven |
| safe-simple-2 | 6426679 | 6680728 | 2869863 | 2984858 | proven / proven |
| safe-simple-3 | 5685392 | 6287982 | 2528011 | 2811108 | proven / proven |
| safe-toy_consensus_epr-1 | 185783 | 185768 | 572283 | 571270 | proven / proven |
| safe-toy_consensus_epr-2 | 185783 | 185768 | 572283 | 571270 | proven / proven |
| safe-toy_consensus_epr-3 | 185783 | 185768 | 572283 | 571270 | proven / proven |
| safe-toy_consensus_forall-1 | 91451 | 92056 | 115382 | 117926 | proven / proven |
| safe-toy_consensus_forall-2 | 91451 | 92056 | 115382 | 117926 | proven / proven |
| safe-toy_consensus_forall-3 | 91451 | 92056 | 115382 | 117926 | proven / proven |
| safe-toy_consensus-1 | 64652 | 65258 | 76032 | 78435 | proven / proven |
| safe-toy_consensus-2 | 64652 | 65258 | 76032 | 78435 | proven / proven |
| safe-toy_consensus-3 | 64652 | 65258 | 76032 | 78435 | proven / proven |

## CPU model for every strict pair

Each pair ran on one isolated pinned large VM. CPU labels missing after scheduler recovery were recovered only from another receipt with the identical VM ID; each JSON side records that source.

- C1: AMD EPYC 4585PX 16-Core Processor
- C2: AMD EPYC 9455 48-Core Processor
- C3: AMD Ryzen 7 9700X 8-Core Processor
- C4: AMD Ryzen 9 9950X 16-Core Processor

### Full gate

| pair | VM | CPU | baseline seconds | candidate seconds |
| --- | --- | --- | ---: | ---: |
| broken-client_server_ae | bx_2hzfj2ah | C1 | 20.05 | 20.48 |
| broken-client_server_db_ae | bx_8nqy7xab | C4 | 21.62 | 22.1 |
| broken-consensus | bx_8nqy7xab | C4 | 0.03 | 0.04 |
| broken-consensus_epr | bx_5f56ms2a | C1 | 3.7 | 3.52 |
| broken-consensus_forall | bx_5wr3bs76 | C4 | 7.56 | 6.47 |
| broken-consensus_wo_decide | bx_5f56ms2a | C1 | 3.02 | 2.85 |
| broken-firewall | bx_7m649ges | C4 | 6.85 | 6.45 |
| broken-learning_switch | bx_25xas5gt | C2 | 13.08 | 12.97 |
| broken-learning_switch_i4 | bx_2kmf8w3s | C4 | 45.54 | 47.01 |
| broken-lock_server | bx_7m649ges | C4 | 0.03 | 0.04 |
| broken-lockserv | bx_5wr3bs76 | C4 | 0.24 | 0.22 |
| broken-lockserv_automaton | bx_5f56ms2a | C1 | 0.2 | 0.2 |
| broken-majorityset_leader_election | bx_5f56ms2a | C1 | 0.75 | 0.6 |
| broken-mldr | bx_7uaxjs82 | C4 | 10.64 | 10.62 |
| broken-naive_consensus | bx_7m649ges | C4 | 2.01 | 2.15 |
| broken-paxos_epr | bx_7vs7decr | C4 | 45.28 | 54 |
| broken-quorum_leader_election | bx_8nqy7xab | C4 | 0.35 | 0.37 |
| broken-sharded_kv | bx_8nqy7xab | C4 | 2.2 | 2.3 |
| broken-sharded_kv_no_lost_keys | bx_5f32uf5a | C1 | 60 | 60 |
| broken-simple | bx_5wr3bs76 | C4 | 0.03 | 0.04 |
| broken-simple_decentralized_lock | bx_2hzfj2ah | C1 | 0.15 | 0.15 |
| broken-simple_election | bx_8y6xda5y | C4 | 2.08 | 2.22 |
| broken-simple_regular | bx_7m649ges | C4 | 0.03 | 0.04 |
| broken-tcommit | bx_5wr3bs76 | C4 | 0.05 | 0.05 |
| broken-toy_consensus | bx_74ss87e4 | C2 | 0.45 | 0.47 |
| broken-toy_consensus_epr | bx_5jvcbp5r | C4 | 1.33 | 1.3 |
| broken-toy_consensus_forall | bx_5f32uf5a | C1 | 0.69 | 0.72 |
| broken-two_phase_commit | bx_5f56ms2a | C1 | 0.04 | 0.05 |
| broken-twophase | bx_7m649ges | C4 | 0.05 | 0.05 |
| duo-consensus_wo_decide-1 | bx_7vs7decr | C4 | 17.64 | 17.92 |
| duo-consensus_wo_decide-2 | bx_76nnjrpb | C1 | 33.06 | 29.72 |
| duo-consensus_wo_decide-3 | bx_25xas5gt | C2 | 17.75 | 19.53 |
| duo-decentralized_lock-1 | bx_7m649ges | C4 | 7.05 | 7.13 |
| duo-decentralized_lock-2 | bx_5f56ms2a | C1 | 6.47 | 6.5 |
| duo-decentralized_lock-3 | bx_7vs7decr | C4 | 6.64 | 6.31 |
| duo-distributed_lock-1 | bx_5jvcbp5r | C4 | 8.71 | 8.76 |
| duo-distributed_lock-2 | bx_7vpz29xf | C1 | 9.41 | 11.76 |
| duo-distributed_lock-3 | bx_6aqepfyv | C1 | 9.07 | 10.24 |
| duo-lock_server_async-1 | bx_8nqy7xab | C4 | 9.63 | 10.48 |
| duo-lock_server_async-2 | bx_5f32uf5a | C1 | 17.56 | 14.54 |
| duo-lock_server_async-3 | bx_5f56ms2a | C1 | 9.86 | 10 |
| duo-lock_server_sync-1 | bx_8f8tzqk2 | C4 | 5.46 | 5.29 |
| duo-lock_server_sync-2 | bx_5f56ms2a | C1 | 3.82 | 3.71 |
| duo-lock_server_sync-3 | bx_6aqepfyv | C1 | 4.97 | 4.32 |
| duo-ring_leader_election-1 | bx_2kmf8w3s | C4 | 17.97 | 18.81 |
| duo-ring_leader_election-2 | bx_2uat3ctg | C4 | 26.48 | 35.36 |
| duo-ring_leader_election-3 | bx_4cma575j | C1 | 16.36 | 15.84 |
| duo-sharded_key_value_store-1 | bx_5jvcbp5r | C4 | 11 | 9.76 |
| duo-sharded_key_value_store-2 | bx_5mqd7ek5 | C1 | 11.24 | 14.45 |
| duo-sharded_key_value_store-3 | bx_8sf3u958 | C1 | 26.15 | 25.77 |
| duo-ticket_lock-1 | bx_4cma575j | C1 | 6.16 | 6.3 |
| duo-ticket_lock-2 | bx_7ah56czc | C3 | 8.27 | 10.12 |
| duo-ticket_lock-3 | bx_5wr3bs76 | C4 | 9.29 | 9.51 |
| duo-toy_consensus_forall-1 | bx_5mqd7ek5 | C1 | 4.16 | 4.42 |
| duo-toy_consensus_forall-2 | bx_5f56ms2a | C1 | 4.29 | 4.28 |
| duo-toy_consensus_forall-3 | bx_7m649ges | C4 | 4.82 | 4.96 |
| duo-two_phase_commit-1 | bx_6k9k52sn | C4 | 7.53 | 7.48 |
| duo-two_phase_commit-2 | bx_5f32uf5a | C1 | 11.47 | 14.61 |
| duo-two_phase_commit-3 | bx_395wpmqp | C4 | 8.34 | 9.32 |
| safe-client_server_ae-1 | bx_69nkhdf7 | C1 | 13.76 | 13.82 |
| safe-client_server_ae-2 | bx_2uat3ctg | C4 | 14.67 | 18.58 |
| safe-client_server_ae-3 | bx_2hzfj2ah | C1 | 16.71 | 14.54 |
| safe-client_server_db_ae-1 | bx_5mqd7ek5 | C1 | 13.64 | 13.86 |
| safe-client_server_db_ae-2 | bx_8nqy7xab | C4 | 14.28 | 14.85 |
| safe-client_server_db_ae-3 | bx_25xas5gt | C2 | 16.32 | 16.29 |
| safe-consensus_epr-1 | bx_6k9k52sn | C4 | 11.99 | 12.81 |
| safe-consensus_epr-2 | bx_8f8tzqk2 | C4 | 18.01 | 19.78 |
| safe-consensus_epr-3 | bx_5f56ms2a | C1 | 15.75 | 20.15 |
| safe-consensus_forall-1 | bx_7vs7decr | C4 | 17.84 | 17.41 |
| safe-consensus_forall-2 | bx_5wr3bs76 | C4 | 25.1 | 23.24 |
| safe-consensus_forall-3 | bx_8f8tzqk2 | C4 | 28.04 | 23.05 |
| safe-consensus_wo_decide-1 | bx_8nqy7xab | C4 | 10.45 | 11.56 |
| safe-consensus_wo_decide-2 | bx_5f32uf5a | C1 | 13.83 | 15.41 |
| safe-consensus_wo_decide-3 | bx_5mqd7ek5 | C1 | 9.39 | 10.96 |
| safe-consensus-1 | bx_5wr3bs76 | C4 | 0.17 | 0.16 |
| safe-consensus-2 | bx_5f32uf5a | C1 | 0.24 | 0.26 |
| safe-consensus-3 | bx_74ss87e4 | C2 | 0.18 | 0.21 |
| safe-firewall-1 | bx_2uat3ctg | C4 | 30.93 | 29.85 |
| safe-firewall-2 | bx_5f32uf5a | C1 | 19.54 | 25.14 |
| safe-firewall-3 | bx_7vs7decr | C4 | 17.2 | 16.39 |
| safe-learning_switch_i4-1 | bx_395wpmqp | C4 | 18.72 | 17.35 |
| safe-learning_switch_i4-2 | bx_4cma575j | C1 | 17.16 | 16.73 |
| safe-learning_switch_i4-3 | bx_7vs7decr | C4 | 19.01 | 17.97 |
| safe-learning_switch-1 | bx_5wr3bs76 | C4 | 21.61 | 19.86 |
| safe-learning_switch-2 | bx_69nkhdf7 | C1 | 20.28 | 19.7 |
| safe-learning_switch-3 | bx_6k9k52sn | C4 | 13.8 | 14.01 |
| safe-lock_server-1 | bx_2hzfj2ah | C1 | 5.54 | 5.24 |
| safe-lock_server-2 | bx_2uat3ctg | C4 | 4.33 | 4.05 |
| safe-lock_server-3 | bx_25xas5gt | C2 | 4.04 | 4.2 |
| safe-lockserv_automaton-1 | bx_395wpmqp | C4 | 5.59 | 5.7 |
| safe-lockserv_automaton-2 | bx_5wr3bs76 | C4 | 7.16 | 6.98 |
| safe-lockserv_automaton-3 | bx_6k9k52sn | C4 | 4.59 | 4.96 |
| safe-lockserv-1 | bx_5wr3bs76 | C4 | 5.55 | 5.99 |
| safe-lockserv-2 | bx_69nkhdf7 | C1 | 5.35 | 5.88 |
| safe-lockserv-3 | bx_7vs7decr | C4 | 7.22 | 8.73 |
| safe-majorityset_leader_election-1 | bx_5wr3bs76 | C4 | 4.5 | 3.55 |
| safe-majorityset_leader_election-2 | bx_5mqd7ek5 | C1 | 3.28 | 2.67 |
| safe-majorityset_leader_election-3 | bx_69nkhdf7 | C1 | 4.14 | 3.39 |
| safe-mldr-1 | bx_8f8tzqk2 | C4 | 33.4 | 59.24 |
| safe-mldr-2 | bx_5mqd7ek5 | C1 | 20.72 | 59.11 |
| safe-mldr-3 | bx_25xas5gt | C2 | 24.45 | 59.14 |
| safe-naive_consensus-1 | bx_2uat3ctg | C4 | 3.76 | 5.88 |
| safe-naive_consensus-2 | bx_69nkhdf7 | C1 | 3.08 | 5.28 |
| safe-naive_consensus-3 | bx_6aqepfyv | C1 | 3.2 | 5.23 |
| safe-paxos_epr-1 | bx_8nqy7xab | C4 | 19.47 | 17.63 |
| safe-paxos_epr-2 | bx_2kmf8w3s | C4 | 27.9 | 21.93 |
| safe-paxos_epr-3 | bx_2hzfj2ah | C1 | 27.3 | 26.28 |
| safe-quorum_leader_election-1 | bx_6k9k52sn | C4 | 1.85 | 0.81 |
| safe-quorum_leader_election-2 | bx_2kmf8w3s | C4 | 3.8 | 1.33 |
| safe-quorum_leader_election-3 | bx_5f56ms2a | C1 | 3.95 | 1.35 |
| safe-sharded_kv_no_lost_keys-1 | bx_4cma575j | C1 | 6.08 | 6.35 |
| safe-sharded_kv_no_lost_keys-2 | bx_7m649ges | C4 | 7.18 | 8.63 |
| safe-sharded_kv_no_lost_keys-3 | bx_5mqd7ek5 | C1 | 6.31 | 6.23 |
| safe-sharded_kv-1 | bx_8nqy7xab | C4 | 16.8 | 16.57 |
| safe-sharded_kv-2 | bx_5f32uf5a | C1 | 31.62 | 26.8 |
| safe-sharded_kv-3 | bx_2hzfj2ah | C1 | 23.26 | 22.26 |
| safe-simple_decentralized_lock-1 | bx_69nkhdf7 | C1 | 3.41 | 3.51 |
| safe-simple_decentralized_lock-2 | bx_7m649ges | C4 | 3.73 | 3.52 |
| safe-simple_decentralized_lock-3 | bx_7vs7decr | C4 | 3.32 | 3.32 |
| safe-simple_election-1 | bx_6k9k52sn | C4 | 2.57 | 3.82 |
| safe-simple_election-2 | bx_5f32uf5a | C1 | 2.97 | 4.51 |
| safe-simple_election-3 | bx_6k9k52sn | C4 | 2.36 | 3.91 |
| safe-simple_regular-1 | bx_8f8tzqk2 | C4 | 12.4 | 12.07 |
| safe-simple_regular-2 | bx_5wr3bs76 | C4 | 12.26 | 11.59 |
| safe-simple_regular-3 | bx_69nkhdf7 | C1 | 12.46 | 12.42 |
| safe-simple-1 | bx_5jvcbp5r | C4 | 8.94 | 8.71 |
| safe-simple-2 | bx_7vs7decr | C4 | 9.79 | 9.12 |
| safe-simple-3 | bx_7m649ges | C4 | 10.21 | 10.26 |
| safe-tcommit-1 | bx_69nkhdf7 | C1 | 0.35 | 0.41 |
| safe-tcommit-2 | bx_5mqd7ek5 | C1 | 0.24 | 0.26 |
| safe-tcommit-3 | bx_8nqy7xab | C4 | 0.23 | 0.26 |
| safe-toy_consensus_epr-1 | bx_7vs7decr | C4 | 2.3 | 1.62 |
| safe-toy_consensus_epr-2 | bx_69nkhdf7 | C1 | 2.94 | 2.19 |
| safe-toy_consensus_epr-3 | bx_5f32uf5a | C1 | 2.49 | 1.63 |
| safe-toy_consensus_forall-1 | bx_395wpmqp | C4 | 2.46 | 1.78 |
| safe-toy_consensus_forall-2 | bx_4cma575j | C1 | 1.7 | 0.88 |
| safe-toy_consensus_forall-3 | bx_6aqepfyv | C1 | 2.97 | 1.4 |
| safe-toy_consensus-1 | bx_7vs7decr | C4 | 1.97 | 0.9 |
| safe-toy_consensus-2 | bx_6k9k52sn | C4 | 1.59 | 0.82 |
| safe-toy_consensus-3 | bx_5f56ms2a | C1 | 2.78 | 1.26 |
| safe-two_phase_commit-1 | bx_69nkhdf7 | C1 | 9.59 | 8.22 |
| safe-two_phase_commit-2 | bx_7vs7decr | C4 | 7.76 | 7.56 |
| safe-two_phase_commit-3 | bx_8f8tzqk2 | C4 | 8.52 | 8.52 |
| safe-twophase-1 | bx_8f8tzqk2 | C4 | 12.6 | 12.9 |
| safe-twophase-2 | bx_5mqd7ek5 | C1 | 11.91 | 11.14 |
| safe-twophase-3 | bx_5wr3bs76 | C4 | 11.25 | 11.61 |

### T-14 and fixed-share controls

| pair | VM | CPU | baseline seconds | candidate seconds |
| --- | --- | --- | ---: | ---: |
| mldr-pair-1 | bx_5f56ms2a | C1 | 22.7 | 59.41 |
| mldr-pair-2 | bx_395wpmqp | C4 | 37.57 | 59.64 |
| mldr-pair-3 | bx_84e8hfw5 | C4 | 19.85 | 59.17 |
| share-pair-1 | bx_8f8tzqk2 | C4 | 59.57 | 59.9 |
| share-pair-2 | bx_2uat3ctg | C4 | 59.14 | 59.1 |
| share-pair-3 | bx_2hzfj2ah | C1 | 59.15 | 59.11 |

### Corrected research capture

| pair | VM | CPU | baseline seconds | candidate seconds |
| --- | --- | --- | ---: | ---: |
| mldr-pair-1 | bx_2eg9t59n | C2 | 27.91 | 59.36 |
| mldr-pair-2 | bx_8y6xda5y | C4 | 60 | 59.13 |
| mldr-pair-3 | bx_84e8hfw5 | C4 | 49.5 | 59.9 |
