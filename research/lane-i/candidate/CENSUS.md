# Historical 28-original no-loss census

Measured candidate: `db14ee14`; baseline: A `5aa76818`.
All runs use unchanged original models, GDP_WORK_FULL=1 and a 15M diagnostic
allowance. This is **not** validation of current exact-tree `7eccce26`.

**PASS: 28 pairs complete, 10 proven+checked on both, 18 unknown on both,
zero errors/refutations/proof regressions.** These are uncalibrated work units.
The complete original-protocol source is byte-identical across A, historical
candidate and current candidate: Git blob `0541fa9436e307a6fb716aa5064637b30b893b79`.

| Original | A | Candidate | A search units | Candidate search units |
|---|---|---|---:|---:|
| consensus | proven | proven | 944743.9687 | 235077.9687 |
| tcommit | proven | proven | 2438449.0489 | 322162.0489 |
| lock_server | unknown | unknown | 15110802.686 | 15111511.686 |
| quorum_leader_election | proven | proven | 6182285.7103 | 4019794.7103 |
| toy_consensus_forall | proven | proven | 8493605.3047 | 5783973.3047 |
| simple_regular | proven | proven | 14363989.049 | 7157472.8214 |
| simple | proven | proven | 8734813.9559 | 5938434.5079 |
| lockserv_automaton | unknown | unknown | 15170293.0997 | 15167641.0997 |
| sharded_kv_no_lost_keys | unknown | unknown | 15828805.4294 | 15822755.2006 |
| sharded_kv | unknown | unknown | 15855126 | 15849623 |
| lockserv | unknown | unknown | 15171619.2075 | 15167742.2075 |
| twophase | unknown | unknown | 15231858.8476 | 15228698.8476 |
| simple_decentralized_lock | unknown | unknown | 15372893.554 | 15370047.554 |
| two_phase_commit | unknown | unknown | 15631106.9145 | 15622391.9145 |
| consensus_forall | unknown | unknown | 15000227 | 15000009 |
| consensus_wo_decide | unknown | unknown | 15000032 | 15000138 |
| naive_consensus | proven | proven | 10431847.7277 | 8596484.7277 |
| client_server_db_ae | unknown | unknown | 15484433 | 15482694 |
| client_server_ae | unknown | unknown | 15199826 | 15195417 |
| simple_election | unknown | unknown | 15001159.5916 | 15000150.2606 |
| toy_consensus_epr | proven | proven | 8149800.7618 | 6613983.7618 |
| toy_consensus | proven | proven | 7510186.874299999 | 5307445.8743 |
| firewall | unknown | unknown | 15147530.944 | 15145588.944 |
| majorityset_leader_election | proven | proven | 13266773.1981 | 7655803.198100001 |
| consensus_epr | unknown | unknown | 15000137 | 15000208 |
| learning_switch | unknown | unknown | 16649823.1599 | 16645626.1586 |
| learning_switch_i4 | unknown | unknown | 16542003.014 | 16522375.014 |
| paxos_epr | unknown | unknown | 15000425 | 15000205 |

The slow `sharded_kv_no_lost_keys` candidate still returned UNKNOWN with a
complete receipt (15,822,755.2006 search units); it did not time out.
The scheduler reported 191.34 seconds on a shared host, versus 3.21 seconds
for A. Those are observation timings, not calibration or native attribution.
Receipt conservation and hashes pass independently; see `results/receipts/`.
