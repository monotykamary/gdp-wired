# Original-model census at 15M

Frozen source: `646811dfbe7ec97729a239012d14593fe92a8503`. All units below are **uncalibrated**.

**10 proved and checked; 18 unknown; 0 refuted.**
No-loss against the prior 28-original census: **true**.
All 28 strict pre-import tripwire runs recorded zero forbidden clock reads.
Normal/strict verdicts and all raw vectors are identical. All 56 hashes,
root/exclusive ledger identities and weighted totals passed the independent audit.

| Original | Previous | This source | Checked | Search units | Why |
|---|---|---|---|---:|---|
| consensus | proven | proven | true | 219557.9687 | — |
| tcommit | proven | proven | true | 305163.0489 | — |
| lock_server | unknown | unknown | false | 38611286.018 | work budget (rule result) |
| quorum_leader_election | proven | proven | true | 3793408.7103 | — |
| toy_consensus_forall | proven | proven | true | 5378302.3047 | — |
| simple_regular | proven | proven | true | 7056778.8214 | — |
| simple | proven | proven | true | 5851080.5079 | — |
| lockserv_automaton | unknown | unknown | false | 26677468.6517 | work budget (rule result) |
| sharded_kv_no_lost_keys | unknown | unknown | false | 30652019.2006 | work budget (rule result) |
| sharded_kv | unknown | unknown | false | 29809816.2944 | work budget (rule result) |
| lockserv | unknown | unknown | false | 26755652.0715 | work budget (rule result) |
| twophase | unknown | unknown | false | 28493397.6996 | work budget (rule result) |
| simple_decentralized_lock | unknown | unknown | false | 34925852.65 | work budget (rule result) |
| two_phase_commit | unknown | unknown | false | 29761075.4265 | work budget (rule result) |
| consensus_forall | unknown | unknown | false | 15000006 | work budget (small) |
| consensus_wo_decide | unknown | unknown | false | 15000002 | work budget (small) |
| naive_consensus | proven | proven | true | 8222540.7277 | — |
| client_server_db_ae | unknown | unknown | false | 28612381 | work budget (rule result) |
| client_server_ae | unknown | unknown | false | 38485136 | work budget (rule result) |
| simple_election | unknown | unknown | false | 15000013.2627 | work budget (mbqi) |
| toy_consensus_epr | proven | proven | true | 6235436.7618 | — |
| toy_consensus | proven | proven | true | 4897833.8743 | — |
| firewall | unknown | unknown | false | 29868514.944 | work budget (rule result) |
| majorityset_leader_election | proven | proven | true | 7368110.198100001 | — |
| consensus_epr | unknown | unknown | false | 15000079 | work budget (small) |
| learning_switch | unknown | unknown | false | 24293246.629 | work budget (rule result) |
| learning_switch_i4 | unknown | unknown | false | 29868571.014 | work budget (rule result) |
| paxos_epr | unknown | unknown | false | 15000430 | work budget (small) |

The original MLDR model is deliberately excluded from these 28 cases. Its
generation-termination work remains with lane A. This does not close full
native/checker metering coverage or calibrate W.
