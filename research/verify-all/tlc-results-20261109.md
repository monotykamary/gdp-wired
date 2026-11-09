# Returned TLC/port receipts

Counts are distinct projected states and distinct directed non-self edges. `done` is the unchanged port harness's flag; TLC complete is parsed independently. Broken `done=true` means the harness stopped after finding bad states, NOT exhaustive exploration.

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

## All attempts (including failures)

| ID | attempt evidence | ms budget | TLC state / edge / complete | port state / edge / done / exit | broken bad / done | wrapper error |
|---|---|---:|---|---|---|---|
| client_server_ae | runs/verify-all/tlc-20261109-first-decoded/tlc-client_server_ae/result.json | 120000 | 4504/15824/true | 4504/15824/true/0 | 2/true | none |
| client_server_db_ae | runs/verify-all/tlc-20261109-first-decoded/tlc-client_server_db_ae/result.json | 120000 | 56416/220128/true | 56416/220128/true/0 | 4/true | none |
| consensus | runs/verify-all/tlc-20261109-first-decoded/tlc-consensus/result.json | 120000 | 4/3/true | 4/3/true/0 | 3/true | none |
| consensus_epr | runs/verify-all/tlc-20261109-first-decoded/tlc-consensus_epr/result.json | 120000 | 110464/717504/true | 110464/717504/true/0 | 0/false | none |
| consensus_forall | runs/verify-all/tlc-20261109-first-decoded/tlc-consensus_forall/result.json | 120000 | 112128/633024/true | 111669/628704/false/0 | 0/false | none |
| consensus_wo_decide | runs/verify-all/tlc-20261109-first-decoded/tlc-consensus_wo_decide/result.json | 120000 | 102912/585792/true | 102912/585792/true/0 | 0/false | none |
| firewall | runs/verify-all/tlc-20261109-first-decoded/tlc-firewall/result.json | 120000 | 68/102/true | 68/102/true/0 | 1/true | none |
| learning_switch | runs/verify-all/tlc-20261109-first-decoded/tlc-learning_switch/result.json | 120000 | 43672/258084/true | —/—/—/-9 | 1/true | none |
| learning_switch_i4 | runs/verify-all/tlc-20261109-first-decoded/tlc-learning_switch_i4/result.json | 120000 | 240/300/true | 240/300/true/0 | 1/true | none |
| lock_server | runs/verify-all/tlc-20261109-first-decoded/tlc-lock_server/result.json | 120000 | 9/24/true | 9/24/true/0 | 1/true | none |
| lockserv | runs/verify-all/tlc-20261109-first-decoded/tlc-lockserv/result.json | 120000 | 80/204/true | 80/204/true/0 | 1/true | none |
| lockserv_automaton | runs/verify-all/tlc-20261109-first-decoded/tlc-lockserv_automaton/result.json | 120000 | 80/204/true | 80/204/true/0 | 1/true | none |
| majorityset_leader_election | runs/verify-all/tlc-20261109-first-decoded/tlc-majorityset_leader_election/result.json | 120000 | 400/993/true | 400/993/true/0 | 8/true | none |
| mldr | runs/verify-all/tlc-20261109-first-decoded/tlc-mldr/result.json | 120000 | 5362/18327/true | 5362/18327/true/0 | 5/true | none |
| naive_consensus | runs/verify-all/tlc-20261109-first-decoded/tlc-naive_consensus/result.json | 120000 | 55/106/true | 55/106/true/0 | 9/true | none |
| paxos_epr | runs/verify-all/tlc-20261109-first-decoded/tlc-paxos_epr/result.json | 120000 | —/—/— | —/—/—/— | —/— | FileNotFoundError: [Errno 2] No such file or directory: '/work/gdp-wired/runs/verify-all/tlc-evidence-paxos_epr-41158/benchmarks/PaxosEprPyv.tla' |
| quorum_leader_election | runs/verify-all/tlc-20261109-first-decoded/tlc-quorum_leader_election/result.json | 120000 | 94/201/true | 94/201/true/0 | 25/true | none |
| sharded_kv | runs/verify-all/tlc-20261109-first-decoded/tlc-sharded_kv/result.json | 120000 | 121/440/true | 121/440/true/0 | 2/true | none |
| sharded_kv_no_lost_keys | runs/verify-all/tlc-20261109-first-decoded/tlc-sharded_kv_no_lost_keys/result.json | 120000 | 100/400/true | 100/400/true/0 | 4/true | none |
| simple | runs/verify-all/tlc-20261109-first-decoded/tlc-simple/result.json | 120000 | 193/388/true | 193/388/true/0 | 1/true | none |
| simple_decentralized_lock | runs/verify-all/tlc-20261109-first-decoded/tlc-simple_decentralized_lock/result.json | 120000 | 12/18/true | 12/18/true/0 | 2/true | none |
| simple_election | runs/verify-all/tlc-20261109-first-decoded/tlc-simple_election/result.json | 120000 | 66/144/true | 66/144/true/0 | 9/true | none |
| simple_regular | runs/verify-all/tlc-20261109-first-decoded/tlc-simple_regular/result.json | 120000 | 109/216/true | 109/216/true/0 | 1/true | none |
| tcommit | runs/verify-all/tlc-20261109-first-decoded/tlc-tcommit/result.json | 120000 | 34/93/true | 34/93/true/0 | 5/true | none |
| toy_consensus | runs/verify-all/tlc-20261109-first-decoded/tlc-toy_consensus/result.json | 120000 | 41/80/true | 41/80/true/0 | 11/true | none |
| toy_consensus_epr | runs/verify-all/tlc-20261109-first-decoded/tlc-toy_consensus_epr/result.json | 120000 | 41/80/true | 41/80/true/0 | 9/true | none |
| toy_consensus_forall | runs/verify-all/tlc-20261109-first-decoded/tlc-toy_consensus_forall/result.json | 120000 | 41/80/true | 41/80/true/0 | 11/true | none |
| two_phase_commit | runs/verify-all/tlc-20261109-first-decoded/tlc-two_phase_commit/result.json | 120000 | 1064/2736/true | 1064/2736/true/0 | 1/true | none |
| twophase | runs/verify-all/tlc-20261109-first-decoded/tlc-twophase/result.json | 120000 | 288/653/true | 288/653/true/0 | 5/true | none |
| consensus_epr | runs/verify-all/tlc-20261109-retry-decoded/tlc-consensus_epr/result.json | 600000 | 110464/717504/true | 110464/717504/true/0 | —/— | none |
| consensus_forall | runs/verify-all/tlc-20261109-retry-decoded/tlc-consensus_forall/result.json | 600000 | 112128/633024/true | 112128/633024/true/0 | 0/false | none |
| consensus_wo_decide | runs/verify-all/tlc-20261109-retry-decoded/tlc-consensus_wo_decide/result.json | 600000 | 102912/585792/true | 102912/585792/true/0 | 2/true | none |
| learning_switch | runs/verify-all/tlc-20261109-retry-decoded/tlc-learning_switch/result.json | 600000 | 43672/258084/true | —/—/—/-9 | 1/true | none |
| paxos_epr | runs/verify-all/tlc-20261109-retry-decoded/tlc-paxos_epr/result.json | 600000 | 7377/23578/true | 7377/23578/true/0 | 137/true | none |

## Effective source and configuration hashes

See `runs/verify-all/tlc-evidence-20261109.json` for original source, graph, repo source hashes, all commands/cwd, timings and receipts.

| ID | module | effective TLA SHA-256 | config SHA-256 |
|---|---|---|---|
| client_server_ae | client_server_ae | 6296d3bef08242be47b5d4f74a2e79790860e83cd0f366a83d82a0b7c1aaec3a | 2a50b00a6a0cb9a2d37eea2f0feeb4b890f4082885b1190103c31fd6f3640410 |
| client_server_db_ae | client_server_db_ae | c10176c22e57b310d119a526d18e7eec474919aa5e6d0794e221f70ab8e59f68 | e73f06b89813687d41fd8a1768b83c4217c4e93094e5dc8e0f9b21cdea249ab8 |
| consensus | Consensus | 5e0bb2d31ac83b557e48b53b04817fc91a7a71771b09bcf6d7fea79a233723c3 | ed109cc4c927d67010e14c12f385cfb0cf2e5a9fbfa98fd2e9744961a802458c |
| consensus_epr | consensus_epr | 4daa0c7740ae6596a38fba52a66bbd1c14093af9dac9bf90776197921a2c2d90 | 6a988400c3203c5fc0f54805085c06315eb49805e037107b2e006d8a72b88980 |
| consensus_forall | consensus_forall | 52e9e1d7cfc9e7d4470bca9703dc24be3c4741a3b1950b231e8881efaf264519 | b43c7ff25600f71a90ab81366b81649d71a3b83840b28305a66e51e99489a464 |
| consensus_wo_decide | consensus_wo_decide | 0bc5b0262bb27dd2dfe725dedc11cab9e666b0b60cd5d4184f8994b5c2e8cad5 | 45258134985a3c869a1377690d9a3b46e9548df0b1f00789f3a60b34b0622b8b |
| firewall | firewall | cfbd024e6d315b46555222615d6c790091c19a014af9c662fb835f1a6b317fd8 | 9243941707d25101810db08b0f525bf63feb7f8eace52b8ba9f932800930c8b4 |
| learning_switch | learning_switch | a05b9c942b5dddc17d1320e3c5f8c4d75be996d1da4a3f862e71207d85d3192d | 5d737e9d2cfbc0a51c705bc31ee6ec9fbee3a0719aeee4eb31a29fb799c0970f |
| learning_switch_i4 | learning_switch_i4 | fac1fd0be2f2ed7c42cb24ead57f2c00bfb67bee40f164808a1e71bafa9affca | 04962d346c2c7068d1262c0780f8bd0f10a52d54a405dfcafb6632775c2423b0 |
| lock_server | lockserver | 0bd06d96896a4d46aae2cd3e23c05cd47de0435d3b2889f943cdb1e8c9a299a4 | 7ef88881a1ab804c73cbba3bc6cde7dd8a1a3393dd01701eed93a3549acf8945 |
| lockserv | lockserv | 87ea36326c8432bdb4a8b669b4294b5b717bd500f44f7faf987452795ca17a77 | ea525f223f7f6ea1297600cb748d9823597e709e38700539cd2424b1be2d002e |
| lockserv_automaton | lockserv_automaton | 0ba2621c7a81aa1b4bccc09592bf7cd84ee16b8ab09d9c4a870ff2aea470e3f7 | ea525f223f7f6ea1297600cb748d9823597e709e38700539cd2424b1be2d002e |
| majorityset_leader_election | majorityset_leader_election | 2561cec2c9b826408ca4c0a3567c120426f23abcfccd8e1aa257339130d8766b | b3edf20417ca133ec4930092c751c8b9452a4aac983cc308a86d40ea989374f0 |
| mldr | MongoLoglessDynamicRaft | c09dd60a54f2dc66c2f58087bbeb49b7686be0425f8af3eb1f10a9299ae73e8e | 7ecbe9db55778faa4e8ac5a0cdc7f1525454313a364bc741a83bbf85739467fe |
| naive_consensus | naive_consensus | 556c009ac6bdf71e9ed5e41dcf444d47a9a72e578ac8914b03364237cffcd1a2 | 7dcedb4e4f4a928e5b2927f5671aaf6cb81ce8392981b7420ee8e61b766036b9 |
| paxos_epr | PaxosEprPyv | 66e83cd5d38a084fcb76ca7bac3d2ea9c31363e1c8995a5515203fb45e8919eb | 8e6528c8b2770c2c47563eb9a9a47cbe614f0f48dd2134d1ed16e6d1c2254ed3 |
| quorum_leader_election | quorum_leader_election | b9ea61f40a2e610cf2b3c0b5171c75a00330fb17390c3192ca8c37f20efa5acb | 5ddaff9fdda8e1b7bac47c754a85ed3e0854fca7714e88c864765deb78cdfdf9 |
| sharded_kv | sharded_kv | 01118a65b28f1e28171e4727999aa8cdd44e542b6e556b7c2a4e05a55d0b48da | 1316d3a413efac71ecf5f65853f17b89415437f1c58c70f7560d3c159efde185 |
| sharded_kv_no_lost_keys | sharded_kv_no_lost_keys | be7475450f677e5926f81c9d3644636630447e66c26ea77f66b449fbfc1817fa | 1316d3a413efac71ecf5f65853f17b89415437f1c58c70f7560d3c159efde185 |
| simple | Simple | 8bf6d786fc4cd19a1aef7de7367014332a2e453dc91f9b7df8e63377be35568f | 2c0f9defabe89b3501a580598f71e6d85410ad08e91585e53b2d1de6ead651c5 |
| simple_decentralized_lock | simple_decentralized_lock | 13ae038722fe4aa05b40669c7aaffa11247f12ef5a29db0f2503af7f2c0cab25 | 9243941707d25101810db08b0f525bf63feb7f8eace52b8ba9f932800930c8b4 |
| simple_election | simple_election | 85ea848525a9193aa6ace230a2b40a55049b2af8dcb0fd5e257229d08a3f0c15 | 34f455d90ac0d73d3d9dbb405e370a8e9e31235a663740ab2b0c53ae2fe58bb7 |
| simple_regular | SimpleRegular | 5b1ac9d0f48f2b51bfc9b39bab2c0a0d8305f0ddc1561f1d265a80a296e8dfd2 | a60199e863cb5ca914d27279539d6e4644e9e698c5cc2f27257a3c1ea39a2223 |
| tcommit | TCommit | da3d6a2b8c868ae278d765c6fa71b6c3d88e38dc8744bb0c10b4659fba3f1239 | 74828340431f11d2ad0865d9a79728e88eb9239dd451cde818bdd042df10a84e |
| toy_consensus | toy_consensus | b9cbdff843ed1bcd6a6925a6b0e8562756041e777e674d24b2a611067c4c35af | e8875ca7f98305e2eb107dec36148e1d9618a8d5a935fedace76e25d8b750681 |
| toy_consensus_epr | toy_consensus_epr | c40b96281fc1c188df63354f53df981e8a392daeba91cbf06481fbe4158c17e1 | f6992145549d26c921392d2e5f9af69ee8e0b915a30e78e60a2bc040fcc591d7 |
| toy_consensus_forall | toy_consensus_forall | 2127111f3b127ef5027922299e0cc2afa54f8d481a13573b443d126832f92bdf | e8875ca7f98305e2eb107dec36148e1d9618a8d5a935fedace76e25d8b750681 |
| two_phase_commit | two_phase_commit | a30bc5ce9c5bb357fc851762d5ce5b2e53b6a73616505819658283b2c97f37f8 | b3edf20417ca133ec4930092c751c8b9452a4aac983cc308a86d40ea989374f0 |
| twophase | TwoPhase | 0f0ce7adf47bb427976a5ccc48b35887e10240e3a72239d50eadc26ce91010da | 74828340431f11d2ad0865d9a79728e88eb9239dd451cde818bdd042df10a84e |
