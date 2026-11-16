# Source-bridge obligations for retained-certificate transport

All entries below are **PENDING**. A kernel/Lean acceptance of a translated
internal machine is not a proof that it is the public source protocol. No
production acceptance or all-sizes source theorem is inferred from these checks.

For every capsule, the bridge must establish:

1. The parameter and request admission conditions of the unbounded source
   correspond to the translated machine; no hidden size<=64 or value<64 premise
   remains in the source theorem.
2. Typed source relations/maps correspond to the internal maps. For re-keyed
   maps, the correspondence uses unbounded tuple components and the kernel's
   right-nested pairing, not radix64 packing. Whole-address binders, flags,
   instances and any ghost maps must share that correspondence.
3. Source initial states and every source transition map to internal initial
   states/transitions, with unchanged operation selection and scalar semantics.
4. The named public safety goal follows from the checked internal family,
   including any required existential/ghost witness projection.

| Capsule | Identity | Additional obligations |
|---|---|---|
| toy_consensus_forall | checked transport commit `d989424d52d861b5f74804d1d9d887c303186102` | P2 owns source bridge; preserve symbolic below:size counts. |
| client_server_db_ae | `e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0` | Existing tuple maps and row-guard/ghost witnesses; project the received-response goal. Two bound-erasure step refusals currently prevent a family lift. |
| sharded_kv | `2d81751966afd9edebcaf04f5acdeadbe3ec75cccee60e0e0df633d08fdbda73` | Table(node,key), Owner(key,node), TransferMsg(node,key,value); expanded raw-address kind binders must cover every tuple. |
| sharded_kv_no_lost_keys | `e41e37724663b689ed716c639694ff002c0be92e99ace6267f4ef8ad3cf8fe4f` | Preserve no-lost-key goal, transfer-message values and quantified ownership flags under tuple re-keying. |
| simple_decentralized_lock | `e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958` | Preserve the SUM-cover relation as well as the plain-machine family; a plain-only check does not discharge this. |
| firewall | `0d65e7fc04cacd716180a8927e4050249fe3323ff23b4331f577ed3be38432ab` | Bridge both retained usual families, not one selected family. |
| paxos_epr | `89ff11ec663114a06032c9df7ef1e1449f68bf5f7ec4cebf60344779dd00062d` | Preserve all count declarations, witness/instance coefficients and quorum semantics; 50 obligation classifications alone are not a transport. |
| MLDR | archive `23f8a704f3b1f9e9cf3ede0ac9e8a69777187b75521e06dbadd6b68eff4825af`; Shared.lean `e138bdbad70f86cdec2252a62582b1dcf335b3cc86bf2704cdf505cb1d12d596` | Preserve counted/auxiliary frame, monotonicity and linear-cut semantics, and join the global check with all 34 row parts. No rerun of the stopped symbolic search. |
