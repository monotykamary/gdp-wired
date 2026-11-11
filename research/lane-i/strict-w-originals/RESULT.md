# Strict-W originals — required non-MLDR gates PASS

Source commit: `d00ad74f526337c0c2f46e6548b83bc1b6688ced`.
Exact tree: `8e367451ea30ed075d2f95e92660fb02e45ba459`.
Parent: `f81c2c50810052de0a33e50f18900ab12a6a1cc2`.

- Active28: all28 at/below15M; all16 former negatives closed; other12 exact.
- Strict28/off: 28 exact pairs;27 checked,1 unchanged unknown. Independently replayed from the completed files;121 hashes verified.
- Native/static:25 full tests/311 assertions;9 off tests/60 assertions; TypeScript and lint PASS. Eight log hashes verified.
- Both commitlint configurations PASS. All181 protected blobs unchanged.
- No raw bucket grew; no price, law, root or tier change. No Lean/whole-line promotion.

| Prior cap-negative case | Baseline units | Candidate units |
|---|---:|---:|
| lock_server | 15000120.6860 | 14999999.6860 |
| lockserv_automaton | 15000012.0997 | 14999999.0997 |
| sharded_kv | 15000018.2817 | 14999999.2817 |
| sharded_kv_no_lost_keys | 15000076.4294 | 14999999.4294 |
| lockserv | 15000178.2075 | 14999999.2075 |
| simple_decentralized_lock | 15000075.5540 | 14999999.5540 |
| twophase | 15000059.8476 | 14999999.8476 |
| two_phase_commit | 15000200.9145 | 14999999.9145 |
| consensus_forall | 15000047.4800 | 14999999.4800 |
| client_server_ae | 15000015.1800 | 14999999.1800 |
| client_server_db_ae | 15000194.8333 | 14999999.8333 |
| firewall | 15000222.9840 | 14999999.9840 |
| learning_switch | 15000129.5555 | 14999999.5555 |
| learning_switch_i4 | 15000058.0140 | 14999999.0140 |
| consensus_epr | 15000062.3800 | 14999999.3800 |
| paxos_epr | 15001010.0000 | 15000000.0000 |

Table values are rounded for display. The unrounded JSON values all satisfy `searchUnits <= 15000000`, with no waiver or tolerance. Maximum: paxos_epr exactly15M.

The extra29th legacy MLDR control also completed: all29 flags-off pairs are exact (27checked/2unknown), with all125 final census file hashes verified. MLDR remains UNKNOWN; this is compatibility only, not a full-mode MLDR cap or closure result.

V1 native test import-cycle failure is retained separately. Correcting that dependency layout did not alter the frozen f81c source used by A’s 1G diagnostic.
