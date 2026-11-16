# Retained certificate radix triage

No proof search is used. This inventory distinguishes bound erasure from actual
radix-to-tuple translation; it is not an acceptance result.

| Protocol | `.mul 64` | `.mul 4096` | Next route |
|---|---:|---:|---|
| client_server_db_ae | absent | absent | Bound erasure/pruning; keys already `.tup`/`.cellT` |
| sharded_kv | present | present | Actual tuple re-keying |
| sharded_kv_no_lost_keys | present | present | Actual tuple re-keying |
| simple_decentralized_lock | present | absent | Actual tuple re-keying; retain SUM-cover bridge |
| firewall | present | absent | Actual tuple re-keying; two usual families |
| paxos_epr | present | present | Actual tuple re-keying; preserve counted certificate data |
| MLDR | present (14,365 occurrences) | absent | Actual tuple re-keying; global + 34 row parts |

The first archive inspection (batch `20261115-224636-c41vad`) scanned the
standard Data library plus Global/Row wrappers and returned no occurrences.
**That is not a sufficient MLDR classification.** The actual payload is
`Shared.lean`, SHA-256
`e138bdbad70f86cdec2252a62582b1dcf335b3cc86bf2704cdf505cb1d12d596`, inside
archive `23f8a704f3b1f9e9cf3ede0ac9e8a69777187b75521e06dbadd6b68eff4825af`.
The immediate replay batch `20261115-225113-zqkb4u` hash-verified and scanned
that actual payload. It recorded `NEEDS_REKEYING`, 14,365 `.mul 64` occurrences,
zero `.mul 4096`, and zero `.tup`/`.cellT`, with zero Lean executions. This
completes the split: one direct bound-erasure candidate and six packed families.

Every replay receipt carries explicit PENDING source-bridge obligations:
parameter/admission correspondence, typed source-map correspondence, public
goal correspondence, and ghost/witness projection where present. A checked
internal family is not production/source acceptance.
