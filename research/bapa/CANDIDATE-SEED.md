# Retained-family candidate seeds

The retained 0.49 family is **candidate data**, not a source of trusted facts. `candidate-seed-manifest.ts` verifies the SHA-256 of `CAPTURE.json`, its graph manifest and each graph shard, and requires a unique retained usual leaf. The sharded fixture manifest binds capsule `2d81751966afd9edebcaf04f5acdeadbe3ec75cccee60e0e0df633d08fdbda73`, protocol `sharded_kv`, explicit map layouts and symbolic domain parameters. Paths are input locations, not custody claims. The caller must compare the manifest protocol against the selected protocol and include the manifest hash and audit in its invocation custody.

`restateSeeds` supports only scalar/bound variables and the explicitly mapped fixed-radix map layouts. Every quantified variable needs a uniquely inferred sort and a source fixed-domain guard. Packed index positions must match the specified radix, coefficient and arity; they become native tuple keys. Only matching bound guards become symbolic parameter comparisons. Unmapped maps, ambiguous values, metadata, existential/nested quantified AST and missing or conflicting sorts are dropped with a reason. This is intentionally incomplete: in particular numeric value binders not appearing in a mapped key may remain unclassified. A restated formula is merely a proposal for the target, not a claim of semantic equivalence between protocols. All non-guard occurrences of the radix literal are refused, not globally replaced.

`proveCandidateSeeds` takes a normalized target `Machine`, complete public `Law[]`, and candidate `Law[]`. It checks both obligations of each candidate against the current family, removes only definite `sat` candidates, and restarts after every removal. Unknown is inconclusive. A successful result requires `proveSetFast` to construct and kernel-check the complete public-plus-kept family; its exact `closure` object carries ordinary `retainFamily` provenance. An inconclusive result must fall back to ordinary inference without retained assumptions. No candidate becomes a machine fact or a given. Candidate and public existential/helper metadata, witness projection and step-law integration are unsupported here. Counted leaves are refused; witness-route captures are usable only where their unique usual leaf has individually mappable plain laws. These limitations mean the six requested unknown families are not all supported or proven.

For capture, the public wrapper must link its returned verdict with `retainFrom(verdict,[closure],{kind:'inference',original:machine,laws:publicLaws})` and publish the exact original machine/public-law references. The usual leaf carries the complete checked family and proof. A changed machine is deliberately an unqualified source projection.

Historical normal-capsule inventory (hash of `CAPTURE.json`):

| Protocol | Route | SHA-256 | Status |
|---|---|---|---|
| sharded_kv | inferred | `2d81751966afd9edebcaf04f5acdeadbe3ec75cccee60e0e0df633d08fdbda73` | explicit fixture mapping |
| sharded_kv_no_lost_keys | witness | `e41e37724663b689ed716c639694ff002c0be92e99ace6267f4ef8ad3cf8fe4f` | target bindings not yet audited; existential public law unsupported |
| simple_decentralized_lock | inferred | `e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958` | target bindings not yet audited |
| lock_server | inferred | `eb4f9e3d76280d713501e26553064d23bec73c249912710b1fd1728cf1a1a9bf` | target bindings not yet audited |
| toy_consensus_forall | counted-family | `33f1a9949fb71fec0b5c1017c0607b25517a4222de10f0634bddc9bd4d8ae84b` | counted leaf unsupported |
| client_server_db_ae | witness | `e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0` | target bindings not yet audited; existential public law unsupported |

The small fixture `candidate-seed-symbolic.ts` uses only a symbolic Node/Key put model (no size cap), and picks its support ASTs mechanically from the sharded capsule. It is not a full protocol proof; each lane's authorized one-time protocol rerun is a separate operation. Its output records the full drop audit, unseeded result and complete-family result. Run via `candidate-seed.jobs.json` under the approved pinned strict-once remote policy, with the retained capsule supplied at `seed-capture-sharded-kv`. No Lean comment parsing is used.

## Verified fixture gate

Strict-once pinned-Bun batch `20261115-212825-x5ogda` passed TypeScript,
**14 tests / 61 assertions**, the symbolic fixture and commitlint. The 23-law
retained family produced 8 mappable candidates and 15 explicit drops in this
small target. The fixture's public value-1 same-key table exclusion was not
inductive alone (`@step`, `sat`); retained entries 5, 10 and 19 then gave a
complete kernel-checked family. They express table/other-owner exclusion,
owner uniqueness and table-implies-owner. This is not a reachable-bug trace,
a proof of the full sharded protocol, or an all-six-family result.

Tests also cover the actual public `ProveOptions.candidateSeeds` path, exact
original-law custody, retained full-family `checkLaws`, and false candidate /
false public-law controls. Full audit and logs are under
`runs/candidate-seed-fixtures-final/candidate-seed-fixtures.files/`.
The first gate stopped at an EPR-only decision limitation; adding the existing
ordinary prover fallback fixed that without treating unknown as proof.
