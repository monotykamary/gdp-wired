# Retained-family candidate seeds

The retained 0.49 family is **candidate data**, not a source of trusted facts. `candidate-seed-manifest.ts` verifies the SHA-256 of `CAPTURE.json`, its graph manifest and each graph shard, and requires validated retained usual leaves or a complete retained counted-family leaf. Multiple usual leaves are restated independently against their own machines; their proposals receive globally unique names and audited source-family indices. The sharded fixture manifest binds capsule `2d81751966afd9edebcaf04f5acdeadbe3ec75cccee60e0e0df633d08fdbda73`, protocol `sharded_kv`, explicit map layouts and symbolic domain parameters. Paths are input locations, not custody claims. The caller must compare the manifest protocol against the selected protocol and include the manifest hash and audit in its invocation custody.

`restateSeeds` supports scalar/bound variables and explicitly mapped fixed-radix map layouts. A declared tuple relation must match every sort position exactly. Any native map, including a numeric `Node × Key → Nat` map, may lack relation metadata: an explicit per-coordinate manifest binding plus declared symbolic size parameters establishes the proposed layout. Missing bindings, conflicting declared sorts and missing parameters are refused. Every non-vacuous quantified variable needs a uniquely classified sort. Truly unused binders are removed, and universals over raw cell addresses can expand to tuple coordinates only when all their uses have one compatible explicit map layout. Existing fixed-domain guards become symbolic parameter comparisons; a binder with no such guard stays unrestricted and is listed in `unboundedBinders`. No new domain assumption is inserted. Packed index positions must match the specified radix, coefficient and arity; they become native tuple keys. Unmapped maps, ambiguous values, metadata, existential/nested quantified AST and missing or conflicting sorts are dropped with a reason. This is intentionally incomplete: in particular numeric value binders not appearing in a mapped key require an explicit `bindings.variables` sort assignment, otherwise they remain unclassified. A restated formula is merely a proposal for the target, not a claim of semantic equivalence between protocols. All non-guard occurrences of the radix literal are refused, not globally replaced.

`proveCandidateSeeds` takes a normalized target `Machine`, complete public `Law[]`, and candidate `Law[]`. It checks both obligations of each candidate against the current family, removes only definite `sat` candidates, and restarts after every removal. Unknown is inconclusive. A successful result requires `proveSetFast` to construct and kernel-check the complete public-plus-kept family; its exact `closure` object carries ordinary `retainFamily` provenance. An inconclusive result must fall back to ordinary inference without retained assumptions. No candidate becomes a machine fact or a given. Candidate and public existential/helper metadata, witness projection and step-law integration remain unsupported in this ordinary entry point. A count-bearing target instead uses `proveCountedCandidateSeeds`: native counted-family admission, followed by a complete `checkCountedLaws` check. Only fresh, translated count declarations are added to the private producer; source declarations cannot be overridden. Counted drops are not mislabeled as SAT, because admission can discard unknown candidates. Packed `lo`/`base` count definitions remain explicit drops. None of these adapters proves the six full protocols merely by loading their candidates.

For capture, the public wrapper must link its returned verdict with `retainFrom(verdict,[closure],{kind:'inference',original:machine,laws:publicLaws})` and publish the exact original machine/public-law references. The usual leaf carries the complete checked family and proof. The public source remains unchanged. Sums and fresh count declarations belong to the private producer; a changed machine still requires the appropriate independent source bridge and is not automatically a qualified source projection.

Historical normal-capsule inventory (hash of `CAPTURE.json`):

| Protocol | Route | SHA-256 | Status |
|---|---|---|---|
| sharded_kv | inferred | `2d81751966afd9edebcaf04f5acdeadbe3ec75cccee60e0e0df633d08fdbda73` | 23 candidates / 0 drops in six-manifest audit |
| sharded_kv_no_lost_keys | witness | `e41e37724663b689ed716c639694ff002c0be92e99ace6267f4ef8ad3cf8fe4f` | 10 candidates / 0 drops; public existential injection still separate |
| simple_decentralized_lock | inferred | `e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958` | 4 candidates / 0 drops, including both native SUMs |
| lock_server | inferred | `eb4f9e3d76280d713501e26553064d23bec73c249912710b1fd1728cf1a1a9bf` | 4 candidates / 0 drops |
| toy_consensus_forall | counted-family | `33f1a9949fb71fec0b5c1017c0607b25517a4222de10f0634bddc9bd4d8ae84b` | fresh unary count definitions and counted admission supported |
| client_server_db_ae | witness | `e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0` | target bindings not yet audited; existential public law unsupported |
| firewall | witness | `0d65e7fc04cacd716180a8927e4050249fe3323ff23b4331f577ed3be38432ab` | 12 candidates / 0 drops across two leaves; public existential injection still separate |

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
The unary-map extension passed `20261115-213713-i8dmwg`: types,
16 tests / 74 assertions and commitlint. It covers `HasLock` and `Semaphore`
without relation metadata, while rejecting missing maps/size parameters,
conflicting declared sorts and missing tuple bindings (the later adapter batch permits explicitly bound numeric tuples).

The first gate stopped at an EPR-only decision limitation; adding the existing
ordinary prover fallback fixed that without treating unknown as proof.

## SUMs, native kinds, and relation-field proposals

Whole-cell retained `Machine.sums` may be mapped only after validating the source definition, zero-initialized source/target state maps, explicit layouts, and the actual native `MapRef.sum()` declaration. `sum$HasLock` and `sum$Message` then denote the native sums of all encoded cells, including a tuple relation's cells. The prover materializes these conservative sums through `withSumsOf` inside the existing public call. Unknown or weighted sum definitions are not free variables and remain drops.

A captured `every <map> cell is a value of its kind` law can be regenerated from the target rule's own `kindLaws()`. It remains a candidate, with `regeneratedKind` in its audit; it is not copied into trusted assumptions. When a target has no separate kind entry, a raw packed-cell kind predicate is instead expanded over explicit tuple coordinates and remains an ordinary proposal. Both paths are audited.

Historical `Owner$n`, `TransferMsg$n21`, and `TransferMsg$v1` are last-written ghost witnesses, **not** projections of an arbitrary current relation row. `bindings.fields` may request a weaker row-based proposal: select explicit key/value coordinates, quantify the remaining coordinates, and guard the proposed formula by membership in those rows. Fields of one relation and key share one row, so message coordinates cannot come from unrelated tuples. The audit explicitly records `row-guarded-proposal` and `absence: not-covered`. These proposals do not establish a witness on empty rows, preserve an arbitrary ghost default, or discharge the original public existential. Every proposal still passes native admission; a no-search audit is not proof.

The six-manifest acceptance recipe is `seed-adapter.jobs.json` with `seed-audit-six.json`. It uses the lane-owned symbolic models supplied as data, sealed normal capsules at `seed-audit-captures/<protocol>`, and a seeding-only core snapshot at `seed-test-inputs/`. `candidate-seed-audit.ts` calls no prover, checks that the source machine is unchanged, and writes a full per-law drop audit. The full protocol reruns remain separate, authorized one-time lane operations.
