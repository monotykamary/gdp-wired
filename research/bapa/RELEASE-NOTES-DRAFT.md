# BAPA release notes — draft

> Not a release announcement. The final unified 27-model check is still pending. The unrestricted-coverage list below is the intended release claim and must not be published unless that check passes with the required theorems and axioms unchanged.

## From retained proofs to source-level guarantees

This release adds one command for lifting an existing proof capsule to its source model:

```sh
gdp-wired lift ./capsule ./source.json --out ./proof
```

The command generates a self-contained Lean project and checks the original public safety laws. It chooses the required transformation from the supplied model and retained proof: bound erasure, typed substitution, key translation, source inclusion, finite-step simulation, or witness and binder renaming. No new invariant search is required, and no handwritten proof file for the individual protocol is loaded by the command.

A successful check produces a `SOURCE_CHECKED` receipt bound to the capsule, source model, and generated files. `--emit-only` writes proof obligations instead; it does **not** report a checked source theorem. Incomplete proof families, unsupported transformations, changed inputs, missing public laws, and unacceptable axioms are rejected.

## What “every size” means

The unrestricted results are the safety theorems of the supplied, encoded source models, under their declared assumptions. Their symbolic size parameters are quantified in Lean: the result is not an extrapolation from tests through size 64. This does not automatically establish equivalence to a separate implementation or specification, and it does not silently remove any bound still present in the source model. Removing a retained bound requires a checked source correspondence.

Subject to the final release check, the unrestricted source-model coverage is:

| Group | Accepted models |
|---|---|
| Locks and elections | `lock_server`, `lockserv`, `lockserv_automaton`, `simple_election`, `quorum_leader_election`, `majorityset_leader_election`, `simple_decentralized_lock` |
| Consensus | `consensus`, `consensus_epr`, `naive_consensus`, `toy_consensus`, `toy_consensus_epr`, `consensus_forall`, `consensus_wo_decide`, `toy_consensus_forall` |
| Transactions and switches | `tcommit`, `twophase`, `two_phase_commit`, `learning_switch`, `learning_switch_i4` |
| Client and witness models | `simple`, `simple_regular`, `firewall`, `client_server_ae`, `client_server_db_ae` |
| Sharded models | `sharded_kv`, `sharded_kv_no_lost_keys` |

These are **27 source models**, not a claim that all 29 benchmark protocols have unrestricted proofs.

## Paxos and MLDR remain bounded

Paxos (`paxos_epr`) and MLDR are **proven up to size 64**. They are not included in the unrestricted 27-model claim. No all-size claim is made for either unless a separate unrestricted result is completed and checked before release.

## Proof and compatibility guarantees

- The original public safety statements are preserved, including their quantifiers and witnesses.
- The complete retained family is checked, including supporting obligations; a partial family is not accepted as a public proof.
- Existing theorem names can be preserved through validated, naming-only aliases. Names cannot select a transformation, alter a law, or provide proof code.
- The release regression checks the required theorem names and axiom sets, not just command success.
- The proof transformation machinery is part of the shipped Lean library. Research examples are not runtime dependencies.

The release will be held if any of the 27 accepted models fails the unified check or requires a changed theorem or axiom contract.
