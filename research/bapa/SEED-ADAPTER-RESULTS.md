# Seed adapter acceptance

Verified strict-once batch: **`20261115-220831-jye1lt`** (pinned Bun 1.4.3).
Typecheck, **31 tests / 173 assertions**, retained-count symbolic fixture, and
commitlint passed. The tests use the seeding-only `core/dsl.ts` snapshot and the
committed baseline `core/proof-output.ts`, not the pending nested-capture fix.
Hashes and source-model hashes are in `SEED-ADAPTER-RESULTS.json`.

## Restatement only: all six manifests

| Protocol | Candidates | Drops |
|---|---:|---:|
| lock_server | 4 | 0 |
| simple_decentralized_lock | 4 | 0 |
| toy_consensus_forall | 8 | 0 |
| sharded_kv | 23 | 0 |
| sharded_kv_no_lost_keys | 10 | 0 |
| firewall | 12 | 0 |

**61 proposals, zero layout/unmapped drops.** This acceptance pass called no
prover, made **zero public calls**, and verified unchanged native work counters
and unchanged supplied source machines. It is not a proof of these protocols.
The firewall pool contains two retained usual leaves; each is restated against
its own producer and has separate source-family/index custody.

Covered cases include numeric tuple maps, unary and tuple SUMs, fresh counted
definitions and scalar count indices, target-native/expanded kind laws, raw-cell
universals, explicit value-sort binders, and row-based relation-field proposals.
The sharded value binders `key$5`/`key$6` and firewall binder `key$3` are explicit
manifest assignments with radix 64, not guessed sorts or new assumptions.

## Native proof controls

- Ordinary, SUM, and counted public-wrapper tests retain complete kernel-checked
  families while preserving the public source.
- False candidates are removed; false public goals cannot be established by them.
- Fresh count definitions cannot override source declarations.
- A multi-leaf fixture deliberately seals a false candidate; native admission
  still rejects it. Capture metadata is not proof authority.
- The exact retained toy count formula and definition are checked as a protected
  goal in a separate, tiny symbolic fixture. This is not a toy-protocol rerun.

## Limits and handoff

`Owner$n`, `TransferMsg$n21`, `TransferMsg$v1`, and `AllowedIn$w` denote historical
last-written ghost witnesses. Their row-based proposals are explicitly guarded
by current relation membership and mark **absence/default cases not covered**.
They are not semantic aliases or proved witness transports.

The ordinary candidate entry still rejects public existential metadata. Thus
firewall/no_lost witness-aware **G-point injection remains separate work**;
zero restatement drops do not mean those public existential proofs now close.
No full protocol rerun was launched by this gate. Any authorized lane rerun must
still prove the original public goals under the same profile and export its
complete checked closure. No new all-size or source-qualified theorem is claimed.

## Artifacts / recipe

- Job contract: `research/bapa/seed-adapter.jobs.json`.
- Six manifests and registry: `research/bapa/seed-audit-*.json`.
- Full per-law audits: `runs/seed-adapter-05/seed-restatement-six.files/*.json`.
- Tests, typecheck, counted fixture and source-boundary hashes:
  `runs/seed-adapter-05/seed-adapter-tests.files/`.
- Supply sealed captures at `seed-audit-captures/<protocol>`, lane model snapshots
  at `seed-audit-models/{p1,p2,p4}.ts`, and the tested core snapshots plus commit
  message at `seed-test-inputs/`. Use `--backend boat --class interactive
  --strict-once --max-attempts 1` and retain the accepted batch ID.
