# Lean exporter repair: retained IC3Syn certificates

Branch: `claude/lean-export-fix`, based on `0281a7e0` (`claude/verify-all`). Implementation follow-up to [paxos-lean.md](paxos-lean.md); not merged. Original captured packet bytes, laws, proof trees and count instances are inputs, not patched artifacts. Generated Lean necessarily changes; the old emitted file remains rejected by the unchanged checker.

## Repairs

**Singleton structure.** `lean-kernel/lean-terms.ts` renders `or [c]` as `or c false`, and `and [c]` as `and c true`. The shared-term printer uses the same helper. Empty and multi-element connectives retain their previous encoding. This preserves truth and the path-sensitive contradiction row that TypeScript `facts` derives from a singleton connective. No row-admission, arithmetic, or checker rule changes, and no retained leaf replacements. Human-readable law corollaries explicitly simplify the neutral children (`or_false` / `and_true`), rather than expecting those propositional equivalences to be definitional.

Lean-first evidence: [export-shape.lean](export-shape.lean) proves the generic truth equivalences, acceptance of the original input-only singleton tree, rejection after connective erasure, and the dual conjunction case. The printer was changed after the clean `export-shape-verified` boat check. [Renderer tests](../../lean-kernel/export-shape.test.ts) check actual output and source-goal/tree immutability.

**Generic binder alpha conversion.** [QAlpha.lean](../../lean-kernel/QAlpha.lean) is an additive semantic proof module. `Rename` selects a flag, an old bound name, and a fresh name. `validAll` checks sequentially that each selected old name is bound and its replacement occurs neither in that flag's binder list nor its body. `renameAll` changes that flag's binder list and body only.

The proofs cover arbitrary bodies/environments/maps, multi-key flags and lists of renamings: `quantified`, `decideQ_rename`, `renameAll_equiv`, `Equiv.view`, `Equiv.next`, `Equiv.sreach`, and `Equiv.creach`. Generic `QAlpha.cmachine_sound` and `QAlpha.smachine_sound` transport the existing checker's laws back to the original machine. No existing Lean checker file or rule changes.

The counted exporter uses an immutable [renaming plan](../../lean-kernel/qalpha.ts), avoiding all source/certificate names. Output keeps `verified_machine` as the original literal, defines `verified_checkedMachine := QAlpha.renameAll verified_machine verified_renames`, checks the original proof there, and derives `verified_laws` over **`CReach verified_machine`** via the generic wrapper. `validAll` is kernel-reduced. No Paxos-specific names, indices, paths, replacement leaves, or hand-written per-certificate semantic bridge occur in the exporter.

The module is included in the generated packaged library and counted-export caller imports. The only protocol-directory edit is the standalone counted-export CLI's import header, not its model/search. Other export routes share the Boolean fix; none of the other 27 accepted packets needs the binder admission repair.

## Verification

Everything substantive runs on boat through `supercomputer`. No external solver, `native_decide`, new axiom, `sorry`, or weakened checker. The generic module's printed dependencies are only Lean's existing `propext`, `Classical.choice`, and `Quot.sound`. Tests cover multi-key/multi-flag renaming, duplicate binders, free-name capture, bound-name reuse, and a missing old binder.

Initial Paxos pilot (before the surface-corollary simplification follow-up): original packet SHA-256 `dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386`, retained proof SHA-256 `682863e5ca89db9cbf3cb6d0ba4aff0c7801f3d8e8afb5606a283a0f3d3194fd`. The original `YYYYN` and `N` leaves pass without the previous diagnostic replacements. New Lean SHA-256: `c1ae72887a924244db6217888ba6fb2426ffe35293741ea8610585eae3e0fd03`. Generated fresh/colliding-machine controls and the original singleton tree also pass.

**28 / 28 accepted packets pass clean Lean checks.** Final all-packet batch: `20261109-102926-h7r6d1`, source tree `b47a35e292b4`, output `runs/verify-all/export-fix-all-v2/`. Every job is boat, exit 0. The TypeScript kernel is unchanged.

| Protocol | Export / Lean | Job seconds |
|---|---|---:|
| `client_server_ae` | pass / pass | 12.59 |
| `client_server_db_ae` | pass / pass | 15.14 |
| `consensus` | pass / pass | 5.36 |
| `consensus_epr` | pass / pass | 29.39 |
| `consensus_forall` | pass / pass | 55.18 |
| `consensus_wo_decide` | pass / pass | 45.68 |
| `firewall` | pass / pass | 11.42 |
| `learning_switch` | pass / pass | 103.48 |
| `learning_switch_i4` | pass / pass | 120.92 |
| `lock_server` | pass / pass | 9.96 |
| `lockserv` | pass / pass | 20.32 |
| `lockserv_automaton` | pass / pass | 12.45 |
| `majorityset_leader_election` | pass / pass | 37.41 |
| `naive_consensus` | pass / pass | 11.62 |
| `paxos_epr` | pass / pass | 61.79 |
| `quorum_leader_election` | pass / pass | 28.31 |
| `sharded_kv` | pass / pass | 60.23 |
| `sharded_kv_no_lost_keys` | pass / pass | 13.4 |
| `simple` | pass / pass | 8.75 |
| `simple_decentralized_lock` | pass / pass | 21.66 |
| `simple_election` | pass / pass | 11.99 |
| `simple_regular` | pass / pass | 15.51 |
| `tcommit` | pass / pass | 5.87 |
| `toy_consensus` | pass / pass | 7.06 |
| `toy_consensus_epr` | pass / pass | 9.06 |
| `toy_consensus_forall` | pass / pass | 9.5 |
| `two_phase_commit` | pass / pass | 23.0 |
| `twophase` | pass / pass | 23.71 |

Other checks:

- Generic alpha proof: initial batch `20261109-101505-f0887g` passed (`qalpha-run-06/`). Removing only its extra EOF blank line was followed by a fresh compile and all universal/negative/axiom tests in the final batch below. Exact committed source SHA-256: `3c362e366b8aad32de802feac45e5ab86d0893cefb9b6e0fc9c2e85ef1bf3a4b`.
- Final validation: `runs/verify-all/export-fix-validation-v3/`, batch `20261109-102926-86u0og`: 17 tests, 13,080 assertions, no failures; full counted examples Lean-check; generated-library exactness; scoped TypeScript and deny-warnings lint, all pass.
- Surface/hash repair pilot: `runs/verify-all/export-fix-repair-v2/`, batch `20261109-102754-t376n7`, both jobs pass, including actual generated singleton law statements and unchanged-source controls.
- Final proof/provenance/source/commitlint batch: `20261109-103933-69h5fh`, `runs/verify-all/export-fix-final-v2/`, all four jobs exit 0. All 28 independent re-exports are byte-identical to the Lean-checked artifacts; all 28 parsed capture objects and retained proof digests remain unchanged. Only Paxos needs the generic alpha bridge.
- Committed manifest: [lean-export-fix-receipts.json](lean-export-fix-receipts.json), SHA-256 `07f0082e36aaf92552f12c19ca0653d4c65c340d19b303de5f8f65fae895bf27`. It records every original packet/proof hash, checked Lean hash, compiler-log hash, and final exporter-source hash. Paxos proves all 25 original captured laws; its final Lean hash equals the successful pilot hash above.

Development failures are retained, not silently counted as passes: `export-fix-all/` exposed seven initial- versus later-Lean hash mismatches (the packet bytes were unchanged) and four plain-statement corollary regressions from retained neutral children. `export-fix-repair/` exposed incomplete surface simplification. The final repair normalizes evaluator/update terms as well as the neutral children; the clean `-v2` all-packet gate above includes every formerly failing case. The earlier `export-fix-validation-v2/` counted-example failure is superseded by clean `-v3`.

### Reproduce

```sh
supercomputer run --jobs research/verify-all/export-fix-all.jobs.json \
  --out runs/verify-all/export-fix-all-v2 --class gate --backend boat \
  --data runs/verify-all/capture-all:evidence
supercomputer run --jobs research/verify-all/export-fix-validation.jobs.json \
  --out runs/verify-all/export-fix-validation-v3 --class gate --backend boat
supercomputer run --jobs research/verify-all/export-fix-final.jobs.json \
  --out runs/verify-all/export-fix-final-v2 --class gate --backend boat \
  --data runs/verify-all/export-fix-all-v2:evidence/export-fix-all \
  --data runs/verify-all/capture-all:evidence/capture-all \
  --data runs/verify-all/export-fix-messages:evidence/messages
```

[export-fix-packet.ts](export-fix-packet.ts) checks original packet hashes against the prior audit, records both the archive’s initial Lean hash and the audit’s possibly later re-export hash, invokes the regular retained-packet exporter, verifies disk bytes and parsed capture/proof objects remain identical, and requires clean Lean success. The research-only alpha-equivalence comparator uses structured binder markers, so a free name resembling an internal marker cannot masquerade as a bound variable. Each job archives generated Lean, result JSON and complete compiler log between `EXPORT_FIX_ARCHIVE_BEGIN` / `EXPORT_FIX_ARCHIVE_END`. [Receipt validation](export-fix-receipts.ts) independently hashes those artifacts, checks all 28 expected IDs/exits, and re-exports each original packet with the final capture/mutation guards. It requires exact byte equality with the already Lean-checked artifact, rather than trusting a propagated input hash. The production proof search is not rerun.

The full-worktree `bun run check` remains blocked by the preserved uncommitted historical `paxos-law12-probe-v1.ts:42` error documented previously. Source validation uses the prior explicit helper: only that unused file is excluded if present; no root configuration changes and no additional compiler exclusion on a clean checkout.

## Scope

This repairs proof export for the qualified captured models; it does not remove the modelling qualifications in `runs/VERIFY-ALL.md` or prove equivalence with unrestricted source protocols. No `kernel/` changes, existing Lean checker-rule changes, history rewrite, worktree recreation, cleanup of untracked/ignored data, push, or merge.
