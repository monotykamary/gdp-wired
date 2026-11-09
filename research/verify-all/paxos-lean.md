# Paxos: resolving the TypeScript / Lean checker disagreement

Baseline: `e11165280a1bab4944a692a64ab1554e5f53c82e`, branch `claude/verify-all`. Follow-up to [the independent audit](../../runs/VERIFY-ALL.md), section 4, and [the initial diagnosis](paxos-diagnostic.md). Law indices below are zero-based. All substantive execution is on boat through `supercomputer`; no external solver or production-source change is involved.

## Answers

1. **Law 12 is a harmless bound-name collision in this certificate.** Renaming only flag `rowOk`'s binder and its three bound occurrences removes Lean's entry-admission failure. Lean proves equality of the flag semantics, step semantics and reachable-state sets before accepting the unchanged law-12 start/step certificates. The small-machine test reproduces the admission mismatch, but its concretely false laws are **not** accepted by TypeScript.
2. **Law 20 is a proof-export/completeness defect, not an unsound arithmetic step.** The first rejected leaf is `YYYYN`; the only other rejected leaf is `N`. Both input a constant contradiction legitimately derived by TypeScript from a singleton disjunction contradicted by the path. Export erases the singleton wrapper, so Lean no longer extracts that constant row directly. Lean correctly refuses the unexpanded row claim. Two explicit arithmetic derivations repair a *separately named diagnostic tree*; no checker or emitter is patched.
3. **None of the other 27 accepted families has either generated feature.** Their passing Lean checks therefore did not exercise a scan-prefix entry with further keys or a carry co-write step. Many contain other multi-key laws; none of those further keys collides with a quantified-flag binder in this census.

**Does the Paxos result stand?** The original exported certificate still fails the unchanged Lean checker. However, a separate Lean theorem now checks the alpha-renamed machine with just those two leaf derivations expanded and transports **all 25 original captured laws back to the original exported counted machine**. Thus these two disagreements do not refute the captured Paxos laws. This is not a claim that the original bytes passed, that the current exporter has been fixed, or that the bounded/qualified model is equivalent to unrestricted Paxos. The original audit's modelling qualifications remain.

## 1. Law 12: scope, alpha conversion, and counterexample search

### Exact collision and permitted change

Law 12 is `scan-prefix:cnt:rowOk:d93992f463f488aa`. Its further key is `k$21`, interned as Lean variable `29`. The binder of quantified flag `rowOk` (flag `72`) is also `29`.

`lean-kernel/Sets.lean:926–936` defines `skFresh` using syntactic occurrences in quantified-flag bodies and requires it for every further key in `key2Ok`. That test sees the bound occurrences as well as free occurrences. `kernel/kernel.ts:2090`'s `checkCountedLaws` checks reconstructed obligations and witness freshness, but does not perform this entry-side test. Missing this test is not, on its own, evidence of a false accepted law.

[paxos-law12-alpha.ts](paxos-law12-alpha.ts) first checks both original input hashes. In a separate packet it changes only:

```text
machine.step.flags.rowOk.key: k$21 -> paxosLaw12AlphaFresh
three occurrences bound by that flag: k$21 -> paxosLaw12AlphaFresh
```

It rejects an already-used fresh name or a nested quantifier rather than blindly renaming. No law, instance, count declaration, retained tree, or other flag is changed. In the separate Lean machine this is the single tuple change `(72, [29], body)` to `(72, [131], renamedBody)`. The external further key remains `29`. TypeScript still accepts the family and the same two law-12 certificates after this change.

### Kernel-checked semantic bridge

[paxos-law12-alpha-v4.lean](paxos-law12-alpha-v4.lean) is appended to the definitions **before** the rejected original `verified_check` theorem; it does not import that failed theorem. It proves:

- `paxos_row_alpha`: for arbitrary scalar environment `X` and maps `N`, the universally quantified old and renamed flag bodies are equivalent.
- `paxos_decideQ_alpha`: all quantified-flag values are equal.
- `paxos_view_alpha`, `paxos_next_alpha`: the machine's view and next-state functions are equal for arbitrary environments and requests.
- `paxos_reach_alpha`: `CReach` of the old and renamed machines is equivalent for arbitrary count declarations and states.
- Original entry 12 fails `cEntryOk`; the alpha entry passes; its witnesses and **unchanged** start and step certificates pass.
- All 25 alpha-machine entry conditions pass. Alpha conversion alone does **not** fix law 20: its step and the whole original family still reject.

These are semantic theorems, not finite testing of valuations. The changes remove an overly conservative admission restriction for this example without changing what the machine or law means. They do not prove that every freshness check could safely be removed.

### Small machine and concretely false laws

[paxos-law12-probe-v2.ts](paxos-law12-probe-v2.ts) constructs this small machine twice, once with the collision `q = g` and once with fresh binder `qFresh`:

```text
state:       B[k] = 0 initially, for every natural key k
request:     a carried map Q (default 0)
good:        forall q, Q[q] <= 1
step:        B[k] := if good then Q[k] else 0, for every k
law keys:    primary a, further g
```

The valid control is `B[a] <= 1 and B[g] <= 1`. With both flag instances supplied, TypeScript accepts it for both binder choices. Lean rejects only the collision's entry-admission test while accepting its start/step refutations; it checks the fresh-binder whole machine and derives its laws. This reproduces the same restriction on a small, meaningful example.

False controls are (i) `B[a] = 0 and B[g] = 0`, and (ii) `B[a] = B[g]`. For `a=0`, `g=1` the interpreter runs:

| State / request | B[0] | B[1] | Bounded control | Both false controls |
|---|---:|---:|---|---|
| initial | 0 | 0 | true | true |
| `Q = {0:1}` | 1 | 0 | true | **false** |
| then `Q = {0:2}` | 0 | 0 | true | true |

For each binder choice and each of these three laws, the probe tries four instance sets: none, primary key only, further key only, and both keys. All 16 false-law trials fail TypeScript checking; both complete valid controls pass. Reusing the valid proof for either false law also rejects (four more direct kernel checks). The six incomplete valid-control trials fail because instances are missing, not because the valid law is false.

**Outcome:** no accepted false law in this targeted probe. It is not an exhaustive search or a proof of general TypeScript soundness. The concrete run falsifies the negative controls, not the law actually accepted. The real law-12 collision is established harmless by the Lean alpha bridge, not by these tests.

## 2. Law 20: first failed node and why the row is valid

Law 20 is `carry:co-write:6282256ba10ee781 @step`. There are no lemma cuts. Full Lean-reconstructed hypotheses equal the directly encoded TypeScript `mcGoal` hypotheses. The original table, goal and retained tree are used throughout localization.

[paxos-law20-localize.ts](paxos-law20-localize.ts) checks each subtree under its **original complete goal and accumulated path**, not as a detached proof of a different goal. TypeScript accepts all **73 nodes / 37 leaves**. Lean's complete list of rejected leaves is:

```text
[[true, true, true, true, false], [false]]
```

With depth-first traversal, yes before no, these are `YYYYN` (first) and `N`. Rejecting ancestors are the root, `Y`, `YY`, `YYY`, and `YYYY`; the split rule itself is not rejected. The other 35 leaves pass. See [the detailed localization report](paxos-law20-findings.md) for full rows, path data, source locations and original terminal receipts.

### First leaf: YYYYN

The five inherited split rows are, in root-to-leaf order:

| Row | Decision |
|---|---|
| `carryKeyX - 63` | <= 0 |
| `Left[n:64,r:1] - 1` | <= 0 |
| `Left[carryKey:1,carryKeyXX#:64] - 1` | <= 0 |
| `carryKey - carryKeyX + 1` | <= 0 |
| `carryKeyXX# - size + 1` | **not** <= 0 |

The `Left[...]` strings are literal canonical TypeScript column names. The leaf's only step is `input 23`, whose row is `{1:1}` with source `fact 24`. The emitter compacts this to:

```lean
.leafAt [(lconst 1, .fact 24)] [.input 0] [] []
```

Lean's row-admission check is **false**, but `Cert.check` of that claimed constant row is **true**. This is neither a bad multiplier nor a bad arithmetic cut. The claimed row is not among the rows that Lean's `facts` function extracts syntactically.

### Singleton normalization changes row extraction, not meaning

Hypothesis 24 positively requires `or [carryKeyXX# < size]` at `YYYYN`. At `N` it positively requires `or [carryKeyX < 64]`. Both are singleton disjunctions.

- TypeScript `facts` (`kernel/kernel.ts:328–332`) filters disjuncts already known false by the path. Zero remaining disjuncts gives the constant row `1 <= 0`.
- The emitter's `reduceRight` (`lean-kernel/emit.ts:618`) turns a singleton disjunction into its bare atom.
- Lean `facts` (`lean-kernel/Kernel.lean:1341–1377`) of a positive bare `<` supplies its comparison row, even when the path contradicts it.
- `leafAtOk` requires the claimed input row in `srcRows` or `leafRows`; semantic derivability without a certificate step is not enough.

For the first failure, let `a = carryKeyXX#`, `b = size`. The two available, valid rows are:

```text
a - b + 1 <= 0     (hypothesis 24: a < b)
b - a     <= 0     (false split: a - b + 1 >= 1)
----------------
1         <= 0     (sum with positive multipliers 1 and 1)
```

At `N`, add `carryKeyX - 63 <= 0` to `64 - carryKeyX <= 0`. Again the sum is `1 <= 0`. There can be no satisfying assignment under either full context. The TypeScript step is sound here; the proof export fails to express that derivation after normalization.

### Checked local controls, not an invented counterexample

[paxos-law20-validate.ts](paxos-law20-validate.ts) proves the original two leaves reject and separate explicit three-step fragments pass. `first_source_inconsistent` applies unchanged `checkT_sound` to show that hypothesis 24 plus the **entire original first-leaf path** is semantically inconsistent. These statements retain the original table and path.

[paxos-law20-semantic.lean](paxos-law20-semantic.lean) checks a tiny control with hypotheses `or [x<y]` and `not (x<y)`. A JSON-round-tripped TypeScript tree passes, but its ordinary export fails Lean. Replacing the singleton by its bare atom makes the same tree fail TypeScript too. A separately expanded two-row arithmetic derivation passes Lean and proves the tiny goal unsatisfiable. This demonstrates the translation mismatch; it is **not** a false machine law or an accepted counterexample.

Only the two failed leaves are replaced in `diagnosticAdaptedTree`; all splits, other leaves, hypotheses and table remain. Lean checks that distinct tree. Because the localized rule is sound, the handoff's conditional request for an accepted false machine law does not apply to law 20.

## 3. Whole-family diagnostic check and original-machine theorem

[paxos-combined-check.ts](paxos-combined-check.ts) combines the two explicitly separated adaptations:

1. one quantified-flag alpha conversion;
2. replacing `YYYYN` and `N` only in entry 20's step tree by the checked arithmetic expansions.

`combinedPaxosProof` otherwise preserves the original entries, proofs and instance choices. Lean proves:

```lean
combined_entries_unchanged :
  combinedPaxosProof.map (·.e) = verified_proof.map (·.e)

combined_paxos_check :
  checkCMachine paxos_alpha_machine verified_decls combinedPaxosProof = true

combined_original_laws (ρ M) (hr : CReach verified_machine verified_decls ρ M)
  (ce : CEntry) (hce : ce ∈ verified_proof) :
  ce.e.Holds ρ (withCnt verified_decls ρ M)
```

The last theorem uses `paxos_reach_alpha`, `cmachine_sound`, and equality of the entry lists. It proves the **original captured statements on the original exported machine**, not just the new machine's Boolean checker output. Count views and caller-law inclusion were checked by the original capture/export audit; this follow-up does not add a theorem equating the qualified protocol encoding with its unrestricted source protocol.

The generated combined file contains none of the rejected original `verified_check` theorem, `sorry`, `admit`, or `native_decide`. Successful theorem dependencies are limited to Lean's existing `propext`, `Classical.choice`, and `Quot.sound` (some theorems need a subset). All checking uses ordinary kernel reduction / `decide`, ordinary tactics, and existing soundness theorems.

## 4. Coverage in the other 27 accepted certificates

[paxos-feature-census.ts](paxos-feature-census.ts) extracts the retained objects for all 29 captured protocols, checks packet identities against capture metadata, and matches successful Lean receipts to both packet and emitted-Lean hashes. It classifies the **actual laws**, not just the printed `found` summaries. [paxos-census-report.ts](paxos-census-report.ts) checks the receipt hashes again. Generated family names are tied to constructors in `core/carry.ts:94–95,168,387–390`.

For **every protocol below**, scan-prefix-with-further-key count = **0**, carry-co-write count = **0**, and the prior exact-family Lean check passed. Counts are other laws with further keys:

| Protocol | Other multi-key laws | Protocol | Other multi-key laws |
|---|---:|---|---:|
| client_server_ae | 6 | client_server_db_ae | 27 |
| consensus | 1 | consensus_epr | 18 |
| consensus_forall | 23 | consensus_wo_decide | 17 |
| firewall | 2 | learning_switch | 15 |
| learning_switch_i4 | 19 | lock_server | 2 |
| lockserv | 7 | lockserv_automaton | 7 |
| majorityset_leader_election | 11 | naive_consensus | 6 |
| quorum_leader_election | 3 | sharded_kv | 21 |
| sharded_kv_no_lost_keys | 0 | simple | 0 |
| simple_decentralized_lock | 1 | simple_election | 5 |
| simple_regular | 0 | tcommit | 1 |
| toy_consensus | 2 | toy_consensus_epr | 4 |
| toy_consensus_forall | 2 | two_phase_commit | 2 |
| twophase | 6 | — | — |

The original complete table, with per-protocol packet / Lean hashes and links to actual successful logs, is in [the census report receipt](../../runs/verify-all/paxos-census-report/paxos-census-report.log). The fresh census repeats those results and verifies that its row-array digest matches the inherited census. `paxos-lean-receipts.json` records these identities and the final checks. MLDR has no accepted family and is not in the denominator. No successful check of these other proofs establishes generic coverage of either failing Paxos feature.

## 5. Reproduction, evidence, and limits

The retained inputs are from `runs/verify-all/capture-all/capture-paxos_epr.log`, `ARCHIVE_BEGIN` base64 xz tar:

| Artifact | SHA-256 |
|---|---|
| Original packet | `dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386` |
| Original emitted Lean | `e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1` |
| Separate alpha packet | `54660f2c5d9e24473eb516749cbdcb88d3de4d0f41818a6f2faa3bf421e45823` |
| Separate alpha Lean | `453822882fcabdab514a04a2a2ddd570bfa9ea449199cfc8ca96d9e95b4a26ed` |
| Local law-20 diagnostic Lean | `3d47991d66529c90181efd31fe6165307164a2cf64e04e90978c41a1ef262966` |
| Combined diagnostic Lean | `170ac978ac261a918fc5917466fcc987aca19ccf3300ce4ef25600836bda2c2d` |

Fresh verification commands:

```sh
supercomputer run --jobs research/verify-all/paxos-lean-recheck.jobs.json \
  --out runs/verify-all/paxos-lean-recheck --class interactive --backend boat \
  --data runs/verify-all:evidence-all --data runs/verify-all/capture-all:evidence

# Before the final batch, save the intended commit message to runs/verify-all/paxos-lean-commit.txt.
supercomputer run --jobs research/verify-all/paxos-lean-final.jobs.json \
  --out runs/verify-all/paxos-lean-final --class interactive --backend boat \
  --data runs/verify-all:evidence

supercomputer run --jobs research/verify-all/paxos-lean-source-check.jobs.json \
  --out runs/verify-all/paxos-lean-source-check-v3 --class interactive --backend boat
```

The recheck independently regenerates/checks the combined semantic bridge, reruns the small-machine interpreter and TypeScript/Lean probes, and repeats the census. The final batch performs repository type/lint checks, commitlint and deterministic [receipt validation](paxos-lean-receipts.ts). Use `summary.tsv` job exits, not the scheduler client's exit. These are diagnostic checks, not timing benchmarks.

Fresh recheck batch `20261109-095541-v59lub` and validation batch `20261109-095835-qoe0j6`:

| Receipt under `runs/verify-all/` | Job | Exit | Job seconds | Outcome |
|---|---|---:|---:|---|
| `paxos-lean-recheck/summary.tsv` | combined | 0 | 105.10 | complete original-law Lean bridge |
| same | law12-probe | 0 | 8.57 | concrete runs, TS controls, Lean admission/control proofs |
| same | census | 0 | 0.81 | 29 packets, 28 accepted, 27 other matched Lean receipts |
| `paxos-lean-final/summary.tsv` | receipts | 0 | 0.03 | generated artifact, log, census and theorem-output integrity |
| same | commitlint | 0 | 0.82 | final commit message accepted |
| same | check | 2 | 26.80 | inherited unused v1 TypeScript error; see below |

Lean is **4.34.0**, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. The combined job's standalone semantic file and combined file exit 0 (`LEAN_WALL` 0.25 s and 82.52 s); the small-machine Lean check exits 0 (0.30 s). These are diagnostic runtimes, not performance comparisons. The complete long `ALL_EXACT_LEAN_NODES` pretty-print is truncated by Lean; the two-element rejected-leaf list is complete, and the whole-tree/whole-machine check theorems are kernel-checked.

The unmodified inherited `paxos-law12-probe-v1.ts:42` has `TS2353` (passing `hyps` to `encode`, whose API takes an `Exported` object). It is an abandoned, uncommitted predecessor of v2, not used by any final proof. The full-worktree `bun run check` correctly failed; this is not reported as a pass. To preserve that file, [paxos-lean-source-check.ts](paxos-lean-source-check.ts) runs the same compiler/linter with **only that file** additionally excluded, prints its SHA-256, and writes its temporary compiler configuration under the remote `research/verify-all/.paxos-source-check-*/` so that normal `node_modules` type resolution is retained. No root configuration or old file is edited. All other base-tree and research sources remain included.

Final source-check batch `20261109-100333-rpnd53`: `runs/verify-all/paxos-lean-source-check-v3/summary.tsv` reports `source-check 0 35.58 boat`. TypeScript exits 0; oxlint reports **0 warnings, 0 errors on 991 files**. The excluded historical file's hash is `34406958b4c2850babf73aae1644f35dfadcb20b54293f7ab5f350369f116b17`. If that uncommitted file is absent (a clean checkout), the helper has no additional compiler exclusion.

An earlier source-helper attempt (`paxos-lean-source-check`, exit 2) put its temporary configuration under `/tmp`, where package type lookup failed (`TS2688` for Bun/WebGPU types); no theorem was involved. The corrected-location v2 batch passed (46.63 s). V3 rechecks the final helper with the absent-file guard. All three logs are preserved rather than replacing the failed receipt.

The committed [paxos-lean-receipts.json](paxos-lean-receipts.json), SHA-256 `0eb3b5873889150ed61ccad7e0e4cc99a707a06c14223f20865ad95f91bad57e`, contains the combined artifact identity, all three recheck receipts, concrete interpreter results, and every other certificate's packet, Lean-file and matched-log hashes. The verifier extracted the archived combined Lean, recomputed its hash, required the original rejected theorem to be absent, checked the theorem output and all subprocess exits, and matched the fresh census digest to the inherited one. It did not just trust the outer process's exit status. All owned jobs are terminal before the final commit; no process was killed.

Historical failures are not evidence of successful proofs: alpha v1/v2/v3 and law-12 probe v1 were exploratory predecessors; law-20 deep/first-validate had diagnostic elaboration errors. Their logs are retained. The successful alpha v4, probe v2, law-20 terminal and fresh combined checks supersede them. No failed theorem or error-induced `sorryAx` is imported. Inherited untracked exploratory/unfinished assembly files were preserved; the final reproductions, supporting law-20 diagnostic history and their dependencies are committed.

No edits to `core/`, `kernel/`, `lean-kernel/`, or `research/protocols/`; no external solver, cache clearing, cleanup of untracked/ignored data, history rewrite, other-worktree modification, or push. A production change should be separate and reviewed, with Lean first: capture-avoiding alpha conversion / a semantic freshness bridge for admission, and a supported derivation or shape-preserving export for Boolean-derived rows. This report is evidence for that follow-up, not the implementation of either fix.
