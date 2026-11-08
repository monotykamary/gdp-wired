# Track K report

Base: `8610af26c16cf8e50b5ec0564a154c6bf358d82c`; branch: `claude/track-kernel`.

## Independent-review follow-up

F1 is fixed in `53278bd9` at the new lemma-condition decision boundary: all-zero variable coefficients are treated as constants, matching Lean. The global `decide`, old tree checker, empty-list fast path, and proof-row layout are unchanged. The reviewer’s fixtures were captured once from the unmodified `df6f409e` checker (kernel SHA256 `6984ace7dea563b38aa93827558cfe209dd4978fb9ab994d92e4c2f8b9966433`) before the edit. `track-k-review-f1-v1/` passes 9 tests / 43 assertions and the independent Lean edge examples. F2 (`17a7bd21`) adds fixed-input tests for the exact-end slice, duplicate slices/rows, nested lemma trees, repeated/constant splits, cut-assisted eligibility, and cut/path order. The unchanged reviewer runner and all 12 unchanged substitutions pass their baseline; all 11 non-equivalent mutants are killed by unit tests in `track-k-review-mutants-v1/verified.json`. M03 alone survives: the out-of-range selection still fails closed downstream on these dense inputs, and the exact-end boundary is explicitly tested. F3 now explicitly documents TS acceptance as a strict subset of Lean, retaining legacy repeated/constant-split refusals rather than claiming exact equality. Post-fix static checking, all seven shards, Lean/conformance, strict Paxos 3/3, and a final unchanged mutant replay are queued. Previous evidence hashes are the pre-review snapshot, not the modified source. No merge is authorized. No merge will be performed.

## Pre-review baseline status (`df6f409e`)

The Lean-first rule, TypeScript mirror, unchanged-certificate conservation, semantic refusals, Lean export, and measured untrusted emission are implemented. The engine is frozen at `0e9afc3db2317abee2b96894de5dd83e2edf86f4`; all core/kernel/Lean source still matches that commit. The required automated gate pipeline and final helper/artifact recheck passed. **Independent review of the Lean statement and TypeScript mirror remains required before any merge; no merge or publish action was taken.**

| Gate | Verified result | Evidence |
| --- | --- | --- |
| Type/lint and focused refusal checks | 0 errors/warnings; 14 tests / 58 assertions | `track-k-final-engine-v1/final-admission.log` |
| Strict original-harness Paxos | 3/3: 28.964s, 28.800s, 25.712s; opt-in smoke 26.587s | `track-k-final-engine-v1/` |
| Lean soundness, mutants, exports | Passed; only existing `propext`, `Classical.choice`, `Quot.sound` | `track-k-final-static-v1/`, `track-k-shared-lean-v1/` |
| Unchanged C14, C9, C11 | All check with absent/empty lemma lists and zero search | `track-k-conservation/`, `track-k-final-static-v1/` |
| Paired IC3Syn 29 × 3 vs main 8610af26 | **28/29 vs 28/29 in every repeat; 84/87 each; no lost proofs; Paxos 3/3** | `track-k-final-ic3syn-v1/verified.json` |
| DuoAI ten paired | **10/10 candidate vs 9/10 main; no lost proofs** | `track-k-final-duoai-v1/verified.json` |
| Broken variants | **0/29 proven**: 11 refuted, 18 unknown | `track-k-final-broken-v1/verified.json` |
| Seven isolated test shards | **7/7 passed**; 713 Bun test passes, 18 existing skips, plus script checks/examples | `track-k-final-shards-v1/` |
| Quick bar | **Wrong 0; solid losses 0**, ten groups, three reruns per differing task; Lean 6/6 | `track-k-bar/runs/track-k-v1/{REPORT.md,report.json,verified.json}` |

MLDR itself remains **unknown in all three integrated runs on both sides**. This track supplies and measures the sharing rule; it does not claim a complete MLDR proof. The bar has timing-dependent non-solid losses, retained in its detailed report; “no lost proofs” above refers to the paired protocol suites, not every bar task.

Commits: `fa0b1e04` Lean rule; `0c4ed17b` TS mirror; `ecf1fa2f` conservation/refusals; `45b45aa9` exports; `3d68f642` untrusted emission; `0e9afc3d` row reuse. Failed experiments below are retained, not replaced by the final successful run.

The rule and proof obligations are recorded in `research/track-k/README.md`. Independent lemma trees are checked with the old checker; cuts are available only where the original path decides every condition; slices select hypotheses of the containing goal; empty lists take the exact old checker path. Both `Count.lean` and the actual `CountMachine.lean` wrapper are covered.

## Baseline

```
supercomputer run --jobs research/track-k/baseline-jobs.json --out runs/track-k-baseline --class interactive --vm-type large
```

The unchanged `Count.lean` baseline builds (2.18s job time), with the existing axiom set `propext`, `Classical.choice`, `Quot.sound`.

## Step 1: checked Lean rule

`runs/track-k-lean-v4/lean-count-cuts.log` records successful builds of `Count.lean` and `CountMachine.lean`, followed by all twelve kernel-reduced examples in `research/track-k/LemmaCuts.lean` (3.01s job time).

- `CutLemma` has concrete `Cert.Row` conditions/cut, the old `Tree`, and an optional checked index slice of the containing goal. The new section disables implicit variables.
- `lemma_sound` proves the cut under its declared conditions; `lemmaPath_holds` proves only eligible cuts preserve the path; `goalLemmas_sound` proves the same unsatisfiability statement as the old goal checker.
- `counted_sound` and `countedW_sound` retain the original semantic conclusions with an implicit lemma-list parameter. `CCert` defaults its new list to empty; `mc_sound` and `cmachine_sound` continue to compile.
- `checkTLemmas_nil`, `checkGoalLemmas_nil`, `checkCounted_nil`, and `checkCountedW_nil` establish the empty-list compatibility boundary.
- Executable examples accept a genuinely derived cut and legacy empty-list record payload, and reject citation before its decision, opposite conditions, the wrong or out-of-range slice, an empty proof, and self-citation.
- Axiom reports for the extended goal, counted, witness-generalized, MC, and machine theorems contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or new axiom was added.

Failed controls are retained: v1 exposed an unqualified row-evaluation namespace; the first executable examples exposed an unintended implicit row-type parameter and the changed arity of Lean positional structure notation. Rows are now explicit and the legacy payload test uses defaulted record notation. Old positional exported Lean text must be regenerated by the export update in step 5; no claim is made that a six-field positional constructor has seven fields. A malformed intermediate job manifest failed before scheduling and was repaired with JSON serialization.

## Steps 3–4: conservation and refusals

`runs/track-k-conservation/` authenticates the coordinator's pinned C14, C9 and C11 goal/proof bytes. All three check with both absent and explicit-empty lemma lists; search work and every search cost remain zero. Three isolated strict-60-second original-harness Paxos runs are proven (job times 20.82s, 20.85s, 28.97s; exact search times are in the JSON logs), each with `STRICT_EXIT=0`.

`runs/track-k-mutants-v3/` passes eight TypeScript tests / 35 assertions and the kernel-reduced Lean examples. Both reject use above or opposite the declared condition, a non-refuting proof, an incorrect or out-of-range slice, circular/self-support, a read capturing a goal variable, and witnesses capturing a parameter, a `?flag`, or a quantified law's skolem. Lean also proves the positive full-machine fixture with nonempty lemmas. Lemma entries themselves bind no reads or witnesses; the containing certificate's original freshness checks remain mandatory.

The failed v1/v2 controls were fixture errors, not fixed by weakening the checker: the read-extended tree needed its input indices rebound, the count declaration uses `map` rather than `name`, and a skolem-capture test must use an actually quantified law. Lean record-layout mistakes were corrected. No trusted checker changed after the successful conservation replay.

## Step 5: export and conformance

`runs/track-k-export-library-v3/` passes the complete existing counted-example library (20.24s) and expanded conditional-cut conformance (11.16s). The latter includes the actual shared TypeScript fixture, wrong conditions/slices and non-refuting proofs, duplicate path atoms, unconditional cuts, full machine certificates and capture mutants. Both explicit public `toLean` routes compile, and report only `propext`, `Classical.choice`, `Quot.sound`. `leanProject` now ships the counted modules via the generated library.

Main and lemma proofs share a dependency-ordered table; each lemma retains its own original slice and path. New path layouts use checked row lookup rather than mislabeling legacy atom hints. The original count-example generator writes to its directory argument, not stdout; v1 preserves the mistaken driver invocation, repaired in v2/v3. Production export code and all unchanged counted examples pass. The mirror/export and final frozen-revision typechecks report zero errors/warnings; the final static batch also passes the public export routes.

## Step 6: untrusted sharing experiments and final measurements

The pinned read-only Track M snapshot is recorded by `research/track-k/snapshot-replay.ts`. The current source replay emits 3,163 nodes / 1,582 leaves (the source has advanced from the brief's 4,427-node version). Its isolated send branch checks; it is **not** a complete MLDR proof. The portable capture records opaque term definitions as well as the tree and exact root scope, so a fresh process first re-interns columns and authenticates the original with no search.

- v1 selected enclosing subtrees and expired after 60s of transport; no candidate certificate was accepted.
- v2 used cached proposer rows and smaller derivations, but copying dependency chains grew the certificate to 7,755 nodes; the proposer refused it as not smaller.
- v3 shared only independent derivations and minimized conditions by exact row transport. Its 52-cut certificate checks, with 3,101 total nodes / 979 main-tree nodes. On that same VM, the old check took 31.341s and the new check 10.723s; construction took 27.856s, so overall sharing was **slower**, not an accepted performance result.
- The next mechanism retained pre-widening source proofs as optional **untrusted** provenance; v4 still had excessive construction cost. The selected v5 strategy inlines only required, independently proved prerequisites, uses traced conditions rather than expensive greedy minimization, and accepts by support-weighted checking work. Its cold portable replay checks with 4,919 total nodes, 809 main nodes and 70 lemmas (7.065s check, 13.761s construction versus 15.367s old check), so this cold measurement alone is still slower. V6 removed the compact-candidate cutoff and worsened the result (6,351 nodes, 10.498s check, 17.624s construction); it was rejected and the cutoff restored.

The pre-cache focused tests passed: 12 tests / 53 assertions, including a forged-provenance refusal. Three live same-VM v5 pairs, with common provenance capture enabled, all improved: 58.693→43.128s, 45.456→42.700s, 46.233→42.032s; check time fell from 24.982–29.442s to 8.196–8.663s. These are isolated send branches, with all original work counts unchanged (2,753), not full MLDR proofs. The stricter comparison disabled provenance in each baseline and did **not** reproduce those gains: 39.404→55.957s, 47.831→47.850s, and 49.470→59.412s. The next mechanism caches the exact rows already computed by untrusted transport, keyed by goal and ordered path, rather than retaining large source-proof graphs. Its first fair pilot improved 58.447→50.833s (12.184s construction, 13.004s check); the first three-repeat control in `runs/track-k-cache-final-v1/` improved two of three wall times, so it was not treated as a full win. Row-identity/index memoization and eliminating duplicate production checks completed the final revision, `0e9afc3d`. Production now proposes without a duplicate per-goal check: its complete family checker remains authoritative.

`runs/track-k-final-static-v1/` passes all 7 static/Lean/export/conservation jobs. A subsequent lint process in the v6 experiment was SIGKILLed by the host, not a type or lint diagnostic; the isolated larger-memory retry in `runs/track-k-final-check-v2/` passed. A later receipt-helper numeric-sort lint error was fixed before the next final check.

The real emitted 70-lemma send certificate now also passes Lean kernel reduction: `runs/track-k-shared-lean-v1/shared-send-lean.log`. The exported theorem `shared_send` and the rule theorems use only `[propext, Classical.choice, Quot.sound]`; no native-decide axiom was introduced. The portable artifact is `runs/track-k-shared-proof/certificate.json.gz` (SHA256 `4f5ed02ec55b86bd41342475a5e19012367ed4aec4dc0f92d56bc8ed30ddb26e`). An opt-in production admission pass (`GDP_COUNT_LEMMA_CUTS=1`) now preserves source provenance and proposes conditional certificates inside the existing deadline; the original proof remains the fallback and the entire family is still checked. It remains opt-in: the broad regression gates test the conservative default; only the send comparison and a Paxos smoke test exercise opt-in emission. The frozen revision passed its full ordered static/refusal/Paxos admission in `runs/track-k-final-engine-v1/`: three strict production proofs plus an opt-in smoke proof, all below 60s. Its fair live send pairs now all improve with baseline row-hint capture disabled:

| Run | Old wall | New wall | Old check | New check | Construction |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 46.518s | 35.964s | 29.292s | 7.103s | 8.280s |
| 2 | 39.842s | 30.423s | 22.854s | 5.666s | 8.256s |
| 3 | 49.080s | 35.668s | 28.239s | 8.173s | 9.016s |

All have identical search work (2,753), 70 independently checked lemmas, 809 main-tree nodes, and 4,919 total nodes versus 3,163 originally. Total nodes increase because prerequisites remain independently replayable; fewer nodes are checked against the full 172-hypothesis context. This is an isolated send-branch improvement, **not** a whole-MLDR proof or a sub-second checker claim. The remaining trusted-tier gates completed through `research/track-k/run-final-gates.sh`; the results are summarized above. The final helper/artifact check also passes in `track-k-final-source-check-v2/`, reproducing the byte-identical Lean file already kernel-checked.

## Reproduction and final evidence

Run from this worktree. All substantive commands use boat; the `check-gates.ts` and `check-bar.ts` commands only read completed receipts.

```sh
# Original Lean rule, conformance, and unchanged certificates.
supercomputer run --jobs research/track-k/final-static-jobs.json --out runs/recheck-static --class gate --vm-type large --data runs/track-k-input:research/track-k/input

# Real 70-lemma certificate, checked by Lean kernel reduction.
supercomputer run --jobs research/track-k/shared-lean-jobs.json --out runs/recheck-shared-lean --class gate --vm-type large --data runs/track-k-shared-proof:research/track-k/shared

# Static check, refusal tests, and the portable certificate with negative controls.
supercomputer run --jobs research/track-k/final-source-check-jobs.json --out runs/recheck-final --class interactive --vm-type large --data runs/track-k-shared-proof:research/track-k/shared

# Ordered strict admission and paired performance replay (pinned Track M snapshot).
supercomputer run --jobs research/track-k/final-engine-jobs.json --out runs/recheck-engine --class gate --vm-type large --data runs/track-k-send-input:runs/track-k-send-source

# The remaining gates, with a new output suffix (uses frozen baseline archive).
bash research/track-k/run-final-gates.sh recheck

# Recheck the recorded results, without searching again.
bun research/track-k/check-gates.ts paired runs/track-k-final-ic3syn-v1
bun research/track-k/check-gates.ts paired runs/track-k-final-duoai-v1
bun research/track-k/check-gates.ts broken runs/track-k-final-broken-v1
bun research/track-k/check-gates.ts shards runs/track-k-final-shards-v1
bun research/track-k/check-bar.ts runs/track-k-bar/runs/track-k-v1
```

The baseline archive is `runs/track-k-main-8610af26`, made from `git archive 8610af26` with the initialized vendor contents copied in. The source snapshot manifest is `runs/track-k-send-input/manifest.json`; reconstruct it using the README and compare hashes before substituting a newer Track M snapshot. The portable real certificate is self-contained and needs no Track M source.

The final source-check v1 passed type/lint and all 14 tests, then failed to open the portable artifact because ignored `runs/` files are not uploaded automatically. The v2 command supplies the explicit `--data` mapping shown above. V2 passes the static check, all 14 tests, and portable-certificate refusal controls. It regenerates the exact previously kernel-checked Lean text (SHA256 `127782c79bb244825e26f52af47f9ae3ef5f88868d121671c3875be7e21bb083`).

Recorded source, input, and receipt hashes are in `runs/track-k-final/SHA256SUMS`; check them from the repository root with `shasum -a 256 -c runs/track-k-final/SHA256SUMS`. The detailed bar report is retained without claiming its non-solid timing flips as regressions.

All substantive builds, tests, and measurements ran on boat. Work was confined to this worktree; Track M files remained read-only. Independent review is coordinator-owned and still required before any merge.
