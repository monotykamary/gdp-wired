# Canonical six-law conjunction — retained proof assembly

## Scope and result

V24 checked the **actual default twelve start/step obligations** of the archived
safety machine and its complete original six-law set. This is an assembly of
retained complete certificates, not one new 25-second solve. No prover is
imported or called by the assembler or cold checker. The complete conjunction
is independently accepted, and its egraph-only research integration was
fast-forwarded locally as `7fe2f3c3`. Native H01, fullM2, production-runtime
and full-frontier admission remain open. No push or release occurred.

Final packet: `proofs/canonical-six-law.json`, 99,430 bytes, SHA256
`212fa129969cfbd315fac23d6aeebb3e1df1450b943b7c0309c31b0b9d50a8f9`.
Receipt: `canonical-v24.json`, SHA256
`7f38fa90007dbe1acee3b3533cb0183469b842b854c69d99cf5a85396be37236`.
Boat batch `20261104-132723-etrtsc`, uploaded tree `199a87c8bfd0`, worker exit 0.
Raw log/controller: `runs/astra-canonical-v24/` (outside Git).

Canonical JSON machine SHA256:
`62db0a8c310d23638fc9841c41e93d6275125234c0cd73ed2aeb0c4e7cae9b66`.
Complete ordered law-set SHA256:
`997a5df9a4aca6f83ec6b6fd02a823dfd1763cacd67615e5eb0d2ed9a601b3d1`.
The producer and fresh checker verify these unchanged before/after. The packet
also records the archived compressed input pin and unchanged original artifact
hashes. Trusted kernel/checker sources were not modified.

## Two originally missing starts — now certified

V22 batch `20261104-132127-i6q1js`, worker 0, made exactly two proof queries under
the original contexts and budgets: 25,000 ms outer ceiling plus the 2m work guard.
Both certificates pass in-process and fresh-process checking:

- `proofs/safety-start.json`: `0764d08c7f0fe01222bb77666337b51b88ffa62ca3715295afbfc30ac3836336`.
- `proofs/p3-start.json`: `3560a3b55b7dd9e0fca4da96201e0f569f4a419cf268b33f130a45b7ceafdc51`.

They were explicitly generated, not inferred from historical step failures.
The eight preserved positive certificates and independently accepted P3/safety
step certificates were not re-searched or changed. The V21 owner replay of all
eight original-context positives and both TIP graphs/controls was reviewed
and accepted; that review was not a second independent replay of those
original contexts. V21's raw identity mismatch remains true and retained.

## Transport and admission

`context-bindings.ts` records a capture-checked scoped binder bijection, with
free names, rigid symbols and constants unchanged, and a permutation of the
same six named laws. `recovery/conjunction-bookkeeping.json` retains those maps.
That structural correspondence alone is not a proof admission.

`canonical-bundle.ts` instead builds the default all-law obligations without an
index/focus argument and requires twelve unique exact `(law,start/step)` names.
Each target is used as generated, not altered to fit a proof. Metadata terms and
linear columns are renamed; leaf input references are reindexed to equal target
rows. Every renamed source hypothesis must occur in the target, including its
multiplicity. Cuts and arithmetic derivations are retained, not solved again.
Every transformed certificate is kernel-checked. The complete packet then passes
`checkCountedLaws`, including its witness-freshness checks.

| Law | Source → canonical start rows | Source → canonical step rows |
|---|---:|---:|
| one value decided | 2 → 2 | 242 → 242 |
| P1 proposals unique | 2 → 2 | 37 → 37 |
| P2 vote proposed | 2 → 2 | 38 → 38 |
| P3 decision has quorum | 2 → 2 | 77 → 77 |
| P4 one_b left | 2 → 2 | 36 → 36 |
| P5 choosable | 3 → 3 | 56 → 56 |

The packet retains each transformed certificate, source/canonical goal hashes,
actual canonical obligation hash, source/transformed certificate hashes and the
source context mapping. Safety uses its original canonical context unchanged.

`canonical-cold.ts` imports neither the assembler/transport helper nor a prover.
In a separate fresh process it reconstructs the default twelve obligations from
the pinned canonical input, checks the record/certificate hashes, consumes the
complete packet through `checkCountedLaws`, and rejects both controls:

1. remove `one value decided @start`;
2. retain the safety tree but remove its direct-law/count package, restoring the
   pinned original count metadata and original focus-law instances.

All three outcomes are recorded by `CANONICAL_COLD`. Source pins remain unchanged.
Transport used 146,916 metered visits under its 2m/25-second guard. These are
transport visits, not prover work or a runtime/performance comparison.

## Independent acceptance and local integration

Coordinator batch `20261104-133114-cycaqf`, worker 0, independently verified the
frozen original machine and ordered six-law set, all twelve unique default
goals, every source-certificate hash and canonical obligation/expanded-goal
hash. The complete `checkCountedLaws` passed, including witness freshness;
both missing-start and direct-package controls rejected. The checker imported
no prover, assembler or alpha transport. Acceptance is recorded in the
coordinator workspace at `runs/coord-reviews/CANONICAL-v24/ACCEPT.md`.

The separately reviewed egraph-only candidate was fast-forwarded locally:
commit `7fe2f3c3420e9c6034b5980a7b3851a51d2a6bb6`, tree
`3fe68cb153fdde9f157886bc80835ee8d11be7f5`, parent
`9e7a8b422663edf6182ae21b74767d4bf0a6d863`. Exactly 187 egraph additions
preserve the frozen egraph bytes and every non-egraph path on main. This was
not a whole-branch merge or lifecycle conflict resolution. Acceptance:
`runs/coord-reviews/EGRAPH-INTEGRATION-7fe2f3c/ACCEPT.md`.

The composed-tree receipt is retained at
`../gdp-wired-astra-egraph-integration/runs/egraph-integration/receipt.json`,
SHA256 `6114440571c4cda6d70e1dabf8c9f4bd10776fc4f4475386b2445547bfffab0e`.
The original `e7819c87`, packet and failed evidence remain unchanged.

## Validation and preserved failure

V24 passes both research TypeScript projects, scoped strict/type-aware lint,
three transport tests/five assertions, and commitlint. V22 also passed its two
context-binding tests/six assertions and type/lint checks. Before the final
free-name guard, the full egraph regression passed in batch
`20261104-132901-dvo2d5`: 58 tests, 275 assertions,
zero failures. V25 batch `20261104-133025-iwfxrd` then passed the targeted
free-name guard audit (two tests/eight assertions, clean types/lint). The guard
rejects flat renaming of a source name that is also free elsewhere, as well as
target capture. All six recorded maps remain identical and the frozen packet
is unchanged. `canonical-bindings-v25.json` records this audit and the full
regression; no proof regeneration or search was performed. The exact V24
helper source remains at `runs/astra-canonical-v24/source/context-bindings.ts`
for comparison with that receipt’s original source hash. These are distinct
pre-guard and targeted post-guard validation phases.

The later actual composed integration tree passed the complete **19-file
egraph suite: 58 tests / 277 assertions**, including the post-guard tests, in
batch `20261104-140857-fbyqfn` (worker 0). Both research typechecks, strict
type-aware project-source lint, canonical cold replay and both controls, all
six binding maps, both TIP graphs/eight controls, and commitlint passed.
Broad historical protocol scripts that launch searches were intentionally not
run; this is not the full repository/frontier gate.

V23 already produced kernel-accepted proofs but its worker exited 1: TypeScript
caught a one-argument call to zero-argument `Meter.tick()`. Its raw log and source
snapshot remain at `runs/astra-canonical-v23/`. V24 charges each visited row
explicitly, adds the stronger default-obligation/source/control audit, and
passes. V23 is not represented as a successful final checkpoint.
