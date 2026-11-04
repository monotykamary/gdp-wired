# Historical PROTOCOL admission map — accepted research integration

This is an additive status map, not a rewrite of the earlier frozen RESULTS.
Step checkpoint: `3efb88ab`; frozen canonical checkpoint: `e7819c87`.
The separately reviewed egraph-only integration `7fe2f3c3` was fast-forwarded
locally onto `9e7a8b42`; no push or release.
**Native H01, fullM2 and full-frontier/runtime admission remain open.**

| PROTOCOL item | Retained evidence | Status / remaining admission |
|---|---|---|
| 1: manifest-first historical input provenance | `archive-meta/store-manifest.json`, `inputs/materialized-manifest.json`, `BASELINES.md` | Preserved. No new archive reconstruction or worktree mutation needed. |
| 2: canonical engine / six-law per-focus baseline | Engine `444ece6e`, original `runs/astra-history-m2/m2-baseline.log` | Original outcomes preserved. Do not substitute incidental failures in another focus invocation. |
| 2: P1 proposals unique | Exact attempt raw SHA `634bcc43ec28aef4256b107620976299ddb5ecd7deb4dc9f7ce589aa521a112c` | Both start and step certificates freshly checked in v21, including exact goal hashes and source-witness freshness. |
| 2: P2 vote proposed | Raw SHA `4dcefbd3ffba095e8c2f5c9afd57056c9bf14cea8a0d5ee5bf567cf081437bbc` | Both start and step certificates freshly checked in v21, including exact goal hashes and source-witness freshness. |
| 2: P4 one_b left | Raw SHA `7199450fbf8c61e454ab5f9b59171b51bbdf722dddcc79ece447fc3a834f325e` | Both start and step certificates freshly checked in v21, including exact goal hashes and source-witness freshness. |
| 2: P5 choosable | Raw SHA `fe20786b55676014e03f0112269e6933a8036465c56f79e9b231700028ef2f36` | Both start and step certificates freshly checked in v21, including exact goal hashes and source-witness freshness. |
| 2: P3 step | `P3-STEP.md`, retained proof `d72bcca7…` | Checked and independently accepted by coordinator. |
| 2: safety step | `SAFETY-STEP.md`, retained proof `24313e87…` | Independently accepted in coordinator batch `20261104-131511-nm55yw`; `SAFETY-BRIDGE-v19/ACCEPT.md`. |
| Safety/P3 starts — complete | `proofs/safety-start.json`, `proofs/p3-start.json` | V22 explicitly generated and cold-checked the two originally missing starts under the original contexts and budgets. Both are included in the independently accepted canonical conjunction; neither was inferred from a historical step failure. |
| Canonical six-law conjunction | `CANONICAL-CONJUNCTION.md`, `proofs/canonical-six-law.json`, `canonical-v24.json` | Independently accepted in coordinator batch `20261104-133114-cycaqf`: all 12 default goals, complete kernel check, and both negative controls. Research-only local integration is complete; native/full-gate admission is not. |
| 3: comparison/attribution | All negative experiments retained; native-root scope audit off/on resolves to the same proof | The exact historical conjunction is closed, not an e-graph superiority claim. Package deletion rejects the certificate; it is not by itself a fresh native-root package-ablation solve. |
| 4–5: exact TIP theorem and genuine lemma graphs | Statement `225ccffb…`; two full graphs `d6f0f654…` / `492b6821…`; `proofs/materialized-manifest.json` | V21 preservation was reviewed and accepted. Both full graphs and all four negative controls per graph passed again on the composed integration tree; no new translator/prover or dirty historical wrapper run. |
| 6: source/input/proof binding and limits | Per-run source pins, native receipts, separate validation phases below; raw failures retained | Shared proof guards remain 2m/25s, not hard CPU/RAM guarantees. Preservation replay is one sequential job, requested 2 CPU/4096 MiB/600s. |
| 7: native producer/full gate | Owned by coordinator/Sol; see current native admission records | Research-only local integration does not close native H01, fullM2, runtime/producer or full-frontier admission. No push, release, production-runtime or timing claim. |

## V21 preservation result and compatibility boundary

Batch `20261104-131758-31gmal`, worker 0, freshly verifies all eight positive
certificates and both TIP graphs with their removal/corruption/rank controls.
No prover is imported. Type checking, scoped lint and commitlint pass.
`preservation-v21.json` pins the result; SHA256
`522e4ea42fbf1c9565d353bb5fed94ad2d2220d5ffb42f93fc91d3ead936cc51`.
Coordinator review accepted this owner replay for all eight original-context
P1/P2/P4/P5 start/step certificates and both TIP graphs with their controls;
it was not a second independent coordinator replay of those original contexts.
Review: `runs/coord-reviews/HISTORICAL-PRESERVATION-v21-REVIEW.md` in the
coordinator workspace.

The positive attempts' machines/law sets are not byte-identical to safety's.
A separate scope-respecting structural diagnostic finds that bound-variable
renaming (and ordering the law set by name) makes all four match exactly.
This diagnostic was not certificate transport. V24 separately performs explicit
renaming/reindexing and checks the complete canonical packet in the kernel.
The raw false equality flags in the v21 receipt are retained, not overwritten.

## V22 starts and V24 canonical assembly

V22 generated only the missing safety and P3 starts from their original frozen
contexts: two proof queries, each with the unchanged 25-second ceiling and
additional 2m guard. Both cold-check. No preserved positive was re-solved.
V24 uses the capture-checked binder bijections and law permutations to transport
retained certificates, preserving row multiplicities, then checks the actual
default 12-goal canonical conjunction. Fresh-process replay accepts it and
rejects both a missing start certificate and the removed direct safety package.
See `CANONICAL-CONJUNCTION.md` for exact hashes and the preserved V23 metering
API failure. Accepted original step/search artifacts remain unchanged.
This is proof assembly, not one fresh bounded solve or a native H01 admission.

## Independent canonical acceptance and local integration

Coordinator batch `20261104-133114-cycaqf`, worker 0, independently checked the
exact original machine and ordered six laws, twelve unique default goals,
all twelve source-certificate hashes and canonical obligation/goal hashes.
The full `checkCountedLaws` passed; missing-start and direct-package controls
rejected. No prover or transport helper was imported. Acceptance:
`runs/coord-reviews/CANONICAL-v24/ACCEPT.md` in the coordinator workspace.

The isolated `7fe2f3c3` candidate was then reviewed and fast-forwarded locally
onto main `9e7a8b42`: exactly 187 egraph additions, preserving every non-egraph
path, including standalone/frontend, exports/config, core/kernel, lifecycle
and query. The original `e7819c87` and all failed evidence remain frozen.
Acceptance: `runs/coord-reviews/EGRAPH-INTEGRATION-7fe2f3c/ACCEPT.md`.

Validation phases are separate:

- Before the final guard: full egraph regression, **58 tests / 275 assertions**.
- After the guard: **2 targeted tests / 8 assertions**, all six maps unchanged,
  both research typechecks and scoped lint; not a full-suite rerun at that stage.
- On the actual composed integration tree: **58 tests / 277 assertions across
  all 19 egraph test files**, both research typechecks, project-source lint,
  canonical cold replay/both controls, both TIP graphs/eight controls, six-map
  audit and commitlint. Batch `20261104-140857-fbyqfn`, worker 0.

The broader protocol scripts that launch historical searches were not run.
No historical proof search or reassembly accompanied integration. Native H01,
fullM2 and the full-frontier/runtime gate remain open; no push or release.

## Preservation procedure

`inputs/m2/positives/manifest.json` binds each original positive attempt and its
original ordered context/proof/start/step hashes. `preserve.ts` reconstructs and
checks those exact certificates with source-witness freshness, in separate fresh
processes. It also reports whether their machine and unordered six-law set match
the safety source; differences must not be silently combined.

TIP replay checks the pinned 612-byte historical statement and both pinned full
nine-node graphs, all premises/descent through `refuseCyclic`, and rejects removal
of either root use, helper corruption, and nondecreasing rank. It imports no
prover. Existing translator agreement and broken-variant evidence remain in the
frozen RESULTS; they are not mislabeled as newly rerun.
