# BAPA continuation for 0.49.1

Main's release split is fixed: **0.49.0 ships slices 1–2 at `142d1f5ab` with htv9qk parity.** Do not move/rebase that commit or rerun its consumed cohort. Current implementation work remains on `after/bapa`, in new commits only.

## Already established, and still not established

- The minimal unseeded rigid proof and original-source Lean wrapper pass.
- The original-Ivy `naive_consensus` model, its three GIVEN helpers and proof-only `learnedQuorum` exist. The abstract source Lean theorem passes. The full emitted unseeded certificate, ghost elimination and source-level export are still missing.
- The strategy is opt-in/default-OFF and untrusted ordinary `Instances` only. D diff review before merge or counted use still applies.
- Observed full attempt `20261114-062935-4bfabp` exhausted its own work budget, not the job timeout. Only `GIVEN unique vote per node @start` was emitted; no step/ghost/agreement root was observed. Do not diagnose a ghost-helper failure from that evidence.

## Verified finite-source progress

`20261114-092524-36xsij` passed 28 tests/13,699 assertions, strict TypeScript, type-aware lint and commitlint. The new original-source conformance test exhausts 29 reachable states and 3,132 state/request pairs (including refusals) for one 2×2×2 instance, and covers non-majority families, >64 coordinates, empty domains and three concrete premise mutants. See `research/bapa/notes/BAPA-NAIVE-RUNTIME-RESULTS.md`. No production, prover, kernel or Lean file changed.

## Parallel work now

1. **Finite source conformance (already in the reviewed slice-3 plan):** add an independent array-based interpreter of the pinned Ivy actions; compare enabledness and every observable relation with both the bound interpreter and compiled JS. Exhaust small reachable state spaces; cover arbitrary intersecting/non-majority and duplicate-extension quorum families, all three empty-sort situations, >64 coordinates, and concrete mutants dropping intersection, unique voting or fixed membership. This is finite testing, not symbolic acceptance. No production or trusted code changes are needed.
2. **Fable/t2 reads the observed search work before the next algorithm change:** request remains `research/bapa/notes/BAPA-FABLE-PROGRESS-REQUEST.md`, source `3d02f5853`, batch `4bfabp`. One concrete code lead is `instancesFor`'s two passes and repeated complete-binding joins in `extendFunctionInstances`; the observed output is already 427 tuples at 10 s while discovery keeps consuming work. Neither repeated closure nor a specific optimization is established as the cause without a finer measurement/control. Keep the original builder/checker and caps unchanged; no speculative retry or port-specific tuple.
3. **After reviewed strategy direction:** changed-path tests and actual worker-script minimal smoke first, then one observable unseeded port attempt with durable progress and an explicit own-budget outcome. Every failure stays retained. A proof must be checked by unchanged kernel/Lean with the original axiom exposed and ghost discharged before port acceptance.

The suite's majority/counting port proves intersection. This separate original-Ivy port assumes exactly intersection and covers any satisfying family. Helpers remain GIVEN, not found. Neither finite tests nor 0.49.0 parity are a substitute for the missing 0.49.1 proof.
