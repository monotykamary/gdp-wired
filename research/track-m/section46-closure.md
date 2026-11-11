# Section 46.4: greatest closed held family

Base: `f5851b03`; lane B private worktree, no `counts.ts` edits.

`core/count-closed-family.ts` exposes:

- `greatestClosedCountFamily(order, heldMap, {basis?, tick?})`: stable greatest fixed point, direct missing dependencies, root blockers, terminating witness paths. `basis` must contain only A's already-native-checked basis; this helper does not certify it.
- `closeGreatestCountFamily(target, heldRows, {legacy, reserve, submit}, options)`: original row/payload references, no callback for empty/unfunded G, one subset submit at most. Target-in-G delegates to the unchanged legacy callback without rebuilding its family. Outside targets remain outside, regardless of the subset result.

The graph is untrusted scheduling metadata. The callback must assemble/reindex and natively check G's exact INIT/STEP obligations. Bad metadata does not turn a native refusal into acceptance. The helper itself performs no native or search operation. Production wiring and recipe graph remain lane A's responsibility.

## Gate

`jobs-section46-closure.json`, boat gate, run `section46-closure-v2`: **11 tests / 1830 assertions pass**. All five required negatives, false INIT/STEP native mutations, empty/unfunded/cancelled paths, explicit basis, exhaustive 3-node closed-subset containment. Full TypeScript check, type-aware lint, both commitlint configurations, before/after source hashes pass. Receipts: `section46-closure-gate/`.

The first gate exposed a test fixture error: its purported bottom-layer certificate still used the full family's row indexing. Native checking correctly refused it. The corrected fixture constructs the bottom certificate in its exact one-member context. This is not a production repair or a claim about T301's measured artifact.

No measurement campaign, benchmark claim, search change, kernel change, W change, full-family closure claim, or 1G run. Section 44 remains parked; existing holds unchanged.
