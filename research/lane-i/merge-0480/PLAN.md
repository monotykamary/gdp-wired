# 0.48.0 merge gate (lane I)

## Source and purpose

- Exact source: `2de2ce89f9f93eb8feb5fbfb3a355da3adafc4ef`.
- Parents: `4d5b89fe` (I integration evidence) and `f95f306d` (main 0.48.0).
- Coordinator priority: bring all 0.48.0 false-proof, native cross-check,
  unchecked-exit and privacy changes into the common integration before
  resuming the request-space quotient.
- The merge is committed. Local runtime, static and scoped compatibility
  validation is complete; D approval remains **pending**.
- Outcome: semantic/charged-work identity holds for all 28 off receipts.
  The stronger raw-identity hypothesis is false in 9: only unpriced evals
  (and, in two, astNodes) decrease. This is retained, not normalized away
  in the strict audit. See RESULT.md and AUDIT.json.

## Falsifiable merge hypothesis

Taking all release safety changes, while retaining counted time at the two
conflicting expressions, preserves the release's source-validation semantics
and the existing counted endpoint. On the 28 mathematical originals it should
retain all checked results and preserve normalized flags-off receipts. Any
changed result, changed candidate hash, forbidden counted clock read, missing
source check or loss of the previously observed finite cap falsifies this claim.
Do not restore old behavior by weakening a 0.48.0 check.

## Resolution and safety boundary

Only `core/dsl.ts` and `core/infer.ts` conflicted. The DSL resolution preserves
`translationVerdict` after `proveStepsWall`; the inference resolution preserves
the release's internal model-only candidate proving and first-pass negative
model evidence. Both conflicting real-time reads use I's `countedSearchNow`.
All incoming native/source validation, extraction, law and CLI safety files
are byte-identical to main's release version. `kernel/`, `lean-kernel/` and
`core/check.ts` have no merge delta against I's first parent.

`private/` remains ignored and has no tracked entries. The archive is made
from the merge commit, not from a dirty checkout or private fixtures. No
historical reproducer was added back. Existing release research path scrubs
are accepted as supplied by main.

## Gate

`gate.jobs.json` runs on boat: 28 strict counted originals, 28 flags-off
originals, native/CLI safety tests, extraction tests, inference/Effect tests,
counted-cap regressions, static check/complete roster, and commitlint.
Each census receipt records SHA-256 digests of the resolved
`kernel/kernel.ts` and `core/check.ts` source paths before source imports.
The targeted suites additionally verify the protected identity list and the
release safety-file Git blobs inside the extracted archive.

The independent audit checks receipt hashes, source IDs, checker custody,
raw ledger sums, units, forbidden-clock counts, checked verdict retention,
flags-off identity and the existing **finite-census** 1,024-unit slack. This
is not a universal slack proof and does not remove the exported factory's
later-external-deadline limitation. No calibration transfers to this merge.

## Paused quotient

The uncommitted quotient prototype is isolated in path-scoped Git stash
`8b630c720f76cf17877e2b6812269016a13be795` (no `.reflex-saved/` changes).
Its untested files are `core/request-quotient.ts`, its test, a small opt-in
`core/exists.ts` BFS hook and a unit-job file. Resume only after staging this
merge gate. The prototype is not in the merged or tested source.
