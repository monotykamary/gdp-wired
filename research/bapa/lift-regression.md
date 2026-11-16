# Unified LIFT regression infrastructure

**Not a 27/27 native result.** All 27 source fixtures are frozen (24 native
extractions and three current-constructor special sources); 14 regression unit
tests passed on the remote frozen-03 preparation snapshot. This suite retains
27 historical acceptances across different
snapshots. A new 27-job native run on one final frozen implementation is still
required. The only permitted early jobs are fixture extraction and unit tests.
`allSizesProven` is always false. Proving the provided encoded source machine and
laws is not independent verification of TLA source.

## Files and API

- `lift-regression-inputs.json`: 27 data-only identities, accepted capsule hashes,
  mount paths, original locations, and historical artifact directories. Toy uses
  `runs/bapa-toy-reproduction-02/toy-reproduction-2-independent-d9942n.files`;
  sharded uses `runs/bapa-release-sharded-01/replay-sharded_kv.files`. Never retry
  or modify the lost toy run or any historical run.
- `lift-regression-manifest.ts`: inventory-only builder. Reads retained successful
  receipts/emission hashes/logs; audits exact historical source/family names and
  axiom sets with **product** `auditLiftLog`. No legacy emitter is imported.
- `lift-regression-manifest.json`: reviewable baseline + current fixture status.
  Missing fixtures remain explicit pending rows; there are always exactly 27.
- `lift-regression-prepare.ts`: native capsule reader -> data-only source JSON.
  It uses product `readFamilyCapsule`, verifies CAPTURE and lossless JSON equality,
  never calls an emitter or Lean. Refuses special-source entries by scope.
- `lift-regression-prepare-all.ts` and `lift-regression-prepare.jobs.json`: fresh
  child process for each of the 24 native fixtures, plus pure unit-test job.
- `lift-regression-worker.ts`: fresh process for one ID. Uses one product
  `lift(capsule, source, out, options)` call, then ordinary `lake build` and
  `lake env lean BapaProof.lean`; re-audits output with product `auditLiftLog`.
  No per-ID algorithm dispatch, handwritten protocol Lean, or search.
- `lift-regression.jobs.json`: **final-freeze-only** 27 native job recipes.
- `lift-regression-report.ts RUN_DIRECTORY`: rehashes downloaded project/logs,
  re-audits the exact baseline and requires all 27 IDs on one actual implementation
  inventory and one claimed frozen snapshot. Nonzero on any missing/failed case.

## Fixture contract

`lift-fixtures/ID.json` is `gdp-lift-source/v1` JSON: `schema`, `id`, `machine`,
`laws`, plus optional product-supported naming-only `theorems:{family,source}`.
The full exact bytes are SHA-bound; machine/law ASTs are never pre-normalized.
The 24 native fixtures explicitly freeze `capsule.original`, not independent
TLA reconstruction. Three special fixtures must be supplied from **current accepted
source constructors**, not the old bounded capsule original. Their provenance
retains constructor origin/hash, naming-only changes, and historical AST equality
(or mismatch); fresh binder differences remain in the fixture. Native bridge
checking, not fixture rewriting, must justify correspondence.

Do not replace the historical baseline with newly generated names/axioms. Naming
metadata requests mechanically generated aliases for the old names. Historical
alpha receipts contain an aggregate `source_laws` theorem as well as per-law
names: every historical name remains a required axiom answer, while the new
per-law coverage list must have exactly one unique baseline name per source law.

After SHA-verified preparation download, read each output JSON/provenance before
copying it to `lift-fixtures/`; then rebuild with:

```sh
bun research/bapa/lift-regression-manifest.ts
```

This command is small inventory work, not a native replay. Source fixtures have
no acceptance merely because they parse or because their baseline was accepted.

## Remote execution and immutable snapshots

Use `supercomputer --skill`. All tests, extraction and Lean jobs run remotely.
Take a detached snapshot with a **separate `GIT_INDEX_FILE`**, `git read-tree HEAD`,
`git add` only needed suite and product dependencies, `git write-tree`,
`git commit-tree -p HEAD -F MESSAGE`, then **unset `GIT_INDEX_FILE`** before
`git worktree add --detach /tmp/UNIQUE SHA`. Check the new worktree status; if an
inherited alternate index left all files staged deleted while actual files are
intact, `git -C /tmp/UNIQUE read-tree HEAD` repairs the child index only.
This creates no main-branch commit and never writes the real index. Include
untracked product files, especially `lean-kernel/axiom-audit.ts`; exclude runtime
`lean-kernel/lift*/runs/` artifacts. Upload from that immutable worktree.

For preparation, mount each native `capture.origin` at its `capture.path` using
`--data ORIGIN:PATH` from `lift-regression-inputs.json`:

```sh
supercomputer run --jobs research/bapa/lift-regression-prepare.jobs.json \
  --out /absolute/new/preparation-output --backend boat --strict-once \
  --data /absolute/capsule:release-captures/ID # repeat for 24 native capsules
```

**Only after parent explicitly authorizes final source freeze**, take a new
snapshot containing all 27 reviewed fixtures and a fully frozen manifest. Mount
all 27 accepted capsules. Run:

```sh
supercomputer run --jobs research/bapa/lift-regression.jobs.json \
  --out /absolute/new/native-output --backend boat --strict-once \
  --env LIFT_REGRESSION_SNAPSHOT=EXACT_40_HEX_SNAPSHOT \
  --data /absolute/capsule:release-captures/ID # repeat for all 27
bun research/bapa/lift-regression-report.ts /absolute/new/native-output
```

One bounded supercomputer waiter; never launch a second collector for the same
batch. Preserve failed admission receipts; infrastructure preflight refusal is
not a native attempt or LOST result. Stop only the exact owned PID if necessary.
Clean detached temporary worktrees after completion, not during upload.

## Receipt boundaries

`LIFT-REGRESSION.json` binds source/capsule bytes, fixture manifest, complete emitted
file map, emission JSON, exact native command arguments/exits, stdout/stderr hashes,
and content-hashed uploaded core/kernel/lean-kernel implementation plus the suite
TS/JSON files (excluding runs/). Each command is
bounded with a 32 MiB per-stream cap (overflow fails) and exact-child PID kill on
deadline. No reused compiled cache is accepted; generated `.lake` is deleted after
checking, while sources and logs remain. The snapshot field is explicitly a
**claimed** snapshot; actual cross-job equality uses implementation content hashes
and the supercomputer upload receipt, not faith in an environment variable.

`SOURCE_CHECKED` requires native success, all source laws, exact historical
source/family names and axiom sets, and unchanged bytes after execution. Missing
or changed standard axioms also fail; native compiler axioms and sorry fail.
Partial output is evidence of a failure, never acceptance.
