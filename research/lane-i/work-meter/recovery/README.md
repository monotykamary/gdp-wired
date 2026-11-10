# Resume recovery — retained constructor source

The pause artifact is immutable: `runs/lane-i/complete-artifact/complete-ast-artifact.log`.
`materialize.ts` reconstructs only that artifact, verifies all chunks and its
SHA-256, restores the exact baseline and both submodules, applies the patch,
and compares every constructor before/after blob and all other candidate blobs.
It also refuses unbound modified/new files and checks the original-model blob.
No constructor generator is invoked.

Verified on boat: `runs/lane-i/resume-artifact-verify/`, batch
`20261110-201003-umjycw`, job exit 0. This is artifact integrity, not a source
check or complete-accounting claim.

The old `/private/tmp` dependencies did not survive migration and could not be
found on Reflex home. One replacement object cache lives at
`~/.cache/gdp-archives/b11e1f65-a8bbe098`; ignored `*.pack` here are hard links,
not duplicate copies. `manifest.json` binds Git roots, trees and submodules.
The helper is the read-only lane-D `final-gate-common.ts` restoration code;
`driver/resource-run.ts` is the unchanged retained resource runner.

Remote data destinations: this directory as `recovery-input`, original
complete input as `complete-input`, artifact log directory as `artifact-input`,
generator tools as `generator-input`, validation tools as `validation-input`.
`validation/prepare.ts` materializes the verified source on each VM before
running the originally prepared four validation jobs.
