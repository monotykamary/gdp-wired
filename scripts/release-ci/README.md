# Reconstructing the 0.48.0 CI control inputs

These are coordination helpers, not a new gate and not published package contents. They were recovered after a sandbox reboot removed temporary controls. `setup-b11.sh` and `e0-verify.ts` are byte-for-byte copies of the restored, previously used controls; the collector still requires its positive run and all four negative controls before any supplemental verification claim.

**Boat submissions are on hold until the coordinator explicitly says go.** Local preparation does not lift the hold, repair authentication or grant release admission. Do not invoke the worker scripts locally: they install/build/test. The preparation command below performs only filesystem/Git metadata work and does not contact Boat, npm or a controller.

## Local preparation

From the repository root, with the restored folders under `/tmp`:

```sh
bun scripts/release-ci/prepare.ts \
  /tmp/gdp-ci-resume-inputs \
  /tmp/gdp-ci-0480-control \
  "$(git rev-parse HEAD)" \
  /tmp
```

Use fresh empty destination directories. The script refuses nonempty destinations, mixed vendor revisions, changed retained receipt hashes, misaligned versions and a release snapshot lacking the smoke repair. It creates:

- A baseline archive reconstructed directly from the immutable baseline Git commit, not the restored `main.tar` of another revision.
- `candidate-meta/` for the frozen c841 supplement, and **separate** `release-meta/` for the selected full release SHA. Each contains exact commit objects, expected trees and binary patches. The worker checks all of these and a clean Git status.
- A small, separately committed control repository, with the source-only worker files and a generated source-root hook adapter. No restored Mac path, scheduler implementation or credential is copied.
- One-job `verify.jobs.json` and two-job `package-smoke.jobs.json` (Node 20 and 24); no job is submitted.
- `restoration.json`: snapshot identities, archive/control hashes, retained receipt identities, and absolute local mount paths. This local manifest is not a public artifact or a passing gate receipt.

The Node-major workers use `npm exec --yes --package=node@20` / `node@24` **on the worker**, assert the selected major, then run the complete repaired package smoke. No package or toolchain is installed by local preparation. Runtime validation remains outstanding.

The helper reads restored vendor archives from `gdp-ci-fix-optional/archives/` and vendor commit metadata from `gdp-c841-supplement-meta/`. It does not need the wiped temporary control Git history. It requires the existing ignored c841 receipts beside the committed status/hash notes: preserve these across moves. A Git checkout alone does not contain the raw receipts or private fixtures.

## After explicit coordinator go only

Read the installed `supercomputer --skill` before submission. Confirm that the selected shared controller is reachable with legitimate credentials; do not change its keys, breaker, scheduling estimates or implementation. Use new output directories; do not overwrite the original failed package run or completed supplement.

For both submissions, the common mounts are:

```sh
--data /tmp/gdp-ci-resume-inputs/base-archive:base-archive \
--data /tmp/gdp-ci-fix-optional/archives:source-archives
```

1. First submit the package jobs against `release-meta`:

```sh
SUPERCOMPUTER_CONTROLLER=1 supercomputer --repo /tmp/gdp-ci-0480-control run \
  --jobs /tmp/gdp-ci-resume-inputs/package-smoke.jobs.json \
  --out runs/post-resize-package-REPLACE-WITH-UNIQUE-ID \
  --class gate --backend boat \
  --data /tmp/gdp-ci-resume-inputs/base-archive:base-archive \
  --data /tmp/gdp-ci-fix-optional/archives:source-archives \
  --data /tmp/gdp-ci-resume-inputs/release-meta:release-meta
```

2. Submit the receipt collector against **candidate-meta**, not release-meta:

```sh
SUPERCOMPUTER_CONTROLLER=1 supercomputer --repo /tmp/gdp-ci-0480-control run \
  --jobs /tmp/gdp-ci-resume-inputs/verify.jobs.json \
  --out runs/post-resize-supplement-verify-REPLACE-WITH-UNIQUE-ID \
  --class gate --backend boat \
  --data /tmp/gdp-ci-resume-inputs/base-archive:base-archive \
  --data /tmp/gdp-ci-fix-optional/archives:source-archives \
  --data /tmp/gdp-ci-resume-inputs/candidate-meta:candidate-meta \
  --data "$PWD/runs/c841-supplement-resume4-20261110":current-receipts
```

These commands do not replace Lane D's single canonical gate/bar. Receipt decoding, counts, assertions and negative controls must actually pass; native/client exit codes alone do not establish a verified supplement. Final release-tip/tarball privacy review remains open and is not performed by this preparer. If the source snapshot changes, regenerate into fresh directories before using the package jobs; do not silently reuse the old release patch.
