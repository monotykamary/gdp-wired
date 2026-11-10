# 0.48.0 release preflight — not admitted for release

Exact code/test candidate: `c8411149d2c6c3c060a0665a79f10523b1281cbc`.
Required gate baseline: `b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3`.

**No GATE GREEN receipt exists yet.** Versions remain 0.47.0. No push, tag, publish or GitHub write is authorized. Do not treat this checklist or lane-local checks as release admission.

## After Lane D's exact-SHA GATE GREEN

1. Run `bun scripts/version.ts 0.48.0`: updates root version, CLI package version and CLI dependency on gdp-wired together. Verify all three; keep lockfile consistent.
2. Retitle the unreleased changelog section and keep the soundness wording generic: **source translation is cross-checked against native execution by default; unchecked laws exit 2**. Do not include advisory names, affected ranges, private clients or reproduction details. Preserve accurate public API/migration information.
3. Clear the release-boundary privacy review for `origin/main..main` and `main..candidate`, then scan the actual release commit and packed files again. Automated diff scanning is only a first pass: private paths, user paths, credentials, held-disclosure markers and fixture labels are checked without printing matched contents. Client-name review remains a separate required check.
4. Run package/export/version checks, build, pack and consumer smoke tests on Boat. Commit on this branch. Coordinator alone pushes after the user's go.

## What `.github/workflows/publish.yml` will run

- Trigger: pushes to **main** touching either package manifest, or manual dispatch. Optional manual `dry_run`; concurrency group `publish`, no cancellation of an in-progress publish.
- Ubuntu **24.04**, Node **24**: check npm for both exact package versions. Already-published versions are skipped; dry-run forces validation without upload.
- Before packaging, call `.github/workflows/test.yml`: frozen Bun install, typecheck/lint, **seven canonical quick-test shards**, plus package consumer smoke tests on Node **20 and 24**.
- Checkout with recursive submodules; install Bun dependencies with `--frozen-lockfile`; execute `prepublishOnly` (`bun scripts/build.ts`); pack both library and CLI with Bun.
- Smoke-test both tarballs with `scripts/smoke.sh` (runtime and TypeScript consumer checks).
- Install current npm; list tarball contents; publish only missing versions, library first then CLI, with `npm publish --access public --provenance` using GitHub OIDC trusted publishing. Dry-run prints but never uploads.
- Workflow timeouts: release discovery 5 minutes, reusable checks 15/20 minutes, publishing 20 minutes. Neither this workflow nor this checklist replaces the independent release gate.
- Publishing advisories (staged-version 409, OTP/2FA notice, empty `/-/stage`) mean pending; do not bump, retag or retry to bypass them.

## Retained blocked attempts (cancelled before worker placement)

- 39-job exact-candidate supplement: `runs/c841-supplement-resume-20261110/`, batch `20261110-130346-vvxxgb`.
- Immutable canonical plan worker: `runs/c841-canonical-resume-20261110/plan/`; full checks depend on its validated roster.
- Read-only privacy boundary scan: `runs/c841-privacy-resume-20261110/`; a clean automated result alone does not clear client-name review.
