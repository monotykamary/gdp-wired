# Owned packed security execution

This is an **opt-in execution probe**, not a new security policy, public replay API, or CI registration. Its pin manifest carries the historical labels `ce28b821285f9aee8f25277c78697426003e923a` (base) and `8fdbaababd8b300c6cd48634dbb06cbb47b786c6` (tree). These labels are copied into the receipt; they are not a check of Git HEAD or an attestation of the whole source tree. Earlier `6f` receipts remain about `6f`.

## File-hash check scope

Before and after the probes, the source-pin check compares SHA-256 hashes for exactly the ten files enumerated in `packaged-source-pins.json`:

- `action.yml`
- `core/cli.ts`
- `core/security.ts`
- `scripts/build.ts`
- `tsconfig.build.json`
- `package.json`
- `.github/fixtures/security-action/candidate.ts`
- `.github/fixtures/security-action/stated-broken.ts`
- `research/security/call-order.test.ts`
- `research/security/score.ts`

A mismatch in an enumerated file is rejected. **Changes to unlisted files are not rejected by this check.** The `base` and `tree` fields are copied historical labels, not verified HEAD or whole-tree identities. Matching these ten hashes does not establish that the complete checkout or all packaged code comes from the labeled commit. The separate package-file comparisons establish equality between the installed files and the packed artifact, not a whole-tree source attestation.

## Run on boat

Read `supercomputer --skill` and reconcile owned jobs first. Use a fresh run label; the job refuses to overwrite its evidence directory:

```sh
supercomputer run --jobs research/security/packaged-execution.jobs.json \
  --env GDP_PACKAGE_RUN=review-1 --out runs/package-execution/review-1-jobs --class interactive
```

The first job builds with the repository's ordinary build, runs `npm pack` (never publish), and installs that local tarball into an empty consumer. It uses a private Node 22.14.0 installation when the boat image's Node is not 22; this does not change the image or global tools. TypeScript 5.9.3 and the normal optional core peer are installed explicitly. The second job type-checks and type-aware-lints only the new probe. A whole-repository `bun run check` additionally needs the existing vendor submodules; this targeted check is not a substitute receipt for it.

Budgets remain finite: each job has 4 CPUs, 8 GiB and 600 seconds; source CLI checks use 2,000 ms (TypeScript) or 3,000 ms (Java), matching the owned controls. Child commands have timeouts. The copied native suite retains all original options, including its smaller internal reader bounds. Public CLI probes use public flags, not a claim of equivalence to those internal options.

`--emit-packet` writes a SHA-256/length-delimited base64 tar archive between `OWNED_PACKAGE_PACKET_BEGIN` and `OWNED_PACKAGE_PACKET_END` in the full job stdout. **The normal supercomputer result retains only the last 400 KB of stdout and 100 KB of stderr; a large packet will not fit. Do not decode or accept that truncated result.** While the recorded VM is available, retrieve only this completed job's full `~/.sc/b/<batch>/jobs/packaged-security/out` through bounded read-only `boat exec <recorded-vm> --timeout 20 --json -- dd ...` ranges. Require each response to have exit 0 and `stdoutTruncated: false`, concatenate the ranges in order, and retain the range receipts. This is observation of an already-owned job, not permission to restart a VM or change shared infrastructure. If full output is unavailable, packet retention remains a gap; do not rerun passing checks merely to hide the missing evidence. Decode it, verify **both** the declared byte length and SHA-256, then retain the archive and extract only its expected relative paths into a new owned receipt directory. It includes the exact npm tarball and pack metadata, all subprocess stdout/stderr, final summary, source copies, original library results, generated test/adapter, and the executed probe source. A status line alone is insufficient evidence. The JSON summary is incomplete until the probe finishes; any skipped native path remains a gap, not a pass.

## Distinct evidence layers

1. **Installed-library native regression suite.** A copy of `research/security/call-order.test.ts` changes exactly two imports: `check` goes through a recording adapter to the installed package's `dist/core/cli.js`; the private scorer stays the pinned source scorer. All seven test bodies and original check options are unchanged. The adapter retains the existing `OwnedOrder`/`ReplayOrder` fixture bytes before the suite removes its temporary files. This is Bun importing the installed library, not a Node CLI or GitHub-runner claim. The suite's private association helpers remain private, trusted fixture labels, not source authenticity or a production receipt interface.
2. **Actual installed CLI processes.** Plain Node executes the installed CLI file on the two owned Action TypeScript fixtures and both original/repaired Java fixtures, with security off and on. Exit status, JSON source path/entry, candidate review labels, stated-law results, unchanged source hashes, and Java reader execution markers are checked. Original and repaired Java cases retain the same stated policy. A deliberately wrong expected source hash must be rejected before any process is launched.
3. **Actual local Action run-step processes.** The existing `action.yml` supplies the selected run text. Its version is a local `file:` tarball; inputs are fixed, simple owned paths and flags. Real `bash` and `npx` run from an isolated fixture repository on Node 22, with a fresh npm cache and no mock executable. Every installed file in both the consumer and Action npm-cache package must equal the tarball's inventory and bytes. Both Action branches are exercised on both TypeScript and both Java fixtures.
4. **Native CLI-witness controls.** For each entrypoint and security setting, the original CLI's exact zero-argument `arm()`/`hit()` witness is validated in full before dispatch. The existing owned driver is compiled and run against original and repaired sources, in exact and reordered order. Only original/exact may violate the unchanged policy. Native process status, signal/error, complete row grammar, safe counts, steps, source/driver bytes, entry, empty constructor arguments, policy and call order are retained. These are finite owned examples, not a general replay guarantee or external vulnerability reproduction.

## Scope exclusions

- Local shell execution does **not** execute GitHub's checkout/setup-node actions, composite condition evaluator, job permissions, or hosted runner environment. The branch conditions are selected from the existing fixed expressions; no arbitrary expression evaluator is added.
- The tarball's package metadata may say `0.46.0`; its evidence is the ten enumerated file-hash checks and tarball hash, **not** a whole-tree source attestation or the released registry artifact. No registry release is fetched as a security target, no tag or publication is changed, and no live workflow is dispatched.
- This probes the root package's `gdp-wired` CLI used by the Action; it does not establish a separate `gdp-wired-cli` wrapper-package receipt.
- The package is exercised on owned fixtures only. Candidate proposals still require review and do not become accepted policies. Same output from different source/order does not establish identity.
- This probe is invoked explicitly through its jobs manifest, not added to the shared smoke, quick suites, workflows, readers, or production exports.
