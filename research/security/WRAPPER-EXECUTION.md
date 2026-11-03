# Owned local wrapper-package execution

This opt-in research probe exercises the separate `gdp-wired-cli` package. It does not change the core, wrapper entrypoint, Action, workflow, shared smoke or prior receipts.

## Exact claim and registry indirection

`packages/cli/bin.js` imports `main` from `gdp-wired/cli`. Its package declares a versioned `gdp-wired` dependency and a TypeScript range. A normal wrapper-only installation can therefore resolve the core through the registry. **That wrapper-only path is not exercised here, and no result is claimed for a released registry artifact.**

The experiment packs the current root package and wrapper separately. An isolated consumer installs both local tarballs, explicitly selects TypeScript 5.9.3, and uses a private npm `gdp-wired` override referencing the consumer's local file dependency. This intentionally forces the core to the local artifact; it is not evidence of unmodified registry installation behavior. The installed lockfile must contain exactly the local root core path and a `file:` resolution to the supplied tarball.

Every installed core/wrapper file must match its respective packed inventory and bytes. The installed wrapper bin symlink is checked. A Node ESM resolution probe from the wrapper directory must resolve `gdp-wired/cli` to that installed local core CLI. An offline `npx --no-install --call` lookup must select that wrapper bin. Actual test commands then use **offline `npx --no-install gdp-wired-cli check`**, not a mock or a direct core invocation.

## TypeScript resolution guard

The Node resolution observation also reads the installed TypeScript package's version. `assertConsumerTypeScript` requires the recorded path to equal the canonical `consumer/node_modules/typescript/lib/typescript.js` path and the recorded version to equal the consumer's exact configured version, currently `5.9.3`. It is checked before every wrapper-case dispatch, not merely printed. A matching version at another path or another version at the correct path is rejected.

Before any positive wrapper case, owned negative controls pass a mismatched path and then a mismatched version (`5.9.2`, which would still satisfy the wrapper's declared range) through the same guarded execution function. They require the specific rejection and unchanged command/dispatch counters at zero wrapper launches. Unit tests separately cover exact matches, alternate paths, alternate versions and both mismatches.

This guard checks the recorded resolution snapshot; it does not reload or hash TypeScript's files on every dispatch. The negative controls change owned in-memory observations, not installed package contents. These are trusted research-runner consistency checks, not source authenticity, lifecycle/freshness, supply-chain security, or whole-tree attestation.

## Source and fixture scope

`wrapper-source-pins.json` carries historical base/tree labels for `2f13504b97cb9a639a27efedb2e1b51aab1e2e3f`. The probe does not query Git HEAD or attest the full source tree. It compares only the eleven file hashes explicitly enumerated in that map before/after execution; changes to unlisted files are not rejected by that check.

`wrapper-owned-fixtures.json` reuses the exact original/repaired `OwnedOrder` and `ReplayOrder` bytes from the existing owned call-order fixture. Their SHA-256 hashes are checked before use. Reusing those source bytes does not retarget the earlier `ce28` runtime packet. The old seven-test suite is not rerun.

The eight wrapper CLI cases are the two existing Action TypeScript fixtures and the original/repaired Java fixture, with security off/on. Candidate-only results must stay exit0; broken stated policies must exit1; repaired Java must prove the same stated policy. Opt-in candidates require review and never become accepted policy automatically. Java results must contain the native reader check marker.

For each security setting, the original wrapper witness is validated as a finite nonempty list of only `arm()`/`hit()` before replay. Existing Java fixture code runs in exact/reordered order on both source versions. Source and driver hashes, entry, empty constructor arguments, policy, ordered calls, exit/signal/error and complete numeric result rows are retained. Missing Java support is a gap, never a native pass. These finite controls are not a general replay guarantee.

## Run and retain evidence

Read `supercomputer --skill` and reconcile owned jobs first, then use a fresh run label:

```sh
supercomputer run --jobs research/security/wrapper-execution.jobs.json \
  --env GDP_WRAPPER_RUN=review-1 --out runs/wrapper-execution/review-1-jobs --class interactive
```

For a focused check of the TypeScript assertion gap, use the separate manifest:

```sh
supercomputer run --jobs research/security/wrapper-typescript-guard.jobs.json \
  --env GDP_WRAPPER_RUN=typescript-review-1 --out runs/typescript-resolution/review-1-jobs --class interactive
```

It selects `--typescript-guard-only`: fresh local packages and TypeScript resolution, the two pre-dispatch negative controls, and four TypeScript wrapper cases (candidate/stated-broken × security off/on). It runs no Java toolchain command or native replay and does not renew the earlier native receipt. The original full-mode manifest remains separate. Unit tests and targeted static checks are included in the focused manifest.

The runtime and targeted-static jobs each retain the existing 4-CPU/8-GiB/600-second bounds. Wrapper CLI budgets are 2,000 ms for TypeScript and 3,000 ms for Java; compile/replay commands are separately bounded. The script supplies a private Node22.14.0 when necessary; it does not change global toolchains or the image. Whole-repository checks and other Node/platform/toolchain versions are not implied by the targeted static check.

`--emit-packet` emits `WRAPPER_PACKET_BEGIN <sha256> <bytes>`, a base64 gzip-tar payload, and `WRAPPER_PACKET_END <sha256> <bytes>`. Both actual tarballs, pack metadata, source copies, executed probe, lockfile, manifests, summaries and raw process streams are included. The final JSON repeats the packet digest and size. A partial summary is not complete evidence.

The standard supercomputer log keeps only a 400KB stdout tail. If the packet exceeds it, use the recorded VM and batch to read **only this owned completed job's** full `~/.sc/b/<batch>/jobs/<job-name>/out` (`wrapper-execution` for full mode, `typescript-guard-runtime` for focused mode) in bounded read-only `boat exec ... dd` ranges while available. Require successful, non-truncated transport receipts. Verify full length, the envelope digest/size, safe relative archive members and absence of links before extracting to a new evidence directory. Never accept a truncated packet, change shared log limits, or restart an unrelated VM. If full output cannot be retained, report that gap.

## Not exercised or claimed

- Wrapper-only registry installation, `npx gdp-wired-cli@<released-version>`, registry default/range resolution, or released core/wrapper behavior.
- GitHub Action/workflow execution, hosted runners, publish/tag/release, third-party targets or external vulnerability reproduction.
- Whole-tree/HEAD provenance, compatibility across all supported engines/toolchains, or validation of arbitrary replay inputs.

Prior packets stay unchanged. This manifest is explicit opt-in research, not a default CI or shared-smoke registration.
