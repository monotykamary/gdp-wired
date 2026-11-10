# Optional research-path portability scrub

This changeset removes machine-specific locations from the seven added home-path lines and nine temporary-directory lines in the original remote-main to local-main delta. It is an optional tree-only change on the prepared release snapshot, not a decision to publish research and not a history rewrite.

## Replacement locations

- Paxos runner/data: `./inputs/paxos-runner` and `./inputs/paxos-data`, overridable with `PAXOS_RUNNER` and `PAXOS_DATA`. Keep the original frozen contents; only locations change.
- Row-guard inputs: `inputs/mldr-rows/` at the checkout root, with `input`, `frozen`, `preflight`, `demand`, `flags`, `early`, and `guard` subdirectories. `INV1758_ARTIFACTS` overrides the root; the existing input/frozen variables and new per-directory variables override individual locations. Input hashes, job specs, backend/class/timing flags and mount aliases are unchanged.
- Section 10/11 chunk jobs: prepare or mount the corresponding original packets as `./section10-receipts` and `./section11-receipts` in the worker working directory. Section 10 cleanup is likewise relative; it no longer removes an absolute home-directory location. These jobs no longer implicitly locate one historical VM's packet.
- The scheduling fixture's `stage` is `.` relative to its input bundle. This is a redacted location label: the public JSON is no longer byte-identical to the historical metadata. Configuration, content hashes, manifest digest and every other field are unchanged. The audit checks those bindings, not the absolute staging path. The original remains available from the parent commit.

## Intentionally retained

`tsconfig.json` still excludes the private source directory. This is the one remaining targeted directory reference. Removing it would expand typechecking to unpublished sources; disguising its spelling would not be meaningful privacy remediation. Keep the boundary unless the directory's publication/layout policy is deliberately changed.

## Limits

The scope is the specified original-main delta, not all historical paths or current research artifacts. Git history, captured logs and original receipt hashes are not rewritten. Whether research is published remains a separate decision. No proof semantics, budgets, job resources or scoring are changed. No Boat job is run by this scrub.
