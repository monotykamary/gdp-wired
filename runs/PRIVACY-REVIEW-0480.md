# 0.48.0 privacy review — OPEN, not clean

The review is separate from proof/test admission. No push, tag or publish is authorized. Do not publish internal evidence or treat scanner exit 0 as a clean result.

## Exact scope and execution

- `origin/main` = `40693c7a2e9adcae77c6558dedb8278bd5704ce7`.
- Local baseline `main` = `b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3`.
- Code/test candidate = `c8411149d2c6c3c060a0665a79f10523b1281cbc`.
- Additions in both `origin/main..main` and `main..candidate`, plus candidate tracked path names, were scanned on Boat. The release-prep commit and final tarballs need a fresh scan after submission is permitted again.
- Scanner batch `20261110-131934-17oc5m`, worker `bx_4zdy5q97`, native exit 0.
- Independent summary batch `20261110-132112-1mdy8l`, worker `bx_ac4jda5u`, native exit 0. The ordinary collector wrote an **empty summary log**; the retained worker stdout (6,051 bytes) was fetched separately as `runs/c841-privacy-summary-resume4-20261110/privacy-summary.recovered.log`. The empty original remains. No result was inferred from the exit code alone.
- Integrity SHA-256: raw scanner receipt `3297d0e00d365b4a5e7e84b9c55973ff65096d8a8fb626d8a2dce7e3ffcc97be`; empty original summary `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`; separately recovered summary `1e1b025fddd2b7d49f63f3c0bb1a43367e1c92c8d6ad4b883cd4cdfe6668c2aa`.

Raw scanner receipts and the recovered summary remain local, ignored artifacts pending the privacy/history decision; this report records bounded counts and integrity hashes only.

## Findings

| Boundary | Added lines | Flags | Classification counts |
|---|---:|---:|---|
| origin/main..main | 102,856 | 65 | 57 temporary-artifact references, 7 absolute user paths, 1 private path |
| main..c841 candidate | 17,844 | 1,648 | 1,623 temporary-artifact references, 1 absolute user path, 2 private paths, 22 private-fixture labels |

No tracked private-directory filename was reported. No credential-shaped token, private-key header, URL-query credential or held-disclosure marker was reported by this detector. This is **not a general secret audit** and is not evidence that undiscovered credentials or client names are absent. Explicit client-name review is still incomplete.

Most flags are internal temporary paths in research scripts and recorded diagnostic logs, not runtime package code. They require triage, not a blanket assertion that all 1,713 flags are secrets. The candidate's flagged files are confined to tracked `runs/` artifacts; the baseline also has research scripts, fixture metadata and a tsconfig reference. Full filename inventory is retained in the recovered summary; matched source text is deliberately not printed by the scan.

## Required disposition before any push

1. Review absolute user paths and private references. Do not ship private client identities or held disclosure material in public source/history.
2. Keep exact original receipts and their hashes in private storage. Never edit a raw receipt and continue to call it byte-exact evidence. Do not silently delete failures or rewrite history.
3. Coordinator must choose the authorized public integration/history boundary for internal evidence. Removing a path in a later commit alone does not remove it from earlier commits that would be pushed. No history rewrite or public-branch cleanup has been performed here.
4. Review client identifiers independently of the detector's generic fixture-label patterns. Fixture labels are not themselves proof of client-name exposure, nor a substitute for that review.
5. Re-scan the actual release tip and both npm tarballs after the gate, package validation and authorized privacy disposition. The package allowlists currently contain `dist`, README and LICENSE for the library and `bin.js` for the CLI; the broad Git-history review remains required even if tarballs exclude `runs/`.

## Public release wording

The prepared 0.48.0 changelog intentionally stays generic: source translation is cross-checked against native execution by default; unchecked laws exit 2. It includes no new advisory name, affected release range, private client name or reproduction detail.
