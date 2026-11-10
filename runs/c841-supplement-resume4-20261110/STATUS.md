# c841 supplement — native execution complete, verification pending

This is a bounded receipt inventory, **not GATE GREEN** and not permission to submit more work. The coordinator's submission hold remains in effect.

## Completed pre-hold execution

- Batch: `20261110-131934-rcevew`.
- Local task: `db17dfdd-b8f0-4fda-9835-e711e3e723d9`; exited 0 after approximately 1,717 seconds. No replacement was submitted.
- Requested code/test candidate, as recorded in the input `main.sha`: `c8411149d2c6c3c060a0665a79f10523b1281cbc`. Per-job embedded source identity still requires the semantic verifier.
- Native `summary.tsv`: 39 rows, all with exit code 0 and backend `boat`: four mutant jobs, generator/roster/P2, private-law replay, build/exports/original-runtime, and 32 fuzz shards (eight each for seeds 0, 1, 31 and 4294967295).
- All 39 corresponding local log files are present and nonempty. This is a file inventory only, not verification of their embedded receipts.
- Native backend metadata: 1,716.0 s wall time, 1,797.7 s reported job time, 39 Boat jobs, no fallbacks, three VMs and four starts. The client reported closing the completed batch.
- Native timing output reports each job alone, zero co-tenants, four of eight vCPUs pinned, on AMD EPYC 4585PX / AMD Ryzen 9 9950X large VMs. These are recorded observations, not an accepted canonical performance result; the competing-scheduler provenance issue remains separate.

## Deferred checks — do not submit until coordinator's go

The prepared `current-verify.sh` must run the positive `e0-verify.ts` collector and all four `verify-negative-controls.ts` checks on Boat after the hold. Expected checks include exact per-job source identity; archive integrity and cardinality; all 1,664 fuzz cases and outcomes; 26 mutant kills and restoration; 20 private laws and 212 native rows; and rejection of missing, duplicate, non-Boat or failed job rows. These counts are **required verifier expectations**, not claims established by this note.

The independent Lane D canonical gate/bar, final release-tip package checks, and privacy approval remain outstanding. Package-smoke task `c1ceb05f-b56b-4a16-86e9-4b2df86e4ce7` subsequently failed (native job exit 1 despite client exit 0); see `runs/c841-package-smoke-resume4-20261110/STATUS.md` for the separate failure and unvalidated smoke repair. No verifier job, retry, new waiter, scheduler change, credential change, push, tag or publish was started while collecting this receipt.

## Local native-metadata integrity

Raw logs and native metadata remain local ignored artifacts pending privacy disposition. This bounded note does not add them to public-bound history.

| File | SHA-256 |
|---|---|
| `summary.tsv` | `79f3ab33576ff47997a195f11a5055df22e93d20e222241b35fb0055780189cd` |
| `placement.json` | `7eb18f1be78c8d575b25a4023629abd8e5089129271e6fa1f5430af1c152cbdf` |
| `backends.json` | `5b3696b01360a434109020cae5ce57e792528027d52b2cbb7de25c7f984bfaa7` |
