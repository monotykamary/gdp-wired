# The full release gate

The quick CI shards (test.yml) are not the release gate. A release needs **every job of `supercomputer/suite.json`**
run once at the exact commit being published, each passing or failing exactly as `known-failures.json` records.
Coverage is derived from the committed suite, never a hard-coded count: adding a job adds a release obligation.

`publish.yml` runs it, in the same workflow run as the publish, on instabox CI boxes:

1. `suite-matrix` reads the suite (`bun scripts/release-ci/full-suite.ts matrix`): one entry per job, with the box its
   image runs on (`instabox-large-snapshot-<snapshot>`, the snapshot `supercomputer.toml` names for the job's image).
2. `full-suite` runs each entry on a fresh box of that snapshot (`fail-fast: false`, so every job runs): the checkout
   at the run's commit with every submodule at its gitlink, `bun install --frozen-lockfile`, then
   `full-suite.ts run NAME`, which refuses a checkout that is another commit, has a submodule off its gitlink or has
   changes, and runs the job as supercomputer would: `bash -c "<[run] pre><cmd>"` in its cwd, under its timeout, with
   its image's PATH and env and its own env, and `$SUPERCOMPUTER_OUTPUT_DIR`. Each job uploads its `RESULT.json`
   (exit code, definition hash, commit, run attempt, the failure signature when it failed), its full logs, its
   complete Lean diagnostics and its output files as an artifact.
3. `full-gate` (`full-suite.ts gate`) passes only when every suite job has a result from this commit and this run's
   **first attempt**, from the job's current definition, and each one exited 0 or matches a `known-failures.json`
   entry (the same definition hash, exit code and failure signature). A re-run attempt never passes the gate, so a
   failing job cannot be retried into a release. Its verdict is in the job summary.
4. `publish` needs `check` (test.yml), `full-gate` and the version check; a dry run (`dry_run`) runs all of it and
   skips only the npm upload.

To try the gate without publishing: Actions → Publish → Run workflow, with "dry_run" ticked (or
`gh workflow run publish.yml --ref BRANCH -f dry_run=true`).

## Known failures

`known-failures.json` lists the failures a release accepts, each bound to its job's definition hash
(`job-hash.ts`), its exit code and its failure signature (`known-failures.ts`'s `extractFailureSignature`: the failed
tests and their errors, the complete Lean reports). A changed job, a different exit code, another failed test or one
more diagnostic is not that failure, and refuses the release. Adding an entry is a reviewed change to this file.

## Before this (boat)

Until the move to instabox, the suite ran outside GitHub on boat through the old Python supercomputer, and publish.yml
verified a digest-bound receipt of that run from the `release-receipts` branch. The receipt existed only because the
run happened elsewhere; with instabox's CI boxes the run is a part of the publish workflow itself, and GitHub's own job
results at the commit are the evidence. The receipt runner, worker, contract and verifier are retired (in git history).
