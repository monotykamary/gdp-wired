# The full release gate

The quick CI shards (test.yml) are not the release gate. A release needs **every job of `supercomputer/suite.json`**
run once at the exact commit being published, each answering 0 or failing exactly as `known-failures.json` records.
Coverage is derived from the committed suite, never a hard-coded count: adding a job adds a release obligation.

`publish.yml`'s `full-gate` job runs it, in the same workflow run as the publish. The job is only a client, on
GitHub's runner; the suite runs as one supercomputer batch on instabox boxes of gdp-wired's snapshot
(`supercomputer.toml`):

1. `full-suite.ts source` refuses a checkout that is not the run's commit, has a submodule off its gitlink, or has
   any change or untracked file; `identity` then writes `VALIDATION-SOURCE.json` (that commit) at the root, which the
   tree carries in place of `.git` (supercomputer ships no Git administration files).
2. supercomputer 1.0 (`v1.0.1` of github.com/monotykamary/supercomputer, `./install.sh`) and instabox's CLI.
3. `full-suite.ts jobs` writes the batch's jobs file: each suite job with its resources, image and env, its command
   run through `full-suite.ts box NAME`, which on the box installs the pinned dependencies
   (`bun install --frozen-lockfile`, as the release gate always has), runs the job's own command in its cwd under its
   own timeout, records the selected `lean`'s complete output, and writes `.gate/RESULT.json` (exit code, job
   definition hash, batch, failure signature) beside the job's outputs. `full-suite.ts tree` gives the hash
   supercomputer packs this checkout as.
4. `supercomputer run --strict-once` (one attempt, a lost job is not tried again), with the repository secret
   `INSTABOX_API_KEY` in that step's environment only. supercomputer packs the checkout, places the jobs on up to 48
   boxes, fetches every job's log and outputs and their sha256, and writes `batch.json` (the jobs and the log of
   requests its batch rule accepted) and `summary.tsv`.
5. Every box of this run is deleted, whatever happened (an `always()` step, also after a cancel).
6. `full-suite.ts verdict` replays `batch.json`'s log through supercomputer's own batch rule (`src/engine.ts`) and
   passes only when the batch was strict-once, ran this checkout's tree, its jobs are exactly the suite's (each
   through `box`, with its cwd, timeout and image), this is the run's **first attempt**, and every suite job was
   answered once, its result from this batch and the job's current definition, with exit 0 or a match for its
   `known-failures.json` entry (the same definition hash, exit code and failure signature). Its verdict is in the
   job summary; the whole batch (logs, results, outputs) is uploaded as the `full-suite` artifact.
7. `publish` needs `check` (test.yml), `full-gate` and the version check; a dry run (`dry_run`) runs all of it and
   skips only the npm upload.

To try the gate without publishing: Actions → Publish → Run workflow, with "dry_run" ticked (or
`gh workflow run publish.yml --ref BRANCH -f dry_run=true`). A re-run of a failed run is never a release: start a new
run.

## Known failures

`known-failures.json` lists the failures a release accepts, each bound to its job's definition hash
(`job-hash.ts`), its exit code and its failure signature (`known-failures.ts`'s `extractFailureSignature`: the failed
tests and their errors, the complete Lean reports). A changed job, a different exit code, another failed test or one
more diagnostic is not that failure, and refuses the release. Adding an entry is a reviewed change to this file.

## Before this (boat)

Until the move to instabox, the suite ran on boat through the old Python supercomputer, outside any GitHub run, and
publish.yml verified a digest-bound receipt of that run from the `release-receipts` branch. The receipt existed only
because the run happened elsewhere; now the run is a step of the publish workflow itself, and its batch and verdict
are that run's. (instabox's own CI boxes, `runs-on: instabox-*-snapshot-*`, start from a snapshot only in a private
repository, so the suite runs through supercomputer's API client instead.) The receipt runner, worker, contract and
verifier are retired (in git history).
