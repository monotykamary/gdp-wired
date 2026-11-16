# Full canonical release gate

The quick CI shards are not the release gate. A release needs a reviewed native
execution of **every job in `supercomputer/suite.json` at the exact final Git
commit**, with all Git submodules provisioned at their gitlink commits. The
current suite has 245 jobs; coverage is derived from the committed suite rather
than a hard-coded count. Adding a job automatically adds a release obligation.

`publish.yml` requires both the usual checks and the external `release-full-gate`
commit status with a committed, digest-bound receipt. No self-hosted runner or
new CI credential is required. CI only reads GitHub with its `GITHUB_TOKEN`.

## Operator run (outside GitHub Actions)

First finish and review the release commit, initialize its submodules, and keep
the checkout clean. Any later source change creates a new candidate: all release
checks must be repeated on that final SHA. Historical results are not carried
forward as evidence for changed source.

Run on an authorized supercomputer controller, after reading
`supercomputer --skill` and obtaining approval to launch the full suite:

```sh
bun run release:full-gate run /tmp/full-gate-input-UNIQUE /tmp/full-gate-output-UNIQUE gate
```

Both paths must be new and separate from the source checkout. The command:

1. Reads the complete canonical suite, commit and tree from a clean checkout.
2. Initializes and verifies submodules, then packs exact Git objects into opaque
   archives. This avoids transport ignore rules dropping C sources or fixtures.
3. Submits the entire suite to Boat with strict-once, one attempt, no fallback
   and no implicit retry. Only the wrapper and provisioning allowance differ
   from the canonical job; the original command, cwd and resource fields are
   retained and bound by a definition digest.
4. Reconstructs and checks Git trees in each worker, installs frozen dependencies,
   and records provisioning and actual command results separately.
5. Pins the image identified by the native results, including after a completed
   failed run so its diagnostic environment is retained.
6. Authenticates native job results, output manifests and bytes, source bindings,
   and identity-bound cleanup before producing `receipt.json`.

The native invocation has a finite six-hour controller wait. A timeout or lost
connection is unresolved, not permission to resubmit. Preserve the native batch
identity and follow the documented custody/recovery procedure.

Separate preparation and finalization are available for inspection/recovery:

```sh
bun run release:full-gate prepare /tmp/full-gate-input-UNIQUE
bun run release:full-gate finalize INPUT RESULTS_JSON IMAGE_PIN_JSON NEW_RECEIPT_JSON
```

Preparation is **not evidence of a run**. Finalization rejects incomplete,
failed, duplicate, mismatched or unclosed native executions. It never starts a
replacement job. It will not overwrite an existing receipt.

## Review and publication

Retain the native `results.json`, custody journals, worker files, input archives,
and raw image pin alongside the receipt. The approving operator must inspect
these; the CI verifier checks the approved receipt, not remote worker logs.
The receipt contains public identifiers and hashes, not logs, credentials,
absolute local paths or private input bytes.

The tested source cannot contain a receipt referring to its own commit SHA.
Commit the reviewed receipt separately on the repository's `release-receipts`
branch at:

```text
full-gate/<FULL_TESTED_COMMIT_SHA>.json
```

Use a separate worktree and an ordinary new commit (`git commit -F MESSAGE_FILE`).
Do not merge the receipt branch into the tested source and do not rewrite either
history. The source commit/tree, suite bytes and every job definition must match
exactly; partial or count-only coverage does not pass.

Only after reviewing the native evidence, clearing any release HOLD, and pushing
the receipt branch does the authorized Main operator publish the status. The
runner writes a `status-payload.json` with `context: release-full-gate`,
`state: success` and `description: receipt-sha256:<SHA256_OF_EXACT_RECEIPT_BYTES>`.
For example, the operator can use a file-backed API request:

```sh
gh api --method POST "repos/OWNER/REPOSITORY/statuses/$TESTED_SHA" --input "$OUTPUT/status-payload.json"
```

The runner never pushes, publishes or calls a GitHub write API. Publishing checks
that the latest status is successful on the resolved source commit and names
these exact receipt bytes. Missing, pending, failed, ambiguous, truncated or
wrong-SHA responses fail closed. The committed receipt must additionally cover
all canonical jobs, source/submodule identities, protected images and successful
single-attempt execution records. Already-published skip behavior is unchanged.

## Loss and independent reproduction

An original `LOST` record remains `LOST`, including its actual cleanup state.
A user-authorized, separately labelled `<job>-repro-N` may establish that job's
outcome at the same source and definition, but never rewrites the original or
counts as an automatic retry. The contract supports this diagnostic record and
explicitly reports any open original custody. A failed reproduction is still a
failure. The fresh full-suite runner does not silently merge reproductions or
issue an approved release status. Main must retain the evidence and enforce any
HOLD; unknown custody must never be reported as completed cleanup.
