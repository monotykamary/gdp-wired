# Fresh flags-first validation (conditional evidence only)

- Production candidate: `9124348d5d313ab7e89082b0146a72d6a7c8bf66`.
- Existing batch: `20261110-015518-rcbski`; all five workers complete.
- `verified-results.json`: exact fresh-family hashes, counted costs, both
  phase checks, independent replay records, all three original UNKNOWNs,
  focused test totals and CPU labels.
- `file-collection.json`: SDK row/placement records and raw/compressed hashes.
- `*.log.gz`: complete output, including lossless base64 proof captures.
- `summarize-validation.ts`: artifact-integrity summary, **not a proof verifier
  or a final-gate acceptance checker**. Proof/replay checks ran on the workers.

Reconstruct ignored raw logs from the compressed copies, without replacing
existing files, then reproduce the summary with native file operations:

```sh
for f in runs/mldr-incl-flags-first-v1/*.log.gz; do
  test -e "${f%.gz}" || gzip -dc "$f" > "${f%.gz}"
done
bun runs/mldr-incl-flags-first-v1/summarize-validation.ts \
  runs/mldr-incl-flags-first-v1
```

The ordinary-harness runs remain UNKNOWN. Conditional safety uses the other
generated laws as assumptions; it does not establish those laws or 29/29.
No test/proof workload was resubmitted during collection recovery.
