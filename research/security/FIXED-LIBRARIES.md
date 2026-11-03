# Fixed-library reader cohort

`fixed-library-catalog.json` preserves 16 fixed-version advisory entries from 10 libraries,
with 25 exact source pins. `fixed-library-policies.json` selects an entry and method(s)
and records source-intent notes. These notes are not encoded or proven policies.

This is **not a paired security-recall benchmark**. No vulnerable version is run by
`evaluate-fixed.ts`; proposals and security-law search are disabled. A successful job may
be a reader refusal. Only explicit conformance evidence is counted as read-and-checked;
an error or missing conformance is not a pass. Neither outcome certifies a fixed library
safe. The separate published/training corpus and its denominator are unchanged.

On Boat, after `bun install --frozen-lockfile`, run:

```sh
bun research/security/evaluate-fixed.ts <GHSA-id>
```

Each run fetches only the pinned fixed Git object into a temporary checkout, verifies
source hashes before and after reading, checks tracked files were not modified, emits a
bounded gzip/base64 receipt, then removes the checkout. Annotated tags retain both the
original object ID and the resolved commit ID. It installs no upstream dependencies,
adds no permissive stubs and touches no deployment.

Save the logs under `runs/`, then collect with:

```sh
bun research/security/collect-fixed-evaluation.ts --frontend-revision <base-commit> \
  --out runs/fixed-reader/report runs/fixed-reader/logs
```

Record any uncommitted reader patch/tree identity separately with the run. The supplied
base-commit argument is provenance, not an attestation of the executed snapshot. The
collector requires every cohort ID, exact target/revision/source matches and consistent
status evidence. It rejects duplicate entries within a phase; later phase directories
may supersede earlier attempts while retaining their history. `strictRecall` remains
`null`, not `0/16`. Runtime evidence for resumed development is kept under
`runs/sec-resume/`, not inferred from historical cancelled bars.
