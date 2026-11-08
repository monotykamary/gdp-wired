# C33 research only

Exclusive target index: 33. Inputs are the unchanged family fixture and family19 indices. No protocol-specific engine behavior is added.

Scripts:
- `inspect.ts`: inspect original laws and STEP request on boat.
- `probe.ts`: initial three-tuple hypothesis and kind-law repair.
- `minimize.ts`: all single-deletion requests and checked final artifact.
- `check.ts`: fresh zero-search authentication, exact source reconstruction.
- `audit.ts`: import shared `auditSupport` read-only for actual selector; compare same prepareSupport with hand-empty closure.
- `final.ts`: verify original fixture equality, final (not stale pre-closure) encoding, direct proof and lifted minimal proof for all four variants; emit full extra/late tuple ledger.

Example rerun (from repo root):

```sh
supercomputer run --jobs research/track-p/thirtythree/minimize-jobs.json --out runs/track-p-six/thirtythree/minimize-rerun --vm-type large --data runs/track-p-data:research/track-p/input
supercomputer run --jobs research/track-p/thirtythree/audit-jobs.json --out runs/track-p-six/thirtythree/audit-rerun --vm-type large --data runs/track-p-data:research/track-p/input --data runs/track-p-six/thirtythree:research/track-p/thirtythree/evidence
supercomputer run --jobs research/track-p/thirtythree/final-jobs.json --out runs/track-p-six/thirtythree/final-rerun --vm-type large --data runs/track-p-data:research/track-p/input --data runs/track-p-six/thirtythree:research/track-p/thirtythree/evidence --data runs/track-p-gap-source:research/track-p/thirtythree/original
```

`PART` records in logs are 10KB string slices of named JSON evidence files, emitted to avoid long-line truncation while exporting boat artifacts. No benchmark claims: these are non-timing validations. See `runs/track-p-six/thirtythree/REPORT.md` for the checked conclusion and exact evidence inventory.
