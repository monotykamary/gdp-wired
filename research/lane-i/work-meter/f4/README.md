# Preliminary raw determinism census

The source is frozen at `41d39043a75e279dc9600e6a33c8107014b67025`, patch
SHA-256 `f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0`.
Each job restores and checks every source blob, then runs two **fresh Bun
processes** over the unchanged original model. No Node bundle, profiler,
hand-written helper, production seed override or calibrated weight vector is
injected. All exclusive phase raw deltas must reconcile and remain nonnegative.

`pilot.jobs.json` selects `consensus`, `consensus_epr` and `mldr`, each on
`default` and `large` VMs. These names alone do not establish path coverage.
Actual CPU model, architecture,
Bun version and affinity are recorded. VM type is not a CPU-model label. The
pair fingerprint covers the original protocol ID, fixed legacy work allowance,
verdict and every raw counter; wall times do not enter it.

The `work` field is the same legacy 15,000,000 **allowance**, not a measured
consumed-unit total and not a selected final W. These preliminary records test
raw invariance; they are not the all-29, cross-CPU calibrated-unit qualification.
Equal raw vectors determine equal projections under a fixed weight vector, but
no new vector is fitted here. The external 30-minute per-process guard is an
infrastructure failure if hit, never an `unknown` proof result.

Audit all six pairs, compare their actual CPU labels and cross-VM fingerprints,
and expand only after the method and intended path coverage pass. Preserve
every first failure. This
pilot does not resolve the outstanding Bun F3 capability limitation.

## Audited partial results and revised placement plan

`20261110-211756-rm4lfj` independently validated the three completed large-VM
pairs, including lossless stdout hashes, source identity and phase sums:

| ID | CPU | Result / coverage |
| --- | --- | --- |
| `consensus` | Ryzen 9 9950X | `unknown`: `work mode: plain-path migration pending`; only 51 AST constructions, no solver work |
| `consensus_epr` | Ryzen 9 9950X | proven and checked; `epr` counter is zero, so this is not evidence of EPR execution |
| `mldr` | EPYC 4585PX | `unknown`: `work budget (completion)`; counted-path work observed |

These are valid raw pairs, **not representative coverage of all three intended
paths**. In particular, the refusal control must not qualify the ordinary path
or be fitted as ordinary solver performance. All-29 qualification stays closed.

The large pool already has two actual CPU models. `cross.jobs.json` therefore
uses `cpu-gate.ts` before restoration or execution: only a CPU different from
that ID's audited first CPU may proceed. Exit 75 is a placement miss with no
solver execution, not an unknown verdict. Keep miss logs and rerun only missing
placements, never successful CPU pairs, with at most three placement attempts
per ID in this pilot. `audit-cross.ts` requires all three
actual CPU differences and preserves the path-coverage limitations.

## Completed cross-CPU diagnostic

Independent audit `20261110-212826-0yywzw` passed all three original IDs on
**both Ryzen 9 9950X and EPYC 4585PX**. Every pair has equal raw counters and
verdicts across CPUs. `consensus` still refuses, `consensus_epr` is checked but
has a zero EPR counter, and `mldr` still stops at the legacy work allowance.
This is a six-pair diagnostic, not all-29 or intended-path qualification.

The cross-placement backend records have empty CPU labels. The auditor
reports this explicitly; it instead requires the gate and both independently
hashed child records to agree on the nonempty CPU. First-placement labels
remain mandatory. Placement fixtures also reject missing/mismatched gates,
same-CPU gates and missing first-placement labels.

The original batch `20261110-205505-uq8edg` had three completed large jobs and
three unstarted default jobs. After preserving its receipts and completing the
CPU-gated comparisons, its exact waiter was stopped and the owned batch was
closed. All three redundant queued jobs were cancelled; no running job was
cancelled and no completed solver pair was rerun for cleanup.

## Receipt validation

`audit.ts` verifies the exact source/patch, lossless child stdout hashes, fixed
legacy allowance and production seed policy, all 20 nonnegative integer raw
counters, exclusive-phase reconciliation, paired verdicts and fingerprints,
and cross-placement agreement. It reports CPU-model diversity separately from
agreement and never equates a VM type with a CPU model. `audit-fixtures.ts`
rejects ten corruptions, including self-consistent transport hashes enclosing
bad semantic fields, and checks that same-CPU aliases do not qualify.

Batch `20261110-210220-pcmupw` passed these fixtures, all prepared commit
messages and type/lint across 1,692 files with zero warnings/errors. This checked
the initial auditor, not the subsequent cross-CPU receipts. The latter have
the independent real-data audit above; additional placement edge cases are
covered by `audit-fixtures.ts`.

## Immutable dispatch

The first dispatch failed during upload because `ledger/state.json` changed;
no census ran. The retry uses `/tmp/lane-i-raw-census-41d39043`, a 25-file
runner/input tree with the same existing image `sc-f0d8daeee6c3`. The three
packed source files total about 147 MB and are copied once, not per job.
No full extra worktree is created. Report edits cannot change these inputs.

`freeze.sh` recreates the snapshot from the archived inputs and the checked-in
runner templates. Its target must be a new absolute directory. Never edit a
snapshot used by an active batch. The tiny runner resolves the existing image
hooks from `source-root.txt`; it does not rebuild or change the image layers.

