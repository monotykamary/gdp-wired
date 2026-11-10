# Preliminary raw determinism census

The source is frozen at `41d39043a75e279dc9600e6a33c8107014b67025`, patch
SHA-256 `f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0`.
Each job restores and checks every source blob, then runs two **fresh Bun
processes** over the unchanged original model. No Node bundle, profiler,
hand-written helper, production seed override or calibrated weight vector is
injected. All exclusive phase raw deltas must reconcile and remain nonnegative.

`pilot.jobs.json`: ordinary (`consensus`), EPR (`consensus_epr`) and counted
(`mldr`) paths, each on `default` and `large` VMs. Actual CPU model, architecture,
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
and expand only after the method passes. Preserve every first failure. This
pilot does not resolve the outstanding Bun F3 capability limitation.

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

