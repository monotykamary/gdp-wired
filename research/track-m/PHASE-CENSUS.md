# Track M phase census (diagnostic only)

The runner does not introduce a proof strategy, raise a budget, reorder proposals,
or enable an acceptance gate. `install-phase-census.ts` adds timing/capture hooks
only to a disposable Linux snapshot and records before/after SHA-256 hashes.
No instrumented production source is committed.

## Measured phases

All reported phase totals are **exclusive wall milliseconds**:

- `demand`: `demandCountCert`, including its nested proposal generators.
- `proposals`: the existing `certFor` proposal construction, reported separately
  because it also exists on main and is not demand-directed generation.
- `A`: the ceiling/scalar-bound section of `deriveCountClosure`.
- `B`: closure scope/rank setup and closure rounds.
- `C`: numeric-leaf construction and its query/reconstruction, before lifting.
- `kernel`: the ordinary, counted, conditional, and arithmetic checkers; nested
  calls are not double counted and are subtracted from their enclosing phase.
- `search`: ordinary solver/query work outside A/B/C.
- `other`: remaining construction, transport, traversal, and framework work.

A/B inclusive intervals and B round intervals are also retained in the closure
records; they overlap generation/checking and must not be added to the exclusive
totals. Phase-C lifting is in `other`, not silently charged to its query.

## Cut identity and use

A cut ID is local to one law run: `closure-N/cut-M`. Its record includes the
candidate index (null for a scalar cut), instance, guard, and cut. Distinct
conditional instances are counted separately even when their vectors agree.

- **proven**: successfully admitted by the unchanged closure checker.
- **offered**: present as an actual numeric hypothesis in at least one attempted
  Phase-C leaf; this is not a claim of minimal dependency.
- **proofReferenced**: cited by an independently checked numeric proof leaf.
- **coreReferenced**: named by the query's refuted-core hypothesis indices.
- **referenced**: the union of the preceding two dependency sets.

A SAT/unknown attempt with no proof/core has no minimal dependency certificate.
Its supplied cuts remain `offered`, not `proofReferenced`. Full-law checking and
post-run numeric-leaf checking are different verdicts and are reported separately.

All dependency checking and serialization are deferred until **after every law
in a process has run**. Doing them between laws would warm row caches and pollute
the next law's timing. Captured records survive the next recorder reset.
`replay-phase-census.ts` checks the serialized numeric proofs and recomputes their
cut IDs again in a fresh process without the instrumentation.

## Controls

The shell job runs the original five-law focused entry on the candidate, then
uses the shared native `countedAttempts(...).traced(...)` entry on both revisions.
For the native Inv1758 comparison, one-primary and Inv3915 are matched warm-ups.
Each process runs once without hooks and once with hooks on the same exclusive
8-vCPU VM, with identical 5,000-unit/60-second per-law limits and one shared
`withTrees` scope. Controls check verdicts and counted work; wall comparisons
remain single-run diagnostic measurements, not performance acceptance claims.

Main `6a3874d3` has neither `proveFocusedCounts` nor `deriveCountClosure`.
Its A/B/C and demand-directed phases are therefore **not applicable**, not a
zero-cost implementation of the candidate strategy. A native-to-native table is
required for an honest baseline; do not compare its wall to the focused entry
as though those entry points were identical.

Run via `jobs-closure-phase-census.json` with the canonical fixture mounted at
`replay-input` and the checksum-verified main archive at `baseline-input`.
Results belong in `runs/track-m/closure-phase-census-v1/` and `runs/REPORT.md`.
