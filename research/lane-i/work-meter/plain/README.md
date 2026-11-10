# Isolated ordinary work-clock prototype

The audited raw pilot showed that `consensus` is currently a refusal control,
not ordinary solver coverage. Frozen source `41d39043` still contains seven
ordinary DSL wall-clock decisions plus readers in BMC, k-induction and TPA.
This experiment changes those decisions to `searchNow`, which preserves the
legacy wall outside an explicit work scope and reads the shared work clock
inside one. It does not simply delete the safety guard.

Ordinary work still refuses execution by default. It is admitted only with an
explicit complete vector whose eight additional coefficients are strictly
positive. Tests use eight ones solely as fixtures; **no production vector,
calibration, W, performance claim or all-29 qualification is supplied**.

The prototype also avoids debiting EPR twice when it already contributes to
the complete work clock. The legacy separate EPR debit is retained otherwise.
No checker acceptance rule or original protocol source is changed.

`pilot.ts` restores and verifies the exact canonical parent, edits five source
files in a temporary boat directory, runs new clock/cutoff controls and the
existing wall/work controls, then type/lint. It rechecks all source blobs and
only exports a non-admitted patch after success. The first failure is retained.
The working production tree and frozen census input are untouched.

Harness type/lint and commitlint pass (`20261110-212458-uabmnq`, 1,693
files, zero warnings/errors). The prototype passed **22 tests** and type/lint
in `20261110-212430-q24kdg`. Independent roundtrip audit
`20261110-212826-0yywzw` applies its five-file patch to the exact parent tree
`1938f7d70a7ed5fb0369a0e76e2e0c2b5a113131` and checks all 109 source blobs.
Patch SHA-256: `0b81986736b8b20ae97661f4f0ecc377b61d8534a8c935a87aa6b4da9758dfc3`.

The unchanged original `consensus` reaches **47,294 preflight evaluations**,
then returns `unknown` / `work budget (completion)` with `fm = 0`. This is
preflight coverage, not complete ordinary-solver or EPR coverage. No prototype
source is admitted. Additional path coverage, state-machine laws, full
erasure/acceptance checks and CPU comparisons are still required before a new
source can replace `41d39043`.

The auditor's untyped default array sort failed lint in
`20261110-213410-0tn1qx`; an explicit string comparator passes the full
1,695-file tooling recheck. Its independently repeated artifact roundtrip
also passes (`20261110-213829-djrxck`). The intervening wrong-data-alias
failure is retained and is not counted as a successful audit.

## Rebase onto the finite-budget source

`current.jobs.json` selects `PLAIN_PARENT=numeric`: the same five-file
prototype must now start from exact `32a59b2a` / tree
`27b8a07cbd5500c7c7f7549df7d6f15fa41092ab`, preserving its nonfinite-budget
guards and adding the five numeric regressions to the 22 previous controls.
The run `20261110-220932-u5aqln` passed all 27 controls and type/lint.
The original consensus case remains preflight-only (47,294 evaluations,
`fm = 0`). Independent roundtrip audit `20261110-221145-sl6hyo` verifies
all 111 source blobs and only the five intended changed files. The rebased
patch SHA-256 is
`35344c91aa210e57de591bfd0250226aef04a713378cb7c5be865fa3a426a2e9`.
The stricter dual-parent auditor also passes type/lint and commitlint
(1,700 files, zero warnings/errors).
The original-parent mode remains available and unchanged in scope.
No prototype is promoted, no weights are calibrated, and passing these
controls would still not turn preflight-only observations into actual
ordinary-solver or EPR coverage for F4.

`deep/jobs.json` reached actual solver work on the unchanged original consensus
model at its first fixture allowance, 500,000, in `20261110-221416-q6185o`:
**212 FM operations, 14 FM cells, 38 CDCL nodes**, with EPR still zero. The
result is `unknown: work budget (completion)`. No larger allowance was attempted.
Global wall-clock and unseeded-random reads were forbidden during the scoped
attempt. All 111 source blobs of the exact audited prototype were unchanged.
This establishes solver entry, not complete ordinary/EPR coverage or calibrated
weights/W. The allowance is not a measured consumed-work total. Process timeout
or crash is infrastructure failure, never an unknown proof result.
Deep-probe tooling and commitlint pass `20261110-221416-p759n4`
(1,701 files, zero warnings/errors).
