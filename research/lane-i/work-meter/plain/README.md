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
files, zero warnings/errors). Current status: experiment running; no
prototype source admitted. Additional
path coverage, state-machine laws, full erasure/acceptance checks and CPU
comparisons are still required before a new source can replace `41d39043`.
