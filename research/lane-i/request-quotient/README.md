# Lane I: request-space quotient

Runtime source: **bfe647cfd3b81e10c497ca4d5911a8097a02586b**.
Parent: `4c1c05dc` (runtime `2de2ce89`), D scoped GREEN for the release integration.
The previous release's accepted nine-case off-counter exception is not reused here.

Enable with `GDP_REQUEST_QUOTIENT=1`. Default behavior is unchanged. The only
runtime/test diff is `core/exists.ts`, `core/request-quotient.ts`, and its test;
`runtime.patch` is the exact diff from `4c1c05dc`. No checker, Lean, interpreter,
production rejection or weight changes.

- [RESULT.md](RESULT.md): qualified measurements and census.
- [SOUNDNESS.md](SOUNDNESS.md): structural argument and exact proof boundary.
- [ReadSet.lean](ReadSet.lean): checked congruence and fresh-key theorems.
- [D-HANDOFF.md](D-HANDOFF.md): review scope and remaining approvals.
- `results/`: byte-exact raw receipts, including failed pilots and failed initial audits.

## Reproduce

Create `port-input/source.tar` with `git archive bfe647cf`. Vendor archives must
contain their `vendor/` paths and match these gitlinks:

- gdp-ts: `0b6ebeeec827b05210f3acfa4149a70dda9a0de5`
- handwired: `d47141cce2caf5b86b0c2c0c372a5174f424bc15`

Copy the chosen drivers from this directory into `port-input`; use
`research/lane-i/merge-0480/driver/measure.ts` and copy that directory's
`census-preload.source` as `port-input/census-preload.ts`. The legacy controls
use its `flags-off-model.ts` and `flags-off-measure.ts`. `source.txt` contains
the full source hash above. The `*-INPUT-SHA256SUMS` files bind executed inputs.
Archives are not committed.

Run `census.jobs.json` through supercomputer: 28 originals, quotient off/on/on
repeat, 15M provisional units and the pre-import clock tripwire. `legacy.jobs.json`
repeats the existing 28 legacy-mode controls (that driver has no clock tripwire).
`audit.ts`, `audit-controls.ts` and `audit-legacy.ts` perform independent checks.

For the final timing, copy `run-ledger-generation.ts` and
`measure-ledger-generation.ts` into the input bundle and run
`timing-9950x.jobs.json` with **`--timing`**. It requires one exclusive xlarge
VM with CPU string `AMD Ryzen 9 9950X 16-Core Processor`. Both sample and full
admission-prefix measurements run off/on/on/off in fresh processes on that
same VM. `audit-ledger-timing.ts` validates placement, order, zero proof queries,
repeated raw vectors and identical outputs. The older `measure-generation.ts`
pilot omits automatic kind laws and is not the final ledger measurement.

`skipped.jobs.json` is Fable Q1: all 28 originals plus MLDR. `audit-skipped.ts`
inserts exactly two observation hooks into a **disposable extracted sampler**,
not the worktree. Every skipped request is interpreted independently and must
be refused or return the representative's same canonical successor. The
logical trial allowance, actual sampler step counter and walks stay unchanged.
This is an unmetered oracle audit, not a timing or 15M-budget run.

`edge-cases.ts` independently exercises arithmetic *inside selector conditions*
and three bulk-write forms, including past-support defaults while an unread
input map adds a far-away key. It complements the source unit tests.

No command here publishes, merges to main, changes a kernel file or regenerates
another lane's certificate corpus.
