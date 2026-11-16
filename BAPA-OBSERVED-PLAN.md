# Timeout-safe observed retry — Main-authorized

Main's instruction after `20261114-061315-5b3n2y`: retain progress even on timeout, set an internal budget below the job timeout, then ask Fable to read the actual evidence. No next whole-port run before the observer/budget controls pass.

## Isolation

- The strategy `ae288532a` stays the reviewed baseline. The only proposed shared-module delta is a read-only `functionInstanceProgress()` snapshot and an observational cumulative candidate count. No candidate choice, limit, obligation, checker or Lean rule changes.
- Use an isolated research worker and a separate parent timer, not `setInterval` on the blocked proof thread. The parent synchronously appends `progress.jsonl` at start, every ten seconds, and after joining. The worker writes `worker-report.json`; the parent always writes `proof-report.json`, including worker error/backup-stop non-verdicts.
- Use existing `withWorkAdmissionTrace`, existing `withBudget`, `setProveDump` and `profile` hooks. Do not merge f81c or alter its unrelated production paths. The child alone enables `GDP_WORK_FULL=1` to expose the existing metered-site trace. This is a raw-work diagnostic fixture, not a calibrated/canonical measurement or a parity claim against the unmetered attempt. Trace overhead is included.

## Limits and metrics

- Existing root budget: 1,000,000 raw-work-v1 units. Cooperative own wall budget: 180 seconds, checked on metered events; it yields an explicitly labeled unknown/budget report, never a refutation. Parent backup: 240 seconds. Outer job: 600 seconds. Backup termination is a fallback non-verdict, not a successful normal budget return.
- Every ten seconds: last metered site (phase), most recent root goal/hypothesis count, cumulative candidates admitted across discovery calls, Cartesian/matched/total instances generated, function-search work, raw-work floor, solver calls, search nodes, and age of the last checkpoint.
- `kernelCalls` counts the existing metered `kernel choiceFree`, `linear`, `termId`, `truth`, and `facts` entry sites only. Its coverage label is in **every row**. It is not falsely described as every checker invocation. `kernelCheckSteps` is a separate exact work counter. No trustworthy all-checker call counter exists at this pin without additional instrumentation.
- Site and goal messages are observational. The terminal worker report also retains per-site start-event counts and primitive amounts (not phase wall time). No progress quantity can establish a proof. The final original-machine certificate check remains necessary; helper labels remain GIVEN and the port remains unaccepted until its full source wrapper and ghost elimination are checked.

## Pre-run controls

1. Original 15 instantiation controls remain green.
2. Observed unseeded minimal case returns proven/checked with durable progress and no observer failures.
3. Tiny own work budget returns a retained work-budget report without the parent backup.
4. Tiny own wall budget returns a retained wall-budget report without the parent backup.
5. Strict TypeScript, scoped type-aware lint and commitlint.
6. Per Main’s standing smoke rule, execute `scripts/bapa-rigid-observed.sh` itself end to end with `BAPA_OBSERVED_MODEL=minimal`, including the actual CLI, worker, periodic files and final report. No static-only launch gate.

## Verified smoke before the full attempt

- Initial observer gate `20261114-062525-6m2cmv` is retained: the minimal proof itself completed, but a mistaken `ExactRaw.num/den` lookup caused observer errors, and strict typing caught that plus research-driver typing mistakes. No full-port run used that observer.
- Corrected actual-worker gate `20261114-062808-7qemyv`: 19 tests passed, own-work and own-wall reports returned without the backup, and the exact launch script/worker completed the minimal proof with a checked certificate.
- Final source/metric-boundary gate `20261114-062847-i89sny`: 19 tests, strict TypeScript, type-aware lint, commitlint and the actual worker-path minimal smoke passed. Exact five-entry kernel-call coverage is checked against the retained site totals; observer failures zero. Evidence: `runs/bapa-observed-gate-03-fetch/observed-proof-gate.files/`.

The one observable whole-port attempt is now terminal: `20261114-062935-4bfabp` returned a retained own-work-budget report after 38.608 s of observed parent elapsed time (worker native duration 39.59 s); no supervisor backup or job timeout. It did not prove the port. Exact evidence and the Fable/t2 review request are in `BAPA-FABLE-PROGRESS-REQUEST.md`. No further search change, canonical packet or trusted-kernel/Lean change is included.
