# Compatible counted API on the common D-admitted tree

**Frozen tested source:** `646811dfbe7ec97729a239012d14593fe92a8503`
(on `claude/mldr-integ`, descended from `be661632`).
**Status:** functional compatibility and no-loss census PASS; the new three-file
admitted clock diff remains **PENDING-D**. No merge to main or push.

## Delivered

- Ported A's raw work vector, complete/step profiles, work ledger, counted clock,
  scoped budget/deadline surface and public `search.work` admission.
- Retained the common prover, rather than restoring A's prover implementation.
  Clock callers use the scoped clock; wall telemetry is suppressed while counted.
- Supplied B's two admitted exporter regression fixtures and their minimal
  count-frame helper dependency; no strategy/route changes were introduced.
- Added three focused compatibility controls plus independent pre-import clock
  tripwires. The census tripwire records violations even if an exception is
  swallowed by search code, and catches captured Date/performance functions.

## Validation on supercomputer

| Check | Result |
|---|---|
| Focused compatibility + frame/CDCL/exporter tests | 20 passed, 95 assertions |
| Full type/lint | zero errors/warnings, 1,770 files |
| Unchanged admitted files plus core/check.ts | 131 exact identities |
| Common prover body | exact after erasing telemetry clock renames |
| CDCL/EPR | exact after erasing clock calls/imports |
| Machine instrumentation | AST erases exactly to the common base |
| Original model source | same `0541fa9436e307a6fb716aa5064637b30b893b79` blob |
| Census | 10 proved+checked, 18 unknown, no lost proofs or new refutations |
| Normal vs independent strict tripwire | all 28 verdicts/raw vectors identical |
| Forbidden Date.now/performance.now reads | zero across all 28 strict cases |
| Independent receipt audit | all 56 hashes, source/profile, root/exclusive ledger and weighted totals pass |
| Commitlint | all four source/control commits and this report's message pass |

The 15M census covers the **28 other originals**, not MLDR. Full per-case units
and exhausted stages are in [CENSUS.md](CENSUS.md). Original logs, compressed
receipt envelopes, validation, commitlint, audit and initial failed controls are
preserved under `results/`. `results/audit.json` is the machine-readable summary.

## Important limit: cooperative budget, not a hard dispatch bound

Preserving the admitted prover body also preserves its coarse polling points.
The requested 15,000,000 units are therefore an admission/result budget, **not a
promise that every operation stops before that count**. Thirteen cases exceed
it by more than 1%; the largest search total is **38,611,286.018** (`lock_server`).
These cases return unknown with `work budget (rule result)`; they are not
accepted as proofs beyond the budget. Five further unknowns stop at small/MBQI
polling boundaries. Both normal and strict executions agree exactly.

This raw API/machine-observation port does not establish complete counting of
all native or checking instructions, calibrate W, fix generation termination,
or add F/B's lifted transport routes. New in-body polling or checker changes
must be separately scoped with D rather than hidden in this clock-only port.

## D review and next ownership

1. **D:** inspect/admit `admitted-clock.patch` (exact SHA in `identity.json`).
   Only `kernel/prove.ts`, `kernel/cdcl.ts`, `kernel/epr.ts` change inside the
   admitted tree; Lean and both checker blobs remain exact.
2. **A/I, with D review:** close coarse budget polling/dispatch overshoot on the
   preserved implementation; do not treat this compatibility pass as hard
   bounded generation or complete metering.
3. **A:** generation termination remains separate.
4. **F/B:** lifted route registration and downstream obligations remain separate.

Reproduce with `candidate/prepare.sh` at the frozen source, stage the base
identity inputs exactly as `verify.ts` expects, and run `checks.jobs.json` then
`census.jobs.json` through supercomputer. `audit.ts OUT LOGS LOGS BASELINE SOURCE`
rechecks every archived envelope; normal/strict logs are distinguished by name.
The baseline summary is `../candidate/results/audit.json`.

Initial failed runs are not discarded: 4e13 had a verifier type guard/test
expectation issue; 9a5a had two lint-only issues; d329 had a standalone audit
closure type-narrowing issue. The runtime port was not altered to bypass them.
All final batches are terminal; no owned process remains. `.reflex-saved/` was
left untouched.
