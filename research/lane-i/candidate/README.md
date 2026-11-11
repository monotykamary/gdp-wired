# MLDR integration candidate — PENDING-D

Branch: `claude/mldr-candidate`, source checkpoint `db14ee14`.
Pins and conflict decisions: `pins.json`, `ASSEMBLY.md`.
No main merge, push, calibrated W, or soundness-gate claim.

The trusted checking files and complete Lean tree come from the reconciled
B/F overlay. Necessary declared kernel exceptions retain A's counted prover,
raw meter, and work-scope tests. The exact full kernel hash therefore differs;
checking semantics are not silently replaced. Lane D still owns the receipt.

`measure.ts` calls the actual original protocol constructor and original laws,
then public proveRule with a full-work allowance. It captures final checked
verdicts, phase raw/exclusive counters, strategy/tier events, and query outcomes.
No saved target, replayed certificate or changed model is supplied. Source-only
helper proposals do not count as a final proof. Event `units` emitted by old
strategy hooks are normalized clock units (fullRate=250); `atUnits`, searchUnits
and raw ledgers are counted work. None is calibrated W. Telemetry milliseconds
are unavailable inside counted scopes and must not be used as timing results.

Default diagnostic allowance: 15,000,000 units. MLDR also gets 150M and 1.5B
allowance diagnostics to separate preflight exhaustion from proof-leaf gaps.
A and candidate use GDP_WORK_FULL=1, GDP_WORK_STEPS=0, GDP_COUNT_STRATEGIES=1,
GDP_COUNT_TIERS=1 and GDP_COUNT_FRAMES=1, with the frozen all-one extra weights
and historical twelve coefficients. The original constructors/inputs are not
mutated. Baseline A is 5aa76818. This is a paired-budget no-loss census, not a
claim that all 28 are proved or that budgets are reference-host calibrated.

Prepare: `bash research/lane-i/candidate/prepare.sh INPUT SOURCE-PIN`.
Runs use the tiny existing lane-I runner and supercomputer data packs.
`smoke.jobs.json` validates combined code and runs candidate/baseline MLDR plus
candidate consensus. `census.jobs.json` deliberately excludes those duplicate
cases and includes the other 28 originals on both sources. `audit.ts` verifies
receipt hashes, raw-root/exclusive phase equality and weighted totals before
reporting no-loss and MLDR phase/case data. Complete compressed receipts remain
with the audit; failed runs are not erased. See runs/REPORT.md for task IDs.
