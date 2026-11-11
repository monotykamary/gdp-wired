# Scoped evaluation admission — measured on boat

## Scope and invariant

The remaining225642713 endpoint result came from ordinary `brokenOf` evaluation
through counts.ts's lazy judge, not a native checker. A disposable first-crossing
stack is retained in runs/lane-i/rolling-final-step-cap-stack. The repair adds a
`withEvaluationAdmission` scope to that single judge boundary. It does not edit
kernel/prove.ts, native checkers, primitive interpreter counters or prices.

Ordinary visits consume a credit block capped at256 raw units; larger individual
counted charges are admitted directly. When remaining work cannot fit a block,
admission is per visit. Raw `evals` still records every executed visit. Credits
are discarded on nested entry, normal exit and exceptional exit; no child or
later scope inherits permission from a previous local/root budget. No allowance
is minted or added to any budget. Full-profile-off takes the original path.

## Exact tested production source

`8ec48490b0ebaa22caf7a2748fb6365d78f47bf8`, on the committed F integration.
Batch `20261111-081613-ffgzc4`, eval-admission-benchmark. The test explicitly
imports withBudget from core/wall.ts and asserts a real admission hook exists.
The first isolated cd8e729e benchmark did not explicitly initialize this hook;
its timing is retained but is not used here.

One VM/process, order baseline,batch,per-node,per-node,batch,baseline; two
observations per mode. Module loading and logging are outside the timer. Each
loop performs1M ordinary evaluation counter visits. The pre-import clock
tripwire is active during work and inactive only around external timing.

| Mode | Mean wall ms /1M visits | Admission calls | Raw eval units |
|---|---:|---:|---:|
| Counter-only baseline |3.7263665|0|1000000|
| Scoped batch |6.5691015|3970|1000000|
| Per-node admission |12.242223|1000000|1000000|

Added wall relative to baseline: batch2.842735ms, per-node8.5158565ms.
Thus batch removes5.6731215ms/1M visits, or66.6183% of the added admission
cost in this microbenchmark. Total measured loop speedup is1.8636x. Admission
calls fall251.889x (3906 full blocks plus64 tail admissions versus1M calls).
**Unit savings are zero:** all three paths retain the same1M raw evaluations
and weighted units; all other raw buckets are asserted unchanged.

These are descriptive two-observation means, not a confidence interval or an
end-to-end prover speed claim. The benchmark's output has no numeric clock-read
counter: the active tripwire throws on a read, and the work completed without
such an exception. Admission bookkeeping remains unpriced; this reduces its
wall overhead rather than claiming extra proof work.

## Original MLDR endpoint receipts

W225000000, current provisional weights; both public results are UNKNOWN.

| Exact combined manifest | Final raw units | Conservative delta from W |
|---|---:|---:|
| T220 eight flags + final STEP proposal flag |224999999|-1|
| Same +3 F flags |225000051|+51|

Both return an explicit unchecked Inv* proposal before the root end. Nine-flag
return consumes125004150.7273 W-relative units, leaving99995849.2727; the F-flag
return consumes125004812.7273, leaving99995187.2727. These use rootEnd900000.052,
not the larger local count-plan end. The F-flag result is within the documented
1024-unit envelope, but is NOT strictly at/below W. Root/preflight accounting
adds its existing small offset; conservative deltas above use reported raw W.

This is a two-manifest/single-original endpoint gate, not the28-original W
campaign and not final calibration approval. Different prices require a new
bound check. A's closing reserve and whole-family online closure remain open.

Raw evidence: results/check-once and runs/lane-i/rolling-check-once-combined.
