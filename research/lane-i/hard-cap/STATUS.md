# Hard-cap follow-up — active

Baseline: 646811df (runtime), 30ed7471 (evidence). Kernel/, Lean and core/check.ts
must remain byte-identical to this baseline. All work on claude/mldr-integ.

Lane A (ic3-gen/t1f) notified through hc before runtime edits: reserved
core/dsl.ts, core/watch.ts, core/machine.ts, core/runtime-wall.ts, core/wall.ts.
Initial falsifiable hypothesis: BudgetExpired from preflight is swallowed by
refuteByRuns because its catch only preserves WallExpired. Later prover work
then spends beyond the endpoint. Quantifier/eval checkpoint spacing may also
be too large. Native baseline probes will identify actual gaps for 13 cases.

Diagnostic-only overlays instrument core/wall.ts and core/work-meter.ts; the
kernel is never patched. No production edits yet. Probe source and records are
not proof authority and must preserve each baseline raw vector/verdict.
