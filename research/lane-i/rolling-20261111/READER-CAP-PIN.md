# Isolated reader-cap checkpoint for lane D

This commit is on the committed B/K3/A integration (23f74e5c, followed only by
Q1 evidence738789be). Separately staged F runtime changes are NOT part of it.

Only kernel/reader.ts changes at runtime: two imports and seven checks guarded
by completeWorkProfile.enabled, before value/decision/expression/condition/fact/
form/sync work. The predicate is checkWorkEndpoint, not a local-deadline check.
Removing exactly those9 added lines reproduces blob
9a6f5546f979a0085989dcffc57fc5ab9419a06f; patched blob is
b41b0643484bf37b315f0fb9d9920c58f49aabf1. No decoding logic changes.

The native TypeScript-AST runtime-import audit shows checkMC/checkCountedLaws
closure exactly kernel/kernel.ts and core/{check,meter,work-profile,solver,q}.
Reader and prover are not reachable; type-only edges are reported separately.
Checker, raw observer, work-price and Lean files are unchanged. Run
research/lane-i/rolling-20261111/checker-import-audit.ts to reproduce the graph.

Three direct controls (GDP_WORK_FULL=1) cover root exhaustion before work
mutation, no promotion of a local deadline to root expiry, and restoration
on exceptional unwind. They passed with the same reader bytes in the staged
combined tree; fresh isolated-commit gates are being recorded separately.

A staged-F-only diagnostic exposed the original gap: W500000 spent504211.944.
The patched same fixture stops at500073.083; W5M checks its complete proof at
1579282.7335 with observer/no-observer proof and raw identity, zero clock reads.
These F-fixture numbers are NOT a performance/calibration gate for this
isolated without-F pin. Native/default/W re-gates and D review remain required.

Suggested calibration manifest: GDP_WORK_FULL=1 GDP_WORK_STEPS=0
GDP_COUNT_FRAMES=1 GDP_COUNT_REJECTIONS=1 GDP_COUNT_STRATEGIES=1
GDP_COUNT_TIERS=1 GDP_REQUEST_QUOTIENT=1 GDP_COUNT_ROW_DEFER_CHECKS=1.
This preserves lane A's T220 eight flags. All F flags remain unset. No weight
or allowance change is implied. In particular this pin does not fix the newly
reported Inv* dispatch/subbudget issue, which is being investigated separately.
