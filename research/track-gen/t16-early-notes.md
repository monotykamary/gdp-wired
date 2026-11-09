# T16 front-loaded bounded seed certification

## Evidence and falsifier

Coupled-map moves passed 73 tests but caught only 4/4/2 original named drops.
All six active walls were below 2 s, and independent replay confirmed all 22
witnesses. This still fails five-of-seven. The separate radius-one diagnostic
showed the second binary and ternary passes expiring in setup before any seed
attempt, so a richer neighborhood cannot help if it never executes.

Run the SAME seed vectors before native compilation. The finite layout,
materialization and vector enumerator are factored out, not independently
reimplemented. The new seed-only helper constructs coordinate suggestions and
never claims exhaustion, completeness or validity. Its callback is responsible
for checking them. It retains the last-eight, 256-attempt and finite-domain
limits, including uniform-map moves when explicitly enabled.

## Trust boundary and accounting

`finiteTinyHoudini` uses the exact same `certify` closure for early suggestions
and ordinary native proposals. That closure rechecks the entire frozen current
round family, declared facts, protected callers and the actual source step.
Source preconditions/facts also gate early suggestions. The family does not
weaken between the early and native phases of one recorded round, preserving
the independent replay contract.

The early phase replaces the late neighborhood phase; it does not get a second
allowance. Native enumeration still follows under the same wall and round cap.
The added `onSeed` receipt is separate from native traversal statistics, and a
bounded seed batch has no `exhausted` field. Defaults and production stay off.

## Validation pending

Run all previous 73 tests plus seven early-phase fixtures: no native compilation
for seed-only suggestions, exact attempt cap, certification before native work,
no duplicate allowance, frozen-family cascade, caller/source-precondition and
unknown-fact rejection, fallback native search, and expired walls. Run complete
TypeScript, type-aware lint and commitlint. Only then submit the same six pilots
against the unchanged five-of-seven / 2 s criterion.
