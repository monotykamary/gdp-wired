# Search budgets and interruption results

Explicit counted work is opt-in. This page describes the API contract, not a guarantee that every proof family supports it or that a chosen allowance will finish a proof.

## Counted work is not elapsed time

The explicit `work` option bounds instrumented search work. It is not milliseconds and must not be calculated by multiplying an old `ms` value. For fixed code, inputs and options, a slower worker or a pause does not grant less search work. Work accounting can change between versions; retain the version and measurement used to choose a cap.

```ts
const verdict = proveRule(rule, laws, {
  search: {work: 1_000_000}, // example allowance, not a universal recommended cap
})
```

`proveSteps` uses the same `search.work` option. Standalone `inferLaws` takes `{work, watchdogMs}` in its options. Standalone `discover(rule, laws, stepLaws, first, options)` accepts `{work, watchdogMs}` in the optional fifth argument; its search result and interruption fields are in `result.verdict`. The watchdog bounds the whole discovery request, not a fresh duration per candidate or round. These are explicit opt-ins; legacy `ms` calls retain their compatibility behavior and are not a promise of wall-clock-independent completion. Do not combine explicit `ms` and `work` grants. Unsupported work-mode families must refuse honestly rather than silently use a millisecond budget.

Measure a representative successful search, preserve its checked result and work measurements, then choose and test a work margin. Increasing a cap does not fix an incorrect law, missing native interpretation or unsupported construct.

## Additional strategies use the existing grant

Default search can try checked row supports, scalar lockstep, guard-distance
ranks and compressed counterexamples within the existing allowance. These
are proposals, not extra facts. New stages do not increase the caller's budget
or bypass `from: 'any'` and `search: false`.

A verdict may carry `acceleratedRun` (a finite run with checked repeat
segments and a total step count) or `fairRing` (a checked recurring run for a
liveness law). A fair ring replays the stem and first lap in the interpreter;
its symbolic recurrence is over the unbounded natural model, not a promise
of unbounded host execution. Neither field is an expanded finite `run` or
native source replay for an extracted model. Evidence labelled **checked in Lean,
not by the kernel** comes only from the separate [opt-in aggregate API](lean-aggregate.md).

## An optional real safety watchdog

A cooperative real-time bound is a separate option:

```ts
const verdict = proveRule(rule, laws, {
  search: {work: 1_000_000},
  watchdogMs: 60_000,
})
```

The watchdog can interrupt a search before its counted allowance is spent. That result is intentionally sensitive to elapsed time. Omitting it does not disable native compiler, subprocess, test-runner or infrastructure watchdogs; those are separate failures, not proof-search completion. A cooperative watchdog is not an operating-system hard deadline.

Nested scopes cannot renew an enclosing work allowance or watchdog. Effect `withLemmas` options apply **per lemma**, like its legacy `ms` option, rather than granting a total for the whole helper. An existing enclosing scope still limits the combined work. Its additive `attempts` result retains each lemma's actual verdict or failure; an optional support stop does not by itself make the final source-law verdict a timeout.

## Read the result, not its elapsed duration

An actual incomplete search interruption carries structured metadata, for example:

```ts
{
  proven: false,
  checked: false,
  stopped: true,
  termination: {kind: 'work-exhausted', phase: 'inference poll', scope: 'search'},
  context: {goal: 'original goal', stuck: 'sat', witness: {/* original values */}},
}
```

`kind` distinguishes `work-exhausted` from `wall-deadline`; `phase` names the observed boundary. `scope: 'stage'` is a local allowance, not automatically cancellation of the whole operation. Original goal, SAT/model and reason information is retained as context when a later interruption becomes the primary diagnosis. Use the actual fields; words such as “time” in an unrelated semantic refusal are not evidence of a deadline.

A completed checked proof or concrete refutation is not relabelled by a later wall-only observation. Actual rejected work admission still fails closed. An unknown caused by missing source interpretation or an unsupported feature is not automatically a stopped search. Public source acceptance still requires `proven && checked`; a model-only `kernelProven` result is not a native source proof.

## CLI scope

```sh
gdp-wired check service.py --work 1000000 --no-propose --json
# Optional independent safety bound:
gdp-wired check service.py --work 1000000 --watchdog-ms 60000 --no-propose --json
```

The CLI does not treat its default `ms` value as an explicit grant competing with `--work`. Supplying both flags explicitly is invalid. The initial explicit-work CLI path requires proposals disabled and does not support security proposals. Leads-to and two-run checks refuse both explicit work and explicit watchdog modes: their preflight is not scoped by those options. This includes a zero watchdog; it is an unsupported-mode refusal, not a reported deadline. Other liveness checks can likewise refuse unsupported modes instead of silently running an unscoped preflight. Read each law's result and refusal reason; do not assume every family supports explicit work mode.

Incomplete stated-law checks retain exit code 2. JSON preserves search stop metadata and reports optional support attempts separately. Native replay/refusal, malformed input and process failures remain distinguishable from a prover deadline. A stopped search proves neither that a law is true nor that it is false.
