# Cancellation-only checkpoint map

Source: `efd702761f03c320939679912e6d0f2579696010`.
No weights, counters, search order, heuristics, endpoint allocations or checking
rules change. No offending counter is clamped, reset or left unrecorded.

| Source | Check / reason |
|---|---|
| `kernel/prove.ts:258–260` | `checkWorkEndpoint`: strictly enclosing counted endpoint; no local deadline promotion |
| `kernel/prove.ts:296` | prover boundary, before later root/subsearch work |
| `kernel/prove.ts:312` | prover poll, before returning from an expired work scope |
| `core/dsl.ts:2837` | recursive preflight fact bindings |
| `core/dsl.ts:2841,2897` | propagate BudgetExpired only when enclosing W expired; retain old handling of local cuts |
| `core/dsl.ts:2850` | refutation trial/request polling |
| `core/dsl.ts:2951,2997` | refutation return boundary, rule and step-law entry points |
| `core/watch.ts:113` | extra global-only check every 16 bindings; original 256-binding check unchanged |
| `core/infer.ts:301` | relation tuple enumerator, each binding |
| `core/infer.ts:681,690` | inference entry and existing stop predicate |
| `core/infer.ts:779,802` | sample trial and request loops |
| `core/infer.ts:1518` | recursive view-binding loop, outside invalid-frame catch |
| `core/infer.ts:2306` | finite-instance/BFS step, outside invalid-step catch |
| `core/infer.ts:3397` | propagate an outer-W stop through join fallback |
| `core/fresh.ts:25,35,39,76` | fresh entry, trial, step, validation loops |

Every new endpoint check is inert when no explicit work scope exists. At or
below the enclosing endpoint it is inert even if a local search deadline has
passed. Above it, the existing BudgetExpired type reaches workVerdict and
returns `{proven:false, checked:false, stuck:'unknown', why:'work budget (…)'} `
with the checkpoint's own phase. It never converts cancellation into a proof.

Trusted identity gate: all `kernel/` except untrusted `kernel/prove.ts`, all
`lean-kernel/`, `core/check.ts` and original model sources remain byte-identical
to 646811df. The prover body below its cancellation header also remains exact.
`runtime.patch` is the minimal production diff; tests are separate.
