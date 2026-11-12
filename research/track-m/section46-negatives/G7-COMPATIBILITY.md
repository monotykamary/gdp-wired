# Mechanical G7 compatibility only

Base production pin: `b42a0d82441c6d7ec4db94f1ad9c763423fb5957`.

Replayed B chain: `76c35b98` -> `d5c37dc1`; `a0d77117` -> `d49226b3`.

Only the public untrusted-producer fixtures change dispatch IDs/exports.
All 35 test declarations and assertion lines are byte-identical to the replayed
chain. No caps, budgets, proof construction/checks, event assertions or expected
outcomes change. Neither test file was executed or compiled.

| Old public fixture ID | New ID | Use |
|---|---|---|
| `fixture` | `row` | Regular untrusted non-lifted proposal |
| `old` | `row` | N5 first proposal |
| `alternative` | `guard` | N5 replacement; stays a distinct recipe |
| `unavailable` | `row` | N5 unavailable dependency |
| `unknown` | `row` | N8 unknown requirement set; `required` stays omitted |
| `lifted` | `lifted` (unchanged) | Explicit exact lifted lease path |

Non-lifted proposal production moves to the new explicit-kind mock export
`proposeCountStrategyKindForClosing`. The generic
`proposeCountStrategiesForClosing` mock remains solely for the exact lifted
path. Both delegate to the same existing fixture producer and call trace.
Controller-only recipe IDs remain unchanged; they do not use G7 dispatch.

This compatibility change is not a software gate, new coverage, activation,
qualification, or a cure for N3's intentionally unsupported flat body funding.
