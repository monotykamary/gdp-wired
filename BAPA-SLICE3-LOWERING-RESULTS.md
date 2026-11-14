# Slice 3 lowering results — historical GIVEN gate and automatic-minimal update

2026-11-14. At the historical checkpoint below there was no shared core/kernel/emitter change. The canonical candidate remains the independently frozen slices-1/2 commit `142d1f5ab7a85429afa0a3ddfc4d0999765b6761`; none of these research files is in its archive.

## Verified so far

- `research/bapa/rigid-instance.ts`: serialized finite tables, exact declared ranges and original-axiom enumeration, deterministic smallest witness, immutable private copies and cancellation.
- `research/bapa/rigid-lower.ts`: conservative existing-function/fact lowering; no new trusted rule; original source axiom preserved separately. Generic lowering supplies **no hand seed**. Bound execution captures parameters and validated tables for the whole run.
- Multiple-sort runtime/consumer coverage is detailed in `BAPA-SLICE3-CONSUMERS.md`.
- The scalar minimal law is **not automatically found** by current untrusted fact search. `rigidMinimalGivenZero()` is a separate, explicitly **GIVEN** `(0,0)` axiom-instance control. This seed is supplied, not discovered; there is no state-helper invariant in the minimal model.
- The diagnostic's actual generated machine certificate is checked by unchanged Lean. Its source-level corollary `rigid_minimal_original_source` uses `source_iff_extension`, exact `witnessFact_iff`, and `smachine_sound`; it establishes the full emitted facts, including the GIVEN ground instance, from the original intersection axiom and ordinary relation typing. The source theorem has no privileged witness premise and no auxiliary in its conclusion. Printed axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Retained batches

| Batch | Outcome |
| --- | --- |
| `20261114-055659-gafj9t` | 18 validator/runtime tests passed; unseeded minimal search not proven. Preserved as evidence of the general instantiation gap. |
| `20261114-055749-kzjkf4` | Isolated edit syntax error; preserved. |
| `20261114-055833-upjv5b` | Wrong research call shape to existing `substC`; strict typecheck and runtime correctly rejected it. Preserved. |
| `20261114-055912-rd1bni` | 19 tests, strict TypeScript and conditional certificate passed. Its zero-tuple seed was hand supplied: **GIVEN**, not found. Source wrapper was not yet present. |
| `20261114-060044-00kx2a` | 20 tests, strict TypeScript and actual original-source wrapper passed; harmless deprecated/unused simp warnings. **GIVEN** diagnostic. |
| `20261114-060236-uzr4jk` | Expanded multi-sort consumers: 20 tests / 76 expectations, strict TypeScript and warning-free original-source wrapper passed. **GIVEN** diagnostic. |

Every listed batch was fetched with `supercomputer batch fetch` to its numbered `runs/bapa-rigid-minimal-XX-fetch` directory. Failed results are not overwritten.

## Final-check collected

`bapa-rigid-final-check.jobs.json`, batch `20261114-060343-wjzlvw`, completed all three jobs with exit 0, fetched to `runs/bapa-rigid-final-check-01-fetch`. It passed 21 validator/binder tests including refusal of structural capability lookalikes, strict typing of the research/export files, GIVEN diagnostic original-source export, and 52 unchanged finite/tuple/exists/function/export-shape/qalpha regressions. This snapshot predates the authorized shared strategy; it is not claimed as a new-strategy regression run.

## Subsequent authorized strategy

Main subsequently authorized opt-in/default-OFF ordinary function-fact instantiation on `after/bapa`, with D review before merge/count and no new canonical run. The automatic unseeded minimal certificate and original-source wrapper now pass (`20261114-060917-5l4p0z`); the actual port is still incomplete. See `BAPA-FUNCTION-INSTANTIATION.md` for current source, controls and retained failures. The historical remaining-gates description below records the earlier checkpoint, not the current authorization state.

## Remaining gates / limits

The generic unseeded minimal case and actual naive-consensus emitted certificate are **not complete**. `BAPA-PROVER-GAP.md` records the general untrusted strategy requested by Main and design-reviewed by Fable (75.7) and D, including sort-derived zero bootstrap, whole tuples, typed ghost-map results, sort-graph/depth bounds, charged caps and default-off behavior. D's review is design-only, not shared-prover implementation/merge/count-change authority. No such shared patch is made.

Still required: automatic unseeded search controls; actual `learnedQuorum(value)` ghost-map certificate/elimination; original source transition comparison and negatives; full port source-premise discharge and D review. The separately proved Lean source semantics in `RigidNaive.lean` are not a substitute for that emitted-machine proof.

The canonical suite's majority/counting row **proves** intersection. This new Ivy-source port **assumes** the original intersection axiom for arbitrary intersecting families. Helpers for that port remain **given, not found**. Neither result substitutes for the other; this diagnostic is not port acceptance.
