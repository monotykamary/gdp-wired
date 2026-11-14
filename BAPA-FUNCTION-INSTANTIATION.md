# Authorized function-fact instantiation — review checkpoint

2026-11-14. Branch `after/bapa`, after frozen slices-1/2 source `142d1f5ab7a85429afa0a3ddfc4d0999765b6761`. Main authorized this implementation only, not merge, main, the 4aaf claim or a changed canonical run. Fable 75.7 and D's `BAPA-GENERAL-INSTANTIATION-DESIGN-REVIEW.md` define the boundary. **D diff review is still required.**

## Shared change and trust boundary

`kernel/function-instances.ts` proposes only ordinary `Instances` for existing guarded function facts. `kernel/prove.ts` has one import and one conditional branch in `instancesFor`; when no synchronous `withFunctionInstances` scope is active it calls exactly the previous `withFacts(m, inst, fnKeys(m, build(inst)))` path. There is no environment switch, automatic activation, package default, added ground fact, privileged interpretation, obligation-builder change, kernel/checker change or Lean-rule change.

The separate slice-3 Lean foundation and source wrapper were already part of the reviewed Lean-first plan. `Rigid.lean`'s Skolem/source bridge is its only new trusted mathematical statement. Functions known by their facts and relation 0/1 ranges were already representable. The new untrusted strategy does not extend that trust boundary.

## Search contract

- Sort-separated pools; ordered whole function tuples, preserving head and arity; complete bindings only; repeated-variable consistency; compatible covering-pattern joins; no locally quantified variable escapes.
- Priority: actual matching reads, other scoped terms (including typed proof-map values), declared function results, then declaration-derived zero per sort. Zero is proposed even when absent from the goal. It never asserts inhabitance: every original range antecedent stays in the unchanged instantiated fact.
- Optional nominal sort/key metadata filters known-incompatible terms, including an entire native/encoded pair fed back as an atomic sort by legacy helper search. This is a heuristic, not a typing axiom or completeness claim. `learnedQuorum : Value -> Quorum` is proof-side metadata, not a source state map.
- Deterministic sort-graph order; an explicit depth limit for cyclic signatures. Charged work, per-sort candidate, per-fact tuple and intermediate matching/join limits. Limit exhaustion returns `proven=false, checked=false`; it does not establish a finite closure or source counterexample. Existing helper-law planning is not changed.
- Context is restored in `finally`; asynchronous scopes are rejected. Input machine/facts are unchanged. Nonmatching facts retain legacy instantiation.

## Verified retained gates

| Batch | Evidence |
| --- | --- |
| `20261114-060343-wjzlvw` | Prior to shared strategy: 21 validator/binder tests; 52 finite/tuple/exists/function/export-shape/qalpha regressions; strict typing and GIVEN source wrapper; all three jobs exit 0. |
| `20261114-060709-1rz9g0` | Initial 9 strategy tests / 21 assertions and scoped strict TypeScript passed. |
| `20261114-060917-5l4p0z` | 12 strategy tests / 27 assertions and strict TypeScript; actual automatic unseeded minimal certificate plus `rigid_minimal_original_source` compiled in unchanged Lean. Printed axioms only `propext`, `Classical.choice`, `Quot.sound`. |
| `20261114-061315-87if06` | Final strategy snapshot: 15 tests / 38 assertions, strict TypeScript, type-aware lint (zero warnings/errors), commitlint, and automatic minimal original-source Lean export all passed. |

Each is fetched to its numbered `runs/bapa-*-fetch` directory. The unseeded minimal gate adds no `m.facts` entry and supplies no instance tuple. It covers the equivalent no-literal-zero law, whole/off-diagonal three-argument and nested triggers, repeated binders, covering patterns, ghost-result sorts, scope capture, no-match, cyclic/candidate/tuple/work refusal, restoration, axiom/range/membership omission and an exact default-OFF-before/after result comparison.

`20261114-061140-ud2i7l` passed 13 tests / 30 assertions, strict TypeScript, commitlint and the unseeded original-source Lean wrapper; its scoped lint correctly failed on two unused test imports. Those imports were removed; the final `87if06` gate additionally covers exact structural-ID deduplication, deep expression identity and duplicate hypotheses. Its evidence is in `runs/bapa-function-review-02-fetch/`. The separate Lean foundation is committed as `d30c5cf7a1d445096979907776e664f90df9cc40`; the strategy commit does not modify any Lean or trusted-kernel file.

## Actual port — not complete

`research/bapa/rigid-naive.ts` retains the original `vote(Node,Value)`, `decide(Quorum,Value)` and `decision(Value)` state; the two distinct finite guards; and the original intersection assumption. The three source helpers are explicitly **GIVEN, not found**. `learnedQuorum(value)` is a fresh proof-only ghost map checked by the existing `ghostedOk` route, not an observable model helper. Neither a selected table nor a ground tuple is supplied to proof search.

Retained uncounted attempts, each `proven=false`, `checked=false`, never a source counterexample:

| Batch | Refusal |
| --- | --- |
| `20261114-060839-i0i9bo` | Quorum candidate cap 128; work 188267 / matched 8 / generated 1182. |
| `20261114-061140-gvi4q4` | Work cap 2,000,000 after nominal key filtering; work 1999995 / matched 9 / generated 845. |
| `20261114-061223-egozf6` | Same work cap after exact structural IDs; work 2000000 / matched 9 / generated 845. |

Reports are in `runs/bapa-rigid-naive-0N-fetch/unseeded-naive-consensus.files/proof-report.json`. Legacy helper instances can feed whole encoded map keys into scalar ghost-map reads and back into function candidates; generic nominal key filtering prevents that feedback. Remaining repeated scanning is being reduced by exact structural-ID deduplication, without changing the helper planner, adding a port-specific seed, or increasing any cap. A fourth uncounted attempt and the corresponding focused gate are pending.

Still required: actual whole port certificate; ghost-map existential elimination in the actual export; original-source wrapper; independent concrete transition comparison and port negatives. The already proved abstract `RigidNaive.lean` is not a substitute for these.

The suite's majority/counting row **proves** intersection. The new original-Ivy port **assumes** intersection and covers arbitrary intersecting families. Neither implies the other. The running canonical29 batch `20261114-055201-htv9qk` is still exactly frozen `142d`, with its original single collector; it is not rerun here and does not include this new strategy.
