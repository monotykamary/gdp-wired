# Slice 3 Lean-first gate — partial, not port acceptance

2026-11-14. Canonical regression source remains frozen at `142d1f5ab7a85429afa0a3ddfc4d0999765b6761`; these separate slice-3 foundation files are excluded from its archive.

## Retained gate

Batch `20261114-053505-nlevsb`, job `rigid-lean-bridge`, native exit 0. Fetched with `supercomputer batch fetch` to `runs/bapa-rigid-lean-04-fetch/`. The job compiles `Rigid.lean`, `RigidNaive.lean`, and `RigidMutants.lean`; `result.txt` is written only after all three succeed.

- `lean-kernel/Rigid.lean`: generic two-universal/one-existential bounded choice equivalence, finite-typed and bounded-Nat quorum specialization, source-premise discharge, minimal nonempty-quorum/nonempty-node consequence, and existing map framing/start facts. No new axiom or certificate constructor. Choice/discharge use only `propext`, `Classical.choice`; some framing/minimal facts additionally use `Quot.sound` as printed.
- `lean-kernel/RigidNaive.lean`: exact three source relations and three actions, all three **given** source invariants inductive, and original agreement under the original Ivy intersection axiom, for arbitrary symbolic finite Node/Quorum/Value sizes. Initial/step/reach invariant and original safety theorems print **no axioms**.
- `lean-kernel/RigidMutants.lean`: finite countermodels to dropped witness range, missing membership conjunct, and diagonal-only universal coverage. Compiles; one harmless unused-variable warning.

The original Ivy law ASSUMES intersection, covers any intersecting family, and uses helpers given, not found. It does not replace the canonical suite's majority/counting port, whose intersection is PROVED by counting. Endive TLA+ lacked the axiom; the exact restored source is the pinned Ivy file documented in `research/bapa/notes/BAPA-SLICE3-PLAN.md`.

## Not yet delivered

This is a semantic Lean-first gate, not a completed emitted-machine certificate. Still required: exact public rigid-instance lowering/validation; deterministic smallest-node witness tables; proof that the actual emitted machine facts are established by the original precondition (including freshness and tuple substitutions); minimal rigid example through runtime and export; multi-sort/rigid-read finite-consumer census; the actual `learnedQuorum(value)` proof-only ghost-map certificate and source-law discharge; concrete source/interpreter comparison and full negative controls. D review of the new Lean bridge is requested before introducing its TypeScript acceptance/export path. The existing `GhostMap.lean`/`ghostedOk` route is present; it must be used, not replaced with an observable model helper.

## Separate canonical packet preparation

Main authorized a fresh slices-1/2 29-way regression, including an explicit MLDR 9950X/JSC8G amendment, only after D's exact GO. A remote **preparation-only** job is building the source-bound packet and scanning models/laws without a public prove call. At that historical preparation checkpoint no canonical regression had been launched. The subsequently authorized frozen-142d cohort is recorded in `BAPA-CANONICAL29-PENDING.md`; it excludes all slice-3 files, and no new verdict/vector comparison result is claimed here.
