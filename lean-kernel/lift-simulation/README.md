# Shape-driven radix / invariant-restricted simulation

`tryRadixSimulation` accepts a **structural** capsule body, the independent
`gdp-lift-source/v1` AST, and the common `PartOptions`. The caller owns graph/hash
validation and exactly-once term restoration. It does not dispatch on a schema,
protocol identifier, map name, SUM name, fixed basis, or fixed radix.

The result is `EMITTED_NOT_CHECKED`, not a source-acceptance receipt. Every name
in `requiredTheorems` must pass native Lean and the baseline axiom audit before
acceptance. No old generated `Proofs.lean`, research module, or historical check
receipt is a runtime dependency. The original complete retained family is
regenerated through the retained-only exporter after data-only SUM lowering.

## Canonical mathematical interfaces

The helper modules below live only in `lean-kernel/` and are delivered through
`leanSource`. All three passed native Lean with baseline axioms in
`runs/frozen-snapshot-03`; generated SDL source acceptance is a separate gate.

* `InvariantSimulation.lean`: local operational correspondence only under a
  target invariant, instantiated from a checked target-family theorem. Produces
  a finite forward simulation and the original source reachability conclusion
  without adding the invariant to source assumptions. An all-state
  `SourceInclusion` is deliberately not used.
* `SemanticSums.lean`: exact global sums and ghost-independent source projection
  from a proved finite-change cover. Covers quantify over **all natural
  addresses**. They may use the already checked family in the pre-state;
  no extra assumption is inserted into the machine.
* `RadixSumTransport.lean`: fail-closed candidate construction over declared
  layouts, radix, fresh basis and opaque SUM flags. Whole-address integrands
  remain untouched. Typed cell/binder/instance/table/equality-tree phases are
  separate from complete `checkSMachine` acceptance.

## Current emitter boundary

The generic candidate layer handles declared layouts; the source-proof emitter
currently requires binary tuple layouts, no carried maps or pre-existing
quantified flags, and one raw cell read per producer SUM integrand. Nonempty
SUM declarations on the provided source itself are explicitly refused. Whole-map updates on
a typed map need a projection-binder source bridge and are rejected. Mixed
radices, absent/ambiguous SUM declaration provenance, missing primary
certificates, missing Boolean family invariants, changed public-law shapes,
and other unsupported recognized candidates throw; they do not fall through
to a weaker strategy. `null` is reserved for a noncandidate.

The generated target, complete family length/check, shape equalities, semantic
covers, exact sums, operational equalities, restricted simulation and each
unchanged public source conclusion are independent Lean obligations. Generated
proof templates must still be qualified on the exact capsule: a typechecked
emitter or a checked generic helper alone does **not** establish the SDL result.

## Accepted public SDL case

`public-05` ran the public CLI against the independent frozen
`research/bapa/lift-fixtures/simple_decentralized_lock.json` and exact retained
capsule `e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958`.
Snapshot `67c5b69c1b1b17fad152dc559963309bcff549d3` produced
**SOURCE_CHECKED** with both `lake build` and the root Lean check exiting zero.
The complete four-entry family, SUM semantic obligations, invariant-restricted
simulation, original source conclusion, and optional theorem aliases passed;
all 26 audited declarations use only baseline axioms (or none).

Receipt: `runs/public-05/radix-public-sdl.files/project/LIFT-CHECKED.json`.
Emission SHA-256:
`4eb8e997879a402dfdb5ba6a0559054f703df05a5bc2205a8e061802fef7db8a`.
This is newly generated source acceptance, not historical replay or proof search.

## Development verification

Run `check.jobs.json` through `supercomputer` from an immutable detached check
snapshot. It checks generic lemmas, TypeScript, shape-only mutants and exports a
data-only current symbolic-source fixture. It does not load/replay an SDL
capsule or launch proof search. The first mutable-tree submission failed before
admission; its log is retained separately from actual native attempts.
