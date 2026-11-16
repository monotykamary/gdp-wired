# Shared source inclusion and law implication

`SourceInclusion.lean` replaces an equality-only source bridge when a retained
producer admits more requests or proves a stronger law. It is not specific to
64, toy consensus, a variable basis, or a count representation.

## Checked API

In namespace `Kern`:

- `SourceInclusion s t` records equal input/carried interfaces and initialization,
  source-start-map/precondition/fact implications, source-admission implication,
  and equal next states **on source-admitted requests**.
- `SourceInclusion.creach h ds` derives `CReach s ds -> CReach t ds` by induction.
  Count declarations are the same on this leg; additional producer counts must
  first be handled by `bapa_counted_source_law` / its reachability projection.
- `SourceInclusion.sreach h` derives the ordinary `SReach` inclusion.
- `SourceLawImplication strong weak` means the complete quantified strong entry
  implies the complete quantified weak entry, for every environment and map.
- `sourceLawImplication_of_pointwise` lifts a checked Boolean-formula implication
  when the entries' key and additional-key lists agree.
- `sourceLaw_via_inclusion` composes counted inclusion and law implication.
- `sourceLaw_via_sinclusion` does the same for ordinary reachability, and can be
  composed with an independently checked ghost/witness projection.

These are semantic premises proved in Lean, not booleans accepted from the
exporter. There is no assumption that the source already has a producer run.
The reachability inclusion is derived by induction, including count-correct
request views. No transition or public source law is weakened in place.

## Toy consensus composition

`p2-toy-inclusion.ts CAPTURE PROOFS NEW_PROJECT` verifies the exact original
capsule and retained Lean-source hashes. It restores the immutable term prelude,
rechecks the retained native family through the existing exporter, and emits
the current `toy_consensus_forall` port into the retained numerical basis.
`P2ToySource.lean` then checks:

1. The numerical producer basis agrees with the retained machine.
2. `QAlpha.validAll` and its semantic transport for the current source binders.
3. Fresh-count projection using the existing `bapa_counted_source_law`.
4. Source request admission implies transported request admission; request views,
   initialization, and next states agree.
5. The imported `ToyConsensusForallTransport.laws` theorem supplies the full
   transported family, including entry 2, without searching again.
6. Entry 2's unbounded safety implies the untouched source law with `values`
   guards. The resulting theorem is
   `bapa_toy_consensus_forall_source_law0_holds`.

The output manifest hashes every Lean/source-data file, including the source
machine, public laws, numerical basis and imported transport module. Historical
`identity.sourceCommit` belongs to the retained producer; the current source
port is separately bound by `identity.sourcePortSha256`. Emission is explicitly
`EMITTED_NOT_CHECKED`. Only the existing `proof-source-verify.ts`, after a clean
Lean build and explicit named axiom output, writes `SOURCE-CHECKED.json`.

## Client/server and other consumers

P3's `client_server_db_ae` should use the same `SourceInclusion` structure and
`.sreach` leg with its actual sized source/producer pair. Compose that inclusion
with its **separately proved** ghost projection and per-law implication.
`sourceLaw_via_sinclusion` is the convenience composition for kernel entries;
`.sreach` itself also feeds ghost theorems whose conclusion is not an `SEntry`.
The module does not itself invent or certify an existential witness, ghost
projection, binder renaming, or a client's source translation. Those obligations
remain explicit. No toy-specific definition is needed by the shared module.

## Verified gate and negative controls

Batch `20261115-230950-kqcuih` passed scoped TypeScript, commitlint, a complete
35-module Lean build, explicit root/negative-control checks and the independent
source receipt verifier. The source theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.

`SourceInclusionControls.lean` proves:

- `extra_source_request_refused`: there is no inclusion from the all-request
  source into an otherwise identical machine that refuses every request.
- `unsupported_source_law_refused`: a true producer entry cannot imply a false
  source entry.

These are checked negations of the actual admission/implication contracts, not
failures explained by unrelated machine-shape mismatch.

Receipt:
`runs/bapa-p2/inclusion-6/p2-toy-source-inclusion.files/SOURCE-CHECKED.json`.
Lean log hash:
`7b82dca3fe826b89697585fd503360968d811826a61ab44d07a7f60740bd7ada`.
Shared module hash:
`c2f20d4c1b9e3d2d29cecce3ff15af280599e3173224f7d6710f37ec3055054d`.

This establishes the emitted sized source-port law at every size, not a new
formal IC3Syn/TLA+ translation theorem. The existing TLC correspondence remains
a separate bounded check. No additional protocol search was used for this bridge.
