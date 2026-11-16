# Counted bound-inclusion lift

`tryEmitBoundInclusion({id, bundle, providedSourceAST, options})` is a data-only,
no-search emitter. `id` is the common loader's validated `bapa_` + source ID.
`bundle.final` supplies the complete retained machine, laws, and certificates;
its outer capsule schema and identity belong to the common loader. The caller
must validate the entire graph/hash and restore the exact term prelude once
before invoking this component. The provided `gdp-lift-source/v1` machine is
emitted literally; it need not equal the capsule's original source.

A positive upper bound in the retained precondition is a candidate only if
its erasure admits the supplied precondition by structural subsumption. No
candidate returns `null`. Unsupported or ambiguous candidates throw; callers
must not catch those errors and fall back to another strategy. Unsupported
changes to operations, declaration meanings, quantifier keys, source metadata,
or missing/extra primary certificates are refused. Parameter-list labels are
ignored only by operational preflight (SMachine has no params field); all their
actual uses and the supplied source expressions remain in the shared basis. Exactly one retained law
must structurally imply each public law; law names are not selection keys.

The generated project:

* regenerates every retained entry with the existing retained-certificate
  exporter (no old `Proofs.lean` or research-tree dependency);
* transforms the machine, declarations and every certificate with
  `CertificateBoundErasure`, preserving all `CEntryF` auxiliary lists;
* rechecks the transformed global conditions and every complete family entry
  with the native Lean checker, then assembles the entire family theorem;
* checks local QAlpha/RowAlpha transport, operational source inclusion, count
  noninterference and declaration membership, and public law weakening;
* emits both `${id}_laws` and the same-proposition alias
  `${id}_transported_laws`, with the latter returned as `familyTheorem`;
* prints every required theorem's axioms. The common verifier must enforce
  baseline axioms only and must never mark an emitted project as checked.

`StructuralWeakening.lean` defines a generic constructor relation for AND/OR
subsumption and contravariant negation with opaque arithmetic atoms. Its soundness theorem lifts
pointwise implication through the original public quantifier keys. Generated
constructor trees are checked by Lean, not trusted as JavaScript decisions.
No arithmetic/propositional search, SMT, `native_decide`, custom axioms or
admitted proofs are used.

## Native tests

Run only on the supercomputer:

```
supercomputer run --jobs lean-kernel/lift-special/tests.jobs.json \
  --out lean-kernel/lift-special/runs/NEW \
  --class interactive --strict-once --max-attempts 1 --backend boat
```

The two jobs independently check the generic Lean relation and an entire fresh
synthetic counted transformation, with full helper-family retention and a
multi-key public weakening. These are not a replay of the historical real
capsule. The final real-capsule suite is owned by the parent orchestrator.

`StructuralWeakening.lean` has been promoted to the root product library after
its native gate. Both the product emitter and check harness use
`leanSource('StructuralWeakening')`, so bundled/dist execution has no adjacent
source-file dependency. The root module is the single canonical source.
