# Confirm model refinement before admitting SAT

P4's `z7uv4q` retained:7 witness is a model of the initially instantiated
sharded-kv obligation, not the entire assumed family. It violates present
retained:3 and retained:8 at `(241,764,1571,1)`. P4's AST-only inspection
`j43pcr` shows that the existing model-instance selector finds both refinements.
No tuple decoder or protocol-source change is needed.

## Policy

The untrusted prover may keep refining, prove the refined obligation, or report
UNKNOWN. It must never turn an incomplete refinement into SAT by returning its
first model. The existing round cap, work share, tuple/evaluation allowances,
and caller's wall remain limits, not permission to admit an unconfirmed CTI.

- `withModels` no longer returns `first` after a later unsettled result or stop.
  Its callers supply an explicit UNKNOWN constructor that removes the witness.
- `modelInstances` can report completion separately from its optional added
  instances. No additions do not imply confirmation: evaluation failures,
  truncated enumeration, ineligible tuples, and already-assumed false instances
  keep the model unconfirmed.
- The fast/ordinary `settle` paths use the same policy. Only confirmed models
  enter the negative memo; `GDP_STRICT=0` cannot restore unsafe admission.
- Candidate admission preserves UNKNOWN as inconclusive, keeps the candidate,
  and includes the unconfirmed-model reason. It cannot treat that result as a
  Houdini deletion.

Confirmation is the existing model-domain check, not a new proof of an
arbitrary infinite interpretation. Only a complete family proof checked by the
kernel can establish the caller's property. `kernel/kernel.ts` and all Lean
checker sources are unchanged; `kernel/prove.ts` is untrusted search code.

## Regression evidence

`fixtures/retained7-model.json` retains the exact 25-law input and witness,
labelled with the original and AST-inspection batches. The public replay
reconstructs a real DSL rule with that step, injects the saved model at the
existing root-query observation seam, and makes the refined query unsettled.
It enters `proveRule` and inspects its actual candidate-admission report, then
stops at that report to avoid a fallback protocol search. The candidate must
remain, with zero drops and an UNKNOWN reason.

A disposable negative-control run restores the stale-first-SAT return and
requires that public regression to fail. The production file is restored in
`finally`. Unit controls separately cover wall expiry, round exhaustion,
already-assumed false instances, zero tuple allowance, and a genuinely
confirmed model that still reports SAT. Existing positive family proofs and
false-helper controls remain part of the gate.

The first complete focused gate (`20261115-235650-2lp2xa`) passed scoped
typecheck, 285 kernel tests, 45 compatibility/control test executions, and the
two retained-model/public replay tests. The mutation was rejected specifically
because it dropped retained:7 as SAT; it was not accepted merely for a fixture
or infrastructure failure. Final pinned-Bun gate `20261116-000047-3bn9gl` repeated all of these checks and
also passed the `GDP_STRICT=0` replay and commitlint. Exact results are recorded
in `MODEL-CONFIRMATION-RESULTS.json`.

An exploratory `bun test kernel` also matched `lean-kernel/` and exposed an
unchanged export-baseline expectation: the frozen-F list does not include the
already-present `RowAlpha.lean` and `BoundGhost.lean` modules. That separate
baseline is not edited or represented as green here. The focused gate names
all `./kernel/*.test.ts` paths explicitly.

No sharded-kv reseed, protocol acceptance, source Lean result, or new all-size
claim is made here.
