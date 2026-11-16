# Typed client transport: implementation and blocked replay

Historical result; superseded by **SOURCE ACCEPTED** in [P3-TYPED-STEP-RESULTS.md](P3-TYPED-STEP-RESULTS.md).

## Status

**Not source accepted.** The generic `CertificateBoundSubstitution.Typed` module compiles, but client assembly refuses four initialization certificates before the 54-obligation kernel replay. The existing common-size API is unchanged. No proof search or fallback reseed was run.

The new API accepts explicit scope-local variable and map-value sorts, represented by independent size-variable indices. It inserts one table column per size, uniformly shifts original column references, and changes only recognized bound/complement rows and the corresponding expressions. Missing sort information returns `none`. It never defaults an untyped term to one of the sizes. Tree branches, row ordering and arithmetic proof-step ordering are retained in the implementation; the intended concrete tree-shape theorem was NOT checked because assembly stopped first.

The client maps Node/Request/Response/DbRequestId to fresh indices 31/32/33/34, the exact independently sized source parameters. Per-law binder roles are recovered from explicit relation argument positions; `DbResponseSent$g` and `ResponseSent$w` values are Requests, `DbRequestSent$g` values are Nodes. Neither source assumptions nor laws are weakened.

## Exact executable result

Batch `20261115-234617-nv3v1b`, job `p3-typed-client`, native exit1 / 94.41s. `typed-options.tsv` reports:

- All 27 law transformations succeed.
- All 27 step-certificate transformations succeed.
- Initialization transformations succeed for 23 entries.
- Initialization transformations fail for entries **0, 1, 2, 26**; their full entry transformations return `none`.

These are **transformation results, not 54 proof-check results**. `P3TypedClient.lean` emits the table then fails explicitly with `typed annotation gap: see typed-options.tsv`. The family checker, same old-bound mutant check, source inclusion, law implication and source existential theorem have NOT run. No SOURCE_CHECKED receipt exists.

| Index | Law | Lost initialization provenance |
| --- | --- | --- |
| 0 | a received response was matched | ResponseSent$w starts at 0; bound belongs to requestSize |
| 1 | DbResponseSent$g where DbResponseSent is set | DbResponseSent$g starts at 0; bound belongs to requestSize |
| 2 | a received response was matched: ResponseSent$w where ResponseSent is set | ResponseSent$w starts at 0; bound belongs to requestSize |
| 26 | DbRequestSent$g where DbRequestSent is set | DbRequestSent$g starts at 0; bound belongs to nodes |

The retained named initialization hypotheses contain `.lt (.const 0) (.const 64)` (original Proofs.lean lines26,244,420,1194). After initialization substituted the store's zero value, the current classifier no longer sees a variable or ghost-map read from which to recover its sort. It correctly refuses to choose arbitrarily. Do NOT add size>0 or globally assign zero to one sort: empty sorts must remain allowed.

A next deterministic repair can preserve the typed expression origin across initialization substitution, or bind retained named initialization hypotheses to the corresponding rebuilt typed source obligations. The original tree need not be searched or pruned. This repair is not implemented/tested in this commit.

## Separate control-fixture failure

Four positive row controls use `by decide +kernel` on an equality of `Option Cert.Row`, but `Cert.Row` has no required DecidableEq instance. Those controls fail to elaborate and their generated sorryAx output is NOT accepted proof evidence. They should use definitional equality (`rfl`) or compare coefficient/constant projections; no global trusted instance is needed. The unknown-column refusal and ghost-expression sort controls do elaborate, each with propext only. No claim that the full control gate passed is made.

`CertificateBoundSubstitution.lean` itself compiled; `Typed.checked_transport` has only propext/Classical.choice/Quot.sound. This theorem still requires the full ordinary kernel check, never merely successful annotation or translation.

## Run history and custody

- Initial batch `20261115-234132-ey8z0m` stopped at a multiline constructor-layout compile error in the new transformer before any typed replay. Fixed only that layout for the executable batch above. Its cleanup receipt is `e6104088c2f92b30e5cbe0c597309ac4f5b521b74f03cfa2a9f8a39decb8b86d`.
- Executable batch cleanup complete: `008a1f02f302133986e890e133b4eab0b258c9088a11dec278f84aedc14c8f65`. Commitlint passed. No further replay or reseed launched.
- Exact original capsule: `e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0`.
- Exact original Proofs.lean: `8d629dfe6d70661809e378ab21ec738a5173613cf1796473f3032942b1f7dbce`.
- Evidence: `runs/bapa-p3/typed-client-v2/p3-typed-client.files/`.
- `typed-options.tsv`: `371a867768ef8a2713592d494e139a096749515b6221f9782b9c847a1d50a58d`.
- `lean.log`: `08203a253418d8c20a41a9eae60e49aa02a07385d211e3809e13fb6ca28a72f3`.
- Generic module: `668afd1427ce16a823ed12b070ef7f46c3fa085d35b90d032229f6031a4f4067`.

The implementation and failed controls are retained honestly for handoff. This is not a verified all-size source bridge or a shared green gate.
