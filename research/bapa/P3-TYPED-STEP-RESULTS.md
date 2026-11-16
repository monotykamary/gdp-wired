# client_server_db_ae: SOURCE ACCEPTED at every size

## Joint acceptance gate

The single authorized rerun, batch **20261116-000516-xfwsgk**, job `p3-typed-client-step`, completed with **exit0**, 186.76s job time / 934.7s wall time. `lake build`, the explicit final source-proof compilation and the axiom gate all passed.

All of the following hold together in the same tested project:

- **54/54 original target obligations**: 27 INIT and27 STEP checks true.
- **Full family check true**, with `p3_family` and `p3_all54` proved by kernel reduction.
- **Same surviving constant64 bound mutant rejected**, while its unmodified baseline STEP0 now passes. The control is differential, not merely a rejection of an already-failing baseline.
- **Source inclusion checked**: `p3_inclusion` transports the actual source ghost extension into the independently typed target.
- **Public-law implication checked**: `p3_law_implication`.
- **Original source existential theorem checked**: `bapa_client_server_db_ae_source`.

The source theorem quantifies over the source environment and every reachable state. Node, Request, Response and DbRequestId sizes remain independent parameters (`nodes`, `requestSize`, `responses`, `ids`; indices31/32/33/34). No parameter equality, common bound, positivity restriction, padding or nonempty-domain assumption was added. This includes zero sizes.

## Changes in this rerun

1. Added `Typed.withoutStepCache`, whose tree-preservation theorem is rfl. Every STEP optional named-hypothesis list is cleared before the existing typed transform; the original tree and table are retained. The kernel checks each resulting certificate against the **complete reconstructed typed STEP goal**. No goal conjunct is deleted. The prior four INIT-cache clearings are unchanged.
2. Added only `or_assoc` to the public-law helper's existing simplification set. This resolves `(A∨B)∨C` versus `A∨(B∨C)` without changing either law.
3. Checked the concrete STEP/INIT cache-clearing, option completeness, and retained tree-shape properties in the final proof module. The six generic row/sort controls remain green.

No proof search, fallback reseed or additional rerun occurred.

## Axioms

`p3_all54`, `p3_family`, `p3_old_bound_refused` and `p3_law_implication` depend only on `propext`. Source inclusion and `bapa_client_server_db_ae_source` depend only on `propext`, `Classical.choice`, `Quot.sound`. The axiom gate passed; no sorryAx, native_decide trust or new axiom is accepted.

The final source theorem has the form:

```lean
theorem bapa_client_server_db_ae_source (ρ M) (hr : SReach p3_source ρ M) :
    ExHolds p3_source_body p3_source_key p3_source_exists M p3_source_keys ρ
```

It composes source alpha-renaming, checked ghost reachability, source inclusion, the complete target-family theorem, the checked law implication and witness substitution back to the original source state. The source definition is emitted from the actual sized client model, with retained basis equality checked separately.

## Reproduction and evidence

Recipe: `research/bapa/p3-typed-step.jobs.json`; generator: `research/bapa/p3-client-typed.ts`; final source proof: `research/bapa/P3TypedSource.lean`.

Artifacts: `runs/bapa-p3/typed-step-v1/p3-typed-client-step.files/`.

| Artifact | SHA256 |
| --- | --- |
| checks.tsv | 54e8986a08d09e07d8645bd5968dc89a73ce4747609cdf72c5460c119423e8bc |
| lean.log | cda9f654c0636fb4d1dc98e82f1ce775a0bb21acd0a8433f2dd14c69ded1db80 |
| CHECKED.txt | bcdde07c5399b13a03ca3b32ac6cfd75b015f51bfb74b65a237ab9476494a06d |
| project/BapaProof.lean | 78c237961144bfbb183e757acb2dfb70243070c2a9885606d613947f5c32dca8 |
| project/P3TypedDefs.lean | dd0ede63af26af7c22a02f308f7040018cc6be8149feff3bb0bcad5c1191d464 |
| project/P3TypedClient.lean | 49dfbadd258898ffe1cf4a2cd6229542f65527f8fec6bcfdc5bbac70763582b7 |

Original capsule and Proofs.lean pins remain respectively `e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0` and `8d629dfe6d70661809e378ab21ec738a5173613cf1796473f3032942b1f7dbce`.

Cleanup is confirmed by close receipt **83827504bc86c36541a9f4ec5bbec4169dcfc6519fbee67e0cdddbab8b2b6f34** (`cleanup_complete=true`). Commitlint passed. No job remains running for this rerun.

This acceptance supersedes the historical blocked runs documented in P3-TYPED-CLIENT-RESULTS.md and P3-TYPED-INIT-RESULTS.md; those failure records remain intact.
