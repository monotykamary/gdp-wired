# Typed client: INIT repaired; STEP named-hypothesis gate remains

Historical result; superseded by **SOURCE ACCEPTED** in [P3-TYPED-STEP-RESULTS.md](P3-TYPED-STEP-RESULTS.md).

## Result of the one authorized rerun

**Not source accepted.** Batch `20261115-235922-uadbct`, job `p3-typed-client-init`, native exit1 / 50.92s. No search, reseed, extra replay, padding, size equality or positive-size assumption.

All 27 entries now transform successfully. The ordinary checker reports:

- **27/27 INIT checks true**, including previously refused entries0,1,2,26.
- **10/27 STEP checks true**: entries5 through14 inclusive.
- **17 STEP checks false**: entries0 through4 and15 through26.
- Total **37/54**, full-family check false.

For each failing STEP, diagnostic is exactly `named=false;table=true;first-failure=none`. The final field evaluates leaves under the retained transformed named hypotheses, NOT under the complete actual goal. Thus it is not proof that those leaves work against the real typed STEP goal. It isolates the present refusal to `namedIn` rather than table well-formedness or internal arithmetic under those cached premises.

## INIT change and empty sorts

Added `Typed.withoutInitialCache` / `Typed.entryWithoutInitialCache`; only client entries0,1,2,26 select the wrapper. Their optional certificate named-hypothesis lists become empty. The checker therefore uses the **full freshly reconstructed typed INIT goal**. No conjunct is deleted from the goal, and no term is assigned a guessed sort. Both old tree and variable table pass unchanged to the existing per-sort transform; the wrapper's tree-preservation equality is rfl.

This distinction matters: the old `0<64` appeared inside a cached negation of an instantiated law, not as an isolated list item. Removing the cache avoids attempting to retype that closed old formula while leaving all actual obligations intact. The retained INIT trees pass against the complete typed goals even when a size may be zero. No surviving INIT row demanded `0<requestSize` or `0<nodes`, so no provenance fallback or empty-size case split was needed.

The concrete cache-clearing, all-options-present and tree-shape checks elaborated successfully (propext only).

## Controls and source composition

All six `TypedBoundControls` theorems compile, each with only propext. Four row-equality controls now use rfl rather than requiring DecidableEq for Cert.Row.

The same surviving-old-bound mutant returns false and its rejection theorem elaborates. **This is not presently a differential positive/negative control:** its base entry0 STEP already fails `namedIn`. Rejection alone cannot yet demonstrate sensitivity specifically to the surviving constant64 row.

The source-inclusion theorem elaborates with only propext/Classical.choice/Quot.sound. However the overall source proof module fails: the 54/54 and family claims are false, and the public-law implication helper needs associativity normalization for disjunction. Its simplified actual premise has `(A ∨ B) ∨ C` where the expected expression has `A ∨ (B ∨ C)`. The existing helper normalizes `and_assoc` but not `or_assoc`. That helper was not changed/retested after this run. No final source theorem or build receipt is accepted; failing theorems' sorryAx outputs are not evidence.

## Next gap, not another execution

The next certificate task is to reconcile/drop the optional STEP caches and then check the same trees against the complete independently typed goals. Per-scope retyping can differ from the types of other laws instantiated into those goals; this must not be bypassed by trusting the cached formulas. This run does not identify a valid cached-premise implication or prove that STEP cache removal suffices.

No additional job was launched after obtaining these results.

## Evidence and custody

Artifacts: `runs/bapa-p3/typed-init-v1/p3-typed-client-init.files/`.

- `checks.tsv`: `93f2bf393e64bf3632477489dc70ebba4024a72551e2d5a33344332bd35a823a`.
- `typed-options.tsv`: `8f90f2be9cff98b97b62e4171cf38c005ec1e5153a3dd5f5079533729f3b510f`.
- `lean.log`: `8dfef382852b3a86ed8ba1a0051ff986d1a096548841319bdde0893234513ce1`.
- Cleanup complete: `ad9e3c24c83b51191dec79b318ff3c0e84028d797650f80114f2a8e632ed4e29`.
- Commitlint passed. No final CHECKED.txt receipt.

The generated `Checks.lean` records the observed true/false vector, but the job's final all-green source module fails; do not describe this as a successful complete Lean build or SOURCE ACCEPTED.
