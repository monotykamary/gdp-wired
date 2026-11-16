# Sharded KV progress-mode reseed

Main authorized one new seeded call after green SHARED `413865f38`, adopted as
`06fd53635`. The confirmed-CTI admission fix `85171b85b` and checked source
bridge `6c001414d` remain present. No source or candidate-manifest change.

Recipe: `p4-sharded-progress.jobs.json`. Compared with the completed default-four
recipe, the proof-policy change is explicit `--model-rounds progress`. The worker
clears inherited GDP flags, so this CLI option supplies `modelRounds:'progress'`
and records it in the result/input hash; merely setting GDP_MODEL_ROUNDS would
not survive the sealed profile installation. The 0.49 flag profile, 24G work
budget, runtime, memory and process guard remain unchanged. SAT still requires
confirmation; progress mode neither extends nor renews the outer work budget.

The one job retains the previous manifest/capsule SHA checks, records both
shared fixes and source provenance, and runs commitlint before exactly one
public worker invocation. Output: `runs/bapa-p4-sharded-progress/`.
Strict-once / max-attempts 1, no preliminary search and no automatic retry.

If a complete checked capsule is produced, use the source route that actually
matches it: the existing no-search inferred-alpha bridge for an ordinary
same-source/alpha family, or coordinate p1's SktSource* structural simulation if
it targets the distinct immutable transported producer. Do not conflate the
new native capsule with transport snapshot4434fc8d0 or touch p1's simulation
files. No source acceptance without the complete Lean/source/axiom gate.

## Completed native reseed

Batch `20261116-004037-gafb7b`, source commit
`4464e39aef079c8a7b377c05a52a6780cad53381`, invocation
`4614fd43-1639-4105-b545-df2cc0767b9d`. Exactly one public call,
29.634s, 24G work and modelRounds=progress. All 23 seeded candidates were kept;
zero restatement/native drops. Complete 25-entry usual family is proven and
checked. Worker exit 2 is `captured-unqualified`, not a proof failure: original
source projection still required a separate check. Native job 32.61s; batch
wall 3220s included scheduling/collection, not 3220s of proof search.

Capsule SHA256:
`a1885c7c4098ee59f7bfb7d67fff7b379be293f7baa8343b1c8c61c34c4185b2`.
Retained at `runs/bapa-p4-sharded-progress/sharded-progress-seed.files/sharded_kv/closure/`.

## Completed no-search source gate

One no-search job, batch `20261116-013442-clbxcq`, exit 0, job162.49s.
The capsule route is **ordinary inferred**, not witness or counted-family.
Accordingly it uses `proof-emit.ts --projection alpha` / `emitAlphaSource`,
which requires one complete usual family, checks public-law coverage, emits
both original source and producer, and demands whole-machine equality in Lean.
The db9bd046d inference-witness validator and 6c001414d witness-alpha support
are present, but their witness route is not invoked for this ordinary capsule.
No new emitter/validator/helper changes and no additional native search.

Only two binder renames were needed:
- QAlpha: flag `?unowned` (38), `k$3` (48) -> `k$5` (46).
- RowAlpha: `TransferMsg` (3), `k$4` (49) -> `k$6` (47).

`bapa_sharded_kv_alpha_result` proves the entire renamed source machine equals
the producer by `rfl`; there is **no difference beyond alpha**. Both validity
checks are `by decide +kernel`, and all three transport facts are axiom-free.
The unchanged public `one value per key` law is definitionally the checked
family's entry1. The source theorem is:

```
bapa_sharded_kv_source_law0_holds (rho M)
  (hr : SReach bapa_sharded_kv_source rho M)
  : holdsOver bapa_sharded_kv_source_law0 M [11, 12, 13, 14] rho
```

Full `lake build`, root `lake env lean BapaProof.lean`, and repository axiom gate
all passed. Family/source theorems use only `propext`, `Classical.choice`, and
`Quot.sound`; no sorry, custom axiom, or native_decide. The complete family is
checked by `checkSMachine ... = true := by decide +kernel`.

`models.ts` remains SHA256
`3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76`.
No source changes, no use of immutable tuple target4434fc8d0, no SktSource edits.
The result proves the original source safety **as encoded**; it does not claim
a new unrestricted size/cutoff theorem. Keep `allSizesProven:false`.

Artifacts: `runs/bapa-p4-sharded-progress-source/sharded-progress-source.files/`.
`EMITTED.json` remains its immutable pre-check receipt (`EMITTED_NOT_CHECKED`);
the terminal batch, successful Lean/root logs, axiom gate and hashes establish
the subsequent checked result. `P4-PROGRESS-SOURCE-RESULTS.json` records those
observations, not an invocation of the counted/witness receipt verifier.

Hash-verified after collection:
- BapaProof.lean: `3c09154ed491966c0832c08995887af022907dba837d35e974160e458fb8e8db`
- EMITTED.json: `b90f7881ec65f60c34d1b19a2e5dd32f1febf2f0015ee5130b23ae876e7358e7`
- lean.log: `187451e57d016182befa78ae42970f560c0b1ab6d9a4401e275e977458dda0c8`

Commitlint for the report commit passed in the same remote job. Both original
owners are terminal and collected; no live job or waiter remains.
