# C safety (Stage 1)

See [`STAGE1.md`](./STAGE1.md) and [`docs/FRONTENDS.md#opt-in-c-safety-stage-1`](../../docs/FRONTENDS.md#opt-in-c-safety-stage-1) for the Stage 1 C memory & UB safety implementation summary, the four stated assumptions and mechanically checked premises (ABI/types, ownership/zeroed start/aliasing, closed-TU function coverage with explicit `coveredFunctions`/`uncheckedFunctions` reporting, bodyless prototypes, globals, and `fails` paths, first-fault/replay scope), independent soundness-review fixes, bounds-check corpus & UBSan replay results, Lean 4 recheck axioms, and exact-commit Boat gate receipts.

## Research & Lean export scripts

- `export-stage1.ts` runs `extractC(..., {safety: true})` on proven Stage 1 C programs (`c_stage1_ring`, `c_stage1_lut`), verifies their captured kernel proofs with `verifyCSafetyProof`, and emits a self-contained Lean 4 project using `decide +kernel`:

```sh
bun research/c-safety/export-stage1.ts /path/to/stage1-project
(cd /path/to/stage1-project && lake build)
```

- `first-fault.ts` and `first-fault.test.ts` independently check the abstract first-fault monitor properties (ordering, non-masking by later refusal, stutter framing, absorption, and fixed-width `TRAP` semantics) and export the standalone guarded cursor model to Lean:

```sh
bun test research/c-safety/first-fault.test.ts
bun research/c-safety/first-fault.ts /path/to/first-fault-project
(cd /path/to/first-fault-project && lake build)
```
