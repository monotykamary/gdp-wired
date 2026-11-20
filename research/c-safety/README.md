# C safety (Stage 1)

See [`STAGE1.md`](./STAGE1.md) and [`docs/FRONTENDS.md#opt-in-c-safety-stage-1`](../../docs/FRONTENDS.md#opt-in-c-safety-stage-1) for the Stage 1 C memory & UB safety implementation summary, the four stated assumptions and mechanically checked premises (verified native Clang from fixed safe `PATH` reported as absolute `compilerPath`, closed-world allowlisted env, ABI/types/target/std/`-I`/`-D`/`macroConfig`, ownership/zeroed start/aliasing, path-only system-header boundary via `clang -E -v` + spelling+expansion check + macOS `/opt/homebrew/include` default search-list caveat + refusal of user macros expanded in system headers + closed-world user preprocessor allowlist refusing predefined/undefined-elsewhere macros, `__has_*`, `_Pragma`, non-`once` `#pragma`, token pasting `##`, and invocation-dependent macros `__FILE__`/`__LINE__`/`__DATE__`/`__TIME__`/`__COUNTER__`/etc. + token-stream invariance as a second check + closed-TU coverage across all non-system files, symbol aliases/weak/asm exports, struct-field fn-ptrs, bodyless prototypes, and `fails` paths, first-fault/replay scope), independent soundness-review fixes, bounds-check corpus & UBSan replay results, Lean 4 recheck axioms, and exact-commit Boat gate receipts.

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
