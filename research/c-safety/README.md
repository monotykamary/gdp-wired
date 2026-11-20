# C safety (Stage 1)

See [`STAGE1.md`](./STAGE1.md) and [`docs/FRONTENDS.md#opt-in-c-safety-stage-1`](../../docs/FRONTENDS.md#opt-in-c-safety-stage-1) for the Stage 1 C memory & UB safety implementation summary, the four stated assumptions and mechanically checked premises (verified native Clang from fixed safe `PATH` reported as absolute `compilerPath`, `libc` version, `userFilesSha256` + `userFiles` list, `systemHeadersSha256` + `systemHeaders` list, closed-world allowlisted env and flags, ABI/types/target/std/`-I`/`-D`/`macroConfig`, ownership/zeroed start/aliasing, path-only system-header boundary via `clang -E -v` + spelling+expansion check + macOS `/opt/homebrew/include` default search-list caveat + closed-world regular-file user-include boundary under root/`-I` refusing `/proc`/`/dev`/`/sys` + refusal of user macros expanded in system headers + Clang-native byte-contiguous `-dump-raw-tokens` (`0..EOF`)/`-dump-tokens`/`-E -H -dD` closed-world user preprocessor & `__builtin_*` allowlist refusing NUL bytes, trigraphs, non-C23 digit-quote, predefined/undefined-elsewhere macros, `__has_*`, `_Pragma`, non-`once` `#pragma`, token pasting `##`, `<scratch space>` expansions, `SourceLocExpr`/`PredefinedExpr`, `__builtin_*`, and invocation-dependent macros `__FILE__`/`__LINE__`/`__DATE__`/`__TIME__`/`__COUNTER__`/etc. + lexer-independent differential token AND folded-AST-fact path-length/empty-`cwd`/`stdin=/dev/null`/`SOURCE_DATE_EPOCH`/build-mode checks + closed-TU coverage across all non-system files, symbol aliases/weak/asm exports, struct-field fn-ptrs, bodyless prototypes, and `fails` paths, first-fault/replay scope), independent soundness-review fixes, bounds-check corpus & UBSan replay results, Lean 4 recheck axioms, and exact-commit Boat gate receipts.

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
