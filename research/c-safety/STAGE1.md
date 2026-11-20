# Stage 1 C Memory & UB Safety (`feat/c-safety`)

Stage 1 delivers opt-in defensive C memory and undefined-behavior (UB) safety verification over fixed-size C arrays, constant lookup tables, signed integer overflow, and division/remainder faults, backed by an explicit first-fault monitor, independent kernel proof checking (`checkLaws` / `checkKInduction`), Lean 4 `decide +kernel` recheck, and native ASan/UBSan counterexample replay.

- **Branch**: `feat/c-safety` (base `913afb4a8`)
- **Frozen Stage 1 code commit**: `35b51fca85a2c0476b035abc3725239c90f8fef0` (`35b51fca8`)
- **Trusted kernel / Lean files modified**: `0` (`kernel/`, `lean-kernel/*.lean`, and `bend2/bend.ts` untouched)

---

## 1. Opt-In Contract & Default-Path Preservation

C safety mode is strictly opt-in via any of:

- Source directive: `// gdp: safety` or `/* gdp: safety */`
- CLI flag: `--safety`
- Programmatic API: `extractC(file, { ..., safety: true })`

CLI exit codes in safety mode (`core/cli.ts`):

| Status | Meaning | CLI exit |
|---|---|---|
| `proven` | Every tracked site proved clear by the kernel and re-verified via `verifyCSafetyProof` (`checkLaws` / `checkKInduction`) bound to the exact safety machine and target laws | `0` |
| `broken` | Reachable counterexample trace found **and** replayed natively under Clang ASan/UBSan (`-fsanitize=address,undefined -fsanitize-recover=all`, `-fstrict-flex-arrays=3` when supported) with actual sanitizer diagnostics | `1` |
| `unproven` | Supported subset, but neither proven within budget nor reproduced with native sanitizer output (never reported as `proven` or `broken`) | `2` |
| `unchecked` | Input leaves the covered Stage 1 C subset or fails strict pre-lowering/site-accounting/declarator checks | `2` |

Without opt-in, `extractC` and `gdp check` leave the default C extraction and verification path unchanged (`rule.safety === undefined`).

---

## 2. First-Fault Monitor Architecture & Covered Subset

### 2.1 First-Fault Semantics (`core/c/safety.ts`, `core/extract-step.ts`, `core/extract-go.ts`)

1. **Pre-lowering site inventory (`core/c/reader.ts:1295-1314`, `core/extract-go.ts:55,663-675,713-720`)**:
   - Before lowering, `readC(..., safety=true)` validates every selected method and constructor, inventories every typed array/table bounds, signed overflow, and division/remainder site into `GoFunc.safetySites` with stable source positions, and refuses uncovered constructs (`while`/`for`/`do`/`switch`/`goto`, unsequenced state-mutating calls or unsequenced faulting subexpressions, multi-declaration globals, adjusted/VLA/macro parameter declarators, non-covered widths, opaque calls).
   - During lowering (`core/extract-step.ts:277-315`), every site cut records its ID in `safetyCutSites`; genuinely unreachable prefixes (e.g. `if (0)`, short-circuited RHS, statements after `return`) are explicitly marked in `safetyDeadSites`. `readGo` fails closed with `Refusal` if any pre-registered ID is neither cut nor accounted for as dead.
2. **Prefix-ordered first-fault cuts**:
   - Each site evaluates under its exact defined prefix (after evaluating operands on the live path), records its violation predicate, and continues normal execution **only** on the complement of the fault.
   - `monitorCSafety` (`core/c/safety.ts:93-132`) introduces sticky boolean alarm state variables (`cSafetyAlarm1`, ...) initialized to `false` (statically `I.F` sites emit explicit `r.law(..., () => all())` targets rather than dead state variables).
   - On any fault hit (or when an alarm is already set), ordinary state variables, return/out-parameter slots, and fixed-array writes stutter at event-entry values; the fault transition is admitted under the C input type domain `domain` **even when a later configured normal refusal (`fails`) would otherwise reject the step**. Out-of-domain inputs remain refused (`!domain`).
3. **Exact intermediate C arithmetic (`core/extract-step.ts:2506-2540, 3670-3760`, `core/extract-print.ts:245-286`, `core/extract.ts:291,394-410`)**:
   - Signed `+`, `-`, `*` check the exact mathematical result against the promoted C operation type bounds; `/` and `%` both check divisor `!= 0` and exclude `INT_MIN / -1` and `INT_MIN % -1` before constructing quotient/remainder values.
   - `safetyBounds` preserves narrow intervals across value-preserving promotions and joins, uses `BigInt` intermediate bounds to reject unrepresentable JS-rounded ranges (`> 2^53 - 1`), and linearizes single-wrap unsigned arithmetic (`safetyWrapUnsigned`).
   - Natural-valued `modk` and `mul` terms are wrapped in `Int.of(...)` whenever requested as an integer receiver (`core/extract-print.ts:247-284`), and branch-guarded `modk` terms are not hoisted out of their guards (`core/extract.ts:394-405`).
4. **Independent kernel verification (`core/c/safety.ts:134-366`)**:
   - `proveCSafetyTarget` tries direct `proveLaws`, then a generic scalar-bounds Houdini pass (`tryScalarBoundsProof`, pre-filtered by short concrete reachable walks on the compiled machine so false bounds are eliminated before calling the kernel), then `proveRule` invariant search and `k`-induction fallback.
   - Every `proven` verdict requires `verifyCSafetyProof(machine, targetLaws, bundle)` to succeed using `checkLaws` or `checkKInduction` bound to the exact safety machine and exact target laws (`sameSafetyMachine` + `hasAllTargets`). Tampered, missing, or mismatched proofs are rejected.
5. **Native ASan/UBSan replay (`core/c/safety.ts:382-488`)**:
   - Every counterexample run (including deterministic C scalar endpoint probes from `probeBoundaryFault` for nonlinear faults such as `uint16_t * uint16_t`) is compiled with Clang `-O0 -g -fno-omit-frame-pointer -fsanitize=address,undefined -fsanitize-recover=all` (and `-fstrict-flex-arrays=3` when supported) and executed with no shell interpolation (`spawnSync` + temp JSONL files).
   - An obligation is marked `broken` **only** if the harness builds cleanly and produces actual ASan/UBSan runtime diagnostics; otherwise it stays `unproven`.

### 2.2 Checked Premises vs. Remaining Assumptions

A `proven` Stage 1 verdict establishes absence of a **first** tracked array/table-bounds, signed-overflow, or division/remainder fault over the selected C methods. Below is the exact boundary between what Stage 1 **mechanically checks** and what **remains an explicit assumption** (also returned verbatim on every `CSafetyResult.assumptions`):

#### Mechanically checked by Stage 1

| Premise | Enforcement |
|---|---|
| **Translation-unit function & state closure (closed-TU coverage, narrowed `methods`, bodyless prototypes & globals)** | Every function with a body in the translation unit (and project headers under `root`) must be covered as a selected method or an inlined file-local `static` helper; any other function body (narrowed-out functions, non-first-parameter functions, by-value receivers, free functions, unused `static` helpers, `void *`/pointer callbacks) is refused as `unchecked`, named in `uncheckedFunctions` and the verdict output, and exits `2`. Every verdict explicitly reports `coveredFunctions` (and `coveredHelpers`). Bodyless external prototypes referencing the entry struct (anywhere in the TU) or taking pointers/non-scalars/variadics/K&R arguments (in project files), plus `extern`, pointer/function-pointer, and entry-typed globals, are also refused (`core/c/reader.ts`, `core/c/safety.ts`, `core/cli.ts`). |
| **State-preserving configured failure paths (`fails`)** | `onError: 'discard'` is refused in safety mode (`core/extract-c.ts`, `core/extract-go.ts`); every configured `fails` return path runs `Stepper.unwritten()` and is refused as `unchecked` if any state write occurred prior to returning. |
| **Globals linkage chain (`previousDecl`) & `InitListExpr` `array_filler`** | Any modeled global or constant lookup table with multiple declarations in its linkage chain is refused as `unchecked`. Partial and designated constant-table initializers (`array_filler`) are read in Clang's exact semantic order (and explicit narrowing/sign-changing casts in table initializers are refused). |
| **Parameter declarators & types** | Adjusted arrays, VLAs, typedef-arrays, macro-spelled declarators, `volatile`/`_Atomic`, bitfields, and unsupported scalar widths (`> 32` bits) are refused as `unchecked`. |
| **Pre-lowering site inventory & accounting** | Every tracked site is inventoried before lowering and frozen; `readGo` fails closed if any site is neither cut nor accounted for as dead. |
| **Kernel proof binding & site-matched replay** | Every `proven` verdict passes `verifyCSafetyProof` (`checkLaws` / `checkKInduction`) bound to the exact safety machine (`primitiveFailure`, `params`, `inputs`, `state`, `maps`, `pre`, `assume`, `step`, `history`, `sums`, `inputMaps`, `counts`, `leasts`, `fns`, `facts`) and target laws. Every `broken` verdict requires ASan/UBSan replay with `built && reports.length > 0 && matchedSite`. |
| **In-source `gdp: safety` non-override & comment syntax** | `gdp: safety` is recognized in standalone, inline, multiline, case-insensitive, punctuation-bounded, and trailing-text C comments (ignoring string/char literals and C23 digit separators like `1'000`). Lookalike comments (such as `// gdp: safe` or `// gdp: safety = false`) emit a visible warning in both TEXT and JSON output and exit `2`. A `gdp.toml` setting `safety = false` (top-level or per-rule) is refused with exit `2` rather than silently disabling safety checking (`core/cli.ts`). |

#### Remaining explicit assumptions (NOT checked by Stage 1)

1. **Out-parameter aliasing**: Callers pass valid, non-null, non-aliasing pointers for the receiver and every scalar out-parameter (no out-parameter aliases the receiver, any of its fields, any global, or another out-parameter).
2. **Zeroed start & live ownership**: Struct receivers start zero-initialized (live, valid, and properly aligned), or single-declaration file-local `static` globals start from their C initialization; execution is sequential (no concurrency, interrupts, or signal handlers mutating state).
3. **Other translation units & external linkage**: No code in another translation unit (or linked binary, FFI, or inline assembly outside the checked TU) mutates the struct/globals or holds aliased pointers to them.
4. **ABI & first-fault scope**: Clang target uses 8-bit `char`, 16-bit `short`, 32-bit `int`, and two's-complement signed integers. Only the first tracked array/table-bounds, signed-overflow, or division/remainder fault is checked; fixed-array bounds proofs cover accesses to known live arrays of static extent (not general heap lifetime, pointer provenance, loops, or recursion). Abstract stutter on fault is a monitor convention and does **not** claim native C rolls back prior writes.

### 2.3 Default-Path Fixes Carried by Stage 1

While C safety verification itself is strictly opt-in (`// gdp: safety`, `--safety`, `{safety: true}`), five bug fixes also apply to the default extraction path (and should be listed under `Fixed` in the release changelog):

1. `core/extract-print.ts`: Wrap natural-valued `mul` and `modk` expressions in `Int.of(...)` when printed as a signed integer receiver (`!nat && recv`), preventing signed subtraction from lowering to saturating `Term.minus`.
2. `core/extract.ts`: Skip hoisting branch-guarded `modk` expressions whose dividend is not unconditionally non-negative, matching `mul`.
3. `core/c/reader.ts` (`parseT`): Do not treat pointer/array typedefs to structs (`typedef struct ring *ring_ptr;`) as bare struct values.
4. `core/c/reader.ts` (`initListChildren`, `table`, `constTableOf`, `isAllZeroInit`): Read Clang JSON `InitListExpr` `array_filler` elements in semantic order (and refuse non-`InitListExpr` / unsupported fillers) instead of reading partial and designated constant tables as all zeros.
5. `core/law-answer.ts`, `core/laws.ts`, `core/native-law.ts`, `core/extract-c.ts`, `core/extract-go-check.ts`: Validate keyed constant-argument C answers against actual native observations (`d5e9e2535`).

---

## 3. Independent Astra Soundness Review — Blocker Discharge

Prior to Stage 1 completion, an independent read-only audit by `gpt-6.2-astra` (`MAIN-INBOX.md` lines 12378–12383 and `lane-receipts/csafety/2026-11-18/semantics.md`) withheld a C-level verdict pending five concrete blockers/obligations. Every item was fixed in code and covered by dedicated tests and negative mutant controls in `core/extract-c-safety.test.ts`:

| # | Astra Finding | Code Fix | Verification & Negative Control |
|---|---|---|---|
| **1** | **Globals linkage chain (`previousDecl`)**: tentative `VarDecl` referenced by a function while a later unreferenced `VarDecl` supplied a nonzero initializer caused the model to start at `0`. | `core/c/reader.ts:156,185-195,469,991` tracks `globalByName` / `previousDecl` across the whole TU and populates `redeclaredGlobals`, refusing any modeled global or constant table with multiple declarations in its linkage chain. | `core/extract-c-safety.test.ts:314-341` (`Astra Finding 1`): exact tentative + later `static int idx = 10` fixture -> `unchecked`; single-decl in-range -> `proven`; single-decl out-of-range (`idx = 8`) -> `broken` + UBSan `index 8 out of bounds`. |
| **2a** | **Receiver / parameter declarators**: adjusted array, VLA, typedef-array, and macro-spelled receiver declarators could hide entry evaluation outside the body. | `core/c/reader.ts:945-985,1233-1240` (`validateParamDecl`, `validatePointerTypedef`) rejects adjusted array, VLA, typedef-array, and macro-expanded declarators (allowing `<stdbool.h>` `bool` and plain pointer typedefs via `parseT`). | `core/extract-c-safety.test.ts:345-374` (`Astra Finding 2a`): rejects `struct ring r[1]`, `struct ring r[static 1]`, `typedef struct ring ring_arr[1]`, and `#define BAD_RECV struct ring r[1]` as `unchecked`; positive control `typedef struct ring *ring_ptr` proves clear. |
| **2b** | **Pre-lowering site inventory & accounting**: partial inventories were unchecked if a site was dropped or never cut during lowering. | `core/c/reader.ts:1295-1314`, `core/extract-step.ts:277-315`, `core/extract-go.ts:55,663-675,713-720`: pre-lowering `GoFunc.safetySites` inventory; every ID must appear in `safetyCutSites` or `safetyDeadSites`, else `readGo` throws `Refusal`. | `core/extract-c-safety.test.ts:376-417` (`Astra Finding 2b`): dead branch / short-circuit RHS / post-return sites prove clear; Mutant A (dropped lowered stmt) and Mutant B (unmatched pre-registered ID) both throw `Refusal`. |
| **3** | **Natural `modk`/`mul` in signed int receiver & `safetyBounds` widening**: non-hoisted `modk` or natural products returned `Term` so signed subtraction called saturating `Term.minus`; widening lost narrow intervals. | `core/extract-print.ts:247-284` wraps natural `modk`/`mul` in `Int.of(...)` when `!nat && recv`; `core/extract.ts:394-405` skips hoisting branch-guarded `modk`; `core/extract-step.ts:1097,2506-2540,3670-3760` preserves intervals across widening/joins and bounds products via `BigInt`. | `core/extract-c-safety.test.ts:421-488` (`Astra Finding 3`): concrete signed `(x % 8u) - b` oracle (`10 % 8 - 5 = -3 < 0`, inline, hoisted, and in branch guard), `uint8_t * uint8_t - uint8_t` proven with negative difference `-4`, unguarded `uint16_t * uint16_t` -> `broken` + UBSan `signed integer overflow`, guarded `<= 46340u` -> `proven`. |
| **4 & 5** | **Lowered + monitored + printed machine Boolean path table & independent `checkLaws` binding**: verify the real emitted machine against an exhaustive path table and bind `checkLaws` with tamper controls. | `core/c/safety.ts:93-176,300-366,492-574` (`monitorCSafety`, `sameSafetyMachine`, `hasAllTargets`, `verifyCSafetyProof`, joint proof assembly). | `core/extract-c-safety.test.ts:492-604` (`Astra Integration`): 32-row exhaustive path table (`priorAlarm × flag × idx × fail`, plus out-of-domain `int32` refusal) checking `allowed`, sticky alarm, old scalar, nondefault return, both fixed array cells and length; tamper controls reject `undefined`, emptied `trees: {}`, missing target law, and altered `machine.assume`. |

> **Review re-invocation note**: Attempting a follow-up read-only audit via `pi --model gpt-6.2-astra` returned an external provider content-policy refusal (`This content was flagged for possible cybersecurity risk`, the same false positive noted in `brief-neon-csafety.md` for C memory-safety prompts). We did not attempt to bypass it; instead every prior Astra finding was audited line-by-line and verified mechanically by the test controls above.

---

## 4. Ring Buffer & Bounds-Check Corpus Results

All 18 tests in `core/extract-c-safety.test.ts` and 3 tests in `research/c-safety/first-fault.test.ts` passed natively on boat (`35b51fca8`, batch `20261120-083946-l0c7cq`, 120/120 across 5 C/CLI/observation suites):

### 4.1 Eight-Slot Ring Buffer (`brief-csafety.md`)

| Case | Result | Verification / UBSan Replay |
|---|---|---|
| Guarded `% N` wrap (`rb_put` + `rb_get`, `N = 8`) | `proven` | `verifyCSafetyProof` (`checkLaws`) = `true` |
| Guarded `& (N - 1)` wrap (`rb_put` + `rb_get`, `N = 8`) | `proven` | `verifyCSafetyProof` (`checkLaws`) = `true` |
| Off-by-one `rb_set` (`if (i > N)`) | `broken` (`rb_put` proven, `rb_set` broken) | UBSan: `rb.c:5:...: runtime error: index 8 out of bounds for type 'uint8_t[8]'` (`matchedSite: true`) |
| Search-found head reset bug (`r->head = r->head + 1; if (r->head > N) r->head = 0;`) | `broken` (`rb_get` proven, `rb_put` broken) | Multi-step trace (`>= 10` requests) replayed under UBSan: `rb.c:4:...: runtime error: index 8 out of bounds for type 'uint8_t[8]'` (`matchedSite: true`) |

### 4.2 Bounds-Check Corpus & Off-by-One Mutants (0 False Positives, 14/14 Mutants Caught)

| Corpus Item | Unmutated | Off-by-One Mutants Tested | Mutants Flipped to `broken` + UBSan `matchedSite` |
|---|---|---|---|
| `ring-buffer-mod8` | `proven` (`checkLaws` = `true`) | 3 (`i > N`, `% (N + 1)` on `head`, `% (N + 1)` on `tail`) | 3 / 3 |
| `ring-buffer-mask16-helpers-outparam` | `proven` (`checkLaws` = `true`) | 2 (`idx > N`, `head & 31`) | 2 / 2 |
| `bounded-signed-stack` | `proven` (`checkLaws` = `true`) | 3 (`top > 6`, `idx > 6`, `idx < -1`) | 3 / 3 |
| `const-table-1d-2d` | `proven` (`checkLaws` = `true`) | 4 (`weights` `i > 4`, `i < -1`; `grid` `r > 2`, `c > 4`) | 4 / 4 |
| `globals-mode-fixed-array` | `proven` (`checkLaws` = `true`) | 2 (`read_at` `i > 4`, `write_cur` `cursor > 4`) | 2 / 2 |
| **Total** | **5 / 5 proven (0 FP)** | **14 mutants** | **14 / 14 broken + UBSan at site** |

Additional arithmetic/ordering controls verified with UBSan replay: `INT_MIN % -1` before a later configured refusal (`division of -2147483648 by -1 cannot be represented in type 'int'`), signed overflow (`signed integer overflow`), first-fault division ordering (`n / 0` broken with `division by zero`, subsequent `value % -1` proven unreachable as first fault), and CLI opt-in exit codes (`0` / `1` / `2` + default path unchanged).

---

## 5. Lean 4 `decide +kernel` Recheck

`research/c-safety/export-stage1.ts` exports real proven Stage 1 C safety machines (`c_stage1_ring`: 5 sites, 15 laws + Euclidean `divBy`/`modBy` facts; `c_stage1_lut`: 1 site, 4 laws) via `smachineToLean`, `seedStepProof`, and `leanProject`, alongside the isolated first-fault model in `research/c-safety/first-fault.ts` (`c_safe_bounds`).

Built on boat under Lean `4.34.0` (`20261120-083946-l0c7cq`, `lean-recheck`, exit 0, 56.51 s):

- `c_stage1_ring_laws`: `[propext, Classical.choice, Quot.sound]`
- `c_stage1_ring_facts_hold`: `[propext, Quot.sound]`
- `c_stage1_lut_laws`: `[propext, Classical.choice, Quot.sound]`
- `c_safe_bounds_laws`: `[propext, Classical.choice, Quot.sound]`
- Forbidden axioms (`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`): **none (`0`)**.

---

## 6. Exact-Commit Gate Receipts

Every code gate below ran remotely on Boat (image `sc-f0d8daeee6c3`, pinned `node=v24.22.1`, `bun=1.4.3`, `clang=21.0.0`, `lean=4.34.0`) against exact frozen Stage 1 code commit **`35b51fca85a2c0476b035abc3725239c90f8fef0`** (`35b51fca8`):

| Gate | Commit SHA | Boat Batch ID | Result |
|---|---|---|---|
| `tsc -p .`, `tsc -p tsconfig.build.json --noEmit`, `oxlint --type-aware --deny-warnings --disable-nested-config`, commitlint & scope | `35b51fca8` | `20261120-083848-fmpcel` | **PASS** (exit 0, 128.81 s; 0 warnings / 0 errors on 2,493 files; 5/5 commits valid; 21 changed files, 0 forbidden) |
| Overfit scanner (`772706d94:gates/overfit.ts`) | `35b51fca8` | `20261120-083927-e4hrbn` | **PASS** (exit 0, 18.62 s; `0 FAIL`, 92 pre-existing `WARN`, 5,530 files) |
| C safety + C reader + CLI + native observations (`extract-c-safety`, `first-fault`, `extract-c`, `cli`, `native-observations`) | `35b51fca8` | `20261120-083946-l0c7cq` | **PASS** (exit 0, 359.99 s; **120 pass, 0 fail**, 1,486 `expect()` calls) |
| Lean 4 `decide +kernel` recheck (`export-stage1.ts` + `first-fault.ts`) | `35b51fca8` | `20261120-083946-l0c7cq` | **PASS** (exit 0, 56.51 s; standard axioms only, 0 forbidden axioms) |
| Full repository 7-shard test suite (`scripts/test-shards.ts --shard 1/7..7/7`) | `35b51fca8` | `20261120-084011-zaxiih` | **PASS** (**7/7 shards exit 0**, 0 failed tests; 271.5–586.6 s per shard) |
| Paired IC3Syn 29 + DuoAI 10 corpus (`913afb4a8` vs `35b51fca8`, alternating same-VM order) | `35b51fca8` | `20261120-084057-bl2qfg` | **PASS** (**4/4 jobs exit 0**; IC3Syn 29/29 unchanged, DuoAI 10/10 unchanged, **0 reproducible losses**) |

> Note on Boat preflight toolchains: Boat's worker pool reported mixed preflight `/usr/bin/node` versions on a subset of VMs (`toolchain.json`), so every job script explicitly resolved and prepended pinned `node=v24.22.1` to `PATH` and logged `node=v24.22.1 bun=1.4.3` before executing any command.
