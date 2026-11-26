# Emitting Standalone Proven TypeScript Source (`gdp-wired emit`)

Branch: `feat/emit-source` (base `origin/main` `6116b4c02`).
Trusted code diff (`kernel/kernel.ts`, `kernel/cyclic.ts`, `core/check.ts`, `lean-kernel/`): **0 lines changed**.
Reader / docs diff (`core/extract-shapes.ts`, `core/extract-read.ts`, `skills/`): **0 lines changed** (reverted to `origin/main`).

---

## Phase 1: Emitted Source, Differential `--verify`, Half-Even Decimals, and Repo-Root Provenance

### 1. Public API & CLI

- **Library API** (`gdp-wired` and `gdp-wired/emit`, zero new runtime dependencies):
  - `rule.emit(opts?)` / `emitRule(rule, opts?)` -> `EmitResult` (`{source, digest, version, name, kind, exportName, laws, allProven}`)
  - `fun.emit(opts?)` / `emitFun(fun, opts?)` -> `EmitResult`
  - `ratRule.emit(opts?)` / `emitRatRule(ratRule, opts?)` -> `EmitResult`
  - `chart.emit(opts?)` / `emitChart(chart, opts?)` -> `EmitResult`
  - `decimal(places, {round: 'half-even'})` (optional rounding mode on `decimal(places)` in `core/dsl.ts`; omitted option keeps exact throwing behavior unchanged)
  - Helper exports on `gdp-wired/emit`: `GDP_WIRED_VERSION`, `machineDigest`, `qMachineDigest`, `sha256Hex`, `EmitBundle`, `EmitResult`, `EmitProvenance`.
  - Refuses unproven rules/laws or empty law lists by throwing `Unproven` (unless `allowUnproven: true` is passed internally for diagnostics).
- **Emitted Module Shape**:
  - Zero imports, zero `require`, zero `new Function` / `eval`, zero proof/kernel runtime.
  - Header opens with provenance and repo-root-relative regeneration command (resolved via nearest `.git` ancestor, falling back to `cwd`), followed by rule name, canonical `sha256:...` machine digest, exact arithmetic semantics, and every proven law with its proof status (no `// gdp: law` comments, no runner class).
  - `Rule` / `Chart`: `export type Params`, `export type Input`, `export type State`, `export function init(params: Params): State`, `export function step(params: Params, state: State, input: Input): State`.
  - `Fun`: `export type Params` (when present), `export type Input`, `export type Result`, optional `export function defaultParams(): Params`, and one clean `export function <name>(args: Input[, params: Params]): Result` with shared output subterms CSE-bound (e.g. `const decision = ...; const final = ((decision === "review") ? args.secondOpinion : decision)`).
  - `RatRule`: exact BigInt reduced pairs (`export type Rat = readonly [bigint, bigint]`, `RatInput`, `Params`, `Input`, `State`, `toRat`, `formatRat`, `init`, `allowed`, `step`), zero floating-point rounding.
- **CLI** (`npx gdp-wired-cli emit <module>#<export> [--out <file.ts>] [--check] [--verify] [--laws <export>] [--step-laws <export>] [--name <ident>] [--from any] [--ms <n>] [--json]`):
  - Exit `0`: emitted (and matched disk byte-for-byte under `--check`, and passed differential `--verify`).
  - Exit `1`: `--check` drift/missing file (prints short line-numbered diff) or `--verify` differential mismatch (prints failing input/trace).
  - Exit `2`: unproven rule/law (never writes `--out`), missing export, bad arguments, or module load failure.
- **Differential `--verify`** (`core/emit-cli.ts:verifyEmittedFile`):
  - Applies to every target kind (`Rule`, `Fun`, `RatRule`, `Chart`) with zero TypeScript-reader dependency.
  - Dynamically imports the emitted file and differentially tests it against the rule's interpreter (`fun.run()`/`rule.interpreter()`/`interpretQ()`): exhaustive on small finite domains (up to 4,096 inputs), plus randomized & boundary sweeps and explicit error/refusal/rounding parity probes (more decimal places, exact halves, negatives, exponent forms, out-of-range, `NaN`).

### 2. Opt-In Half-Even Decimal Rounding (`decimal(places, {round: 'half-even'})`)

- Implemented in `core/decimal-round.ts` (`scaleDecimalHalfEven` + `DEC_ROUND_HELPER_LINES`), shared by `encodeInput` (`core/dsl.ts`) and emitted `$decRound` (`core/emit.ts`).
- Without `{round: 'half-even'}`, `decimal(places)` is unchanged and throws `RangeError` on values needing more than `places` decimal places (e.g. `0.73219` or `0.00005` on `decimal(4)`), identically in `encodeInput` and emitted `$dec`.
- With `{round: 'half-even'}`, both `encodeInput` and emitted `$decRound` parse the number's shortest IEEE-754 round-trip string (`String(x)`, including scientific notation like `1e-7`, `5e-5`, `1.5e-4`, `-2.5e-4`), shift and round half-even purely on decimal digit strings (zero float multiplication), normalize `-0` to `0`, and check safe integer bounds.
- Emitted header explicitly states: `inputs rounded half-even to 10^-4; laws hold for the rounded values`.
- Verified on exact halves (`0.00005 -> 0`, `0.00015 -> 0.0002`, `0.00025 -> 0.0002`, `0.00035 -> 0.0004`, `0.99995 -> 1`), more-places values (`0.73219 -> 0.7322`), negatives (`-0.00005 -> 0`, `-0.00015 -> -0.0002`, `-0.00025 -> -0.0002`), exponent forms (`1e-7 -> 0`, `5e-5 -> 0`, `1.5e-4 -> 0.0002`, `2.5e-4 -> 0.0002`), and differential `--verify` sweeps.

### 3. Sample Emitted Outputs

#### Synthetic Decision Example (`examples/review-routing.generated.ts`)

```ts
// Generated by gdp-wired 0.61.0 from examples/review-routing.ts#reviewRoutingBundle. Do not edit.
// To change behavior, edit the model and its laws, then run from the repository root: npx gdp-wired-cli emit examples/review-routing.ts#reviewRoutingBundle --out examples/review-routing.generated.ts
// Pure rule: review routing
// Digest: sha256:46a6ff00160ffe66258a8175fd09e050abb62b765a25fea19c23f7de2fe68778
// Arithmetic: exact scaled fixed-point integers (10^-4); inputs rounded half-even to 10^-4; laws hold for the rounded values; safe integer range <= 2^53 - 1
// Proven laws:
//   - [decision] tamper suspected always rejects: proven, kernel-checked
//   - [decision] age concern at or above limit always rejects: proven, kernel-checked
//   - [decision] high risk always rejects: proven, kernel-checked
//   - [decision] approval requires clean safety checks and signal: proven, kernel-checked
//   - [decision] escalation never turns reject into approve: proven, kernel-checked

export type Params = {
  readonly approveAt: number
  readonly clearRisk: number
  readonly blockRisk: number
  readonly rejectAt: number
  readonly ageLimit: number
}

export type Input = {
  readonly relevance: number
  readonly risk: number
  readonly ageConcern: number
  readonly tamperSuspected: boolean
  readonly explicitRequest: boolean
  readonly secondOpinion: "approve" | "reject" | "review"
}

export type Result = {
  readonly decision: "approve" | "reject" | "review"
  readonly final: "approve" | "reject" | "review"
}

// ($dec for strict decimal(4) params and $decRound for half-even decimal(4) inputs omitted here; full file in examples/review-routing.generated.ts)

export function defaultParams(): Params {
  return {
    approveAt: 0.55,
    clearRisk: 0.35,
    blockRisk: 0.75,
    rejectAt: 0.15,
    ageLimit: 0.45,
  }
}

export function reviewRouting(args: Input, params: Params = defaultParams()): Result {
  if (!(args.secondOpinion === "approve" || args.secondOpinion === "reject" || args.secondOpinion === "review")) throw new RangeError("review routing: invalid input")
  const $p_approveAt = $dec(params.approveAt, 4, 10000, "approveAt")
  const $p_clearRisk = $dec(params.clearRisk, 4, 10000, "clearRisk")
  const $p_blockRisk = $dec(params.blockRisk, 4, 10000, "blockRisk")
  const $p_rejectAt = $dec(params.rejectAt, 4, 10000, "rejectAt")
  const $p_ageLimit = $dec(params.ageLimit, 4, 10000, "ageLimit")
  const $a_relevance = $decRound(args.relevance, 4, "relevance")
  const $a_risk = $decRound(args.risk, 4, "risk")
  const $a_ageConcern = $decRound(args.ageConcern, 4, "ageConcern")
  if (!(((0 <= $a_relevance) && ($a_relevance <= 10000) && (0 <= $a_risk) && ($a_risk <= 10000) && (0 <= $a_ageConcern) && ($a_ageConcern <= 10000)))) throw new RangeError("review routing: input violates assumption")
  const decision: "approve" | "reject" | "review" = (args.tamperSuspected ? "reject" : (($p_ageLimit <= $a_ageConcern) ? "reject" : (($p_blockRisk <= $a_risk) ? "reject" : ((args.explicitRequest && ($a_risk < $p_clearRisk)) ? "approve" : ((($p_approveAt < $a_relevance) && ($a_risk < $p_clearRisk)) ? "approve" : (($a_relevance < $p_rejectAt) ? "reject" : "review"))))))
  const final: "approve" | "reject" | "review" = ((decision === "review") ? args.secondOpinion : decision)
  return {
    decision,
    final,
  }
}
```

#### Stateful Rule Sample (README `budget`)

```ts
// Generated by gdp-wired 0.61.0. Do not edit.
// Rule: budget
// Digest: sha256:4e2a2888f8572abaff2ce0de2ec68d3c8178468ef99d8aea717297d486d8ab9a
// Arithmetic: exact JavaScript safe integers over N/Z (truncated natural subtraction max(0, a - b); safe range <= 2^53 - 1)
// Proven laws:
//   - [law] spend stays within b + m: proven, kernel-checked

export type Params = {
  readonly b: number
  readonly m: number
}

export type Input = {
  readonly c: number
}

export type State = {
  readonly s: number
}

export function init(params: Params): State {
  if ((!Number.isSafeInteger(params.b) || params.b < 0) || (!Number.isSafeInteger(params.m) || params.m < 0)) throw new RangeError("budget: invalid params")
  return {
    s: 0,
  }
}

export function step(params: Params, state: State, input: Input): State {
  if ((!Number.isSafeInteger(input.c) || input.c < 0)) throw new RangeError("budget: invalid input")
  const next_s = ((state.s < params.b) ? (state.s + Math.min(input.c, params.m)) : state.s)
  return {
    s: next_s,
  }
}
```

### 4. Phase-1 Verification Results (Boat & Local)

- **Quality / Typecheck / Lint / Build / Exports / Emit Suite** (Boat batch `20261126-220238-2k7hjp`, commit `fa78ca47f`, Bun `1.4.3`, Node `v24.22.1`):
  - `tsc -p tsconfig.build.json --noEmit` + `tsc -p .` outside `research/vendor`: **0 errors**
  - `oxlint --type-aware --deny-warnings --disable-nested-config core/ examples/ scripts/`: **0 warnings, 0 errors (743 files)**
  - `bun run build`: **PASS (`dist: 792 entries`)**
  - `core/exports.test.ts`: **28/28 PASS (260 expect() calls)** — including `./emit` export, zero runtime dependencies, and packed tarball check
  - `core/emit.test.ts`: **15/15 PASS (14,823 expect() calls, 5.28s)** — covering:
    - `Rule` (`budget`, `caps`, `accounts`, `minutes`, `hold`, `seats`, `jobs`, `retry`, `larger`, `room`, `window`, `kinded`)
    - `Fun` (`canEdit` exhaustive 12/12, `approve`, `echoRounded`, `examples/review-routing.generated.ts` 1,520 differential trials + 75 error checks)
    - `RatRule` (`feeSplit`, `limiter`, `ledger` — exact BigInt `[bigint, bigint]` parity vs `interpretQ` and `loadQJs` + differential `--verify`)
    - `Chart` (`order` nested+history, `door` flat — crossCheck + differential `--verify`)
    - `decimal(places, {round: 'half-even'})` exact halves, negatives, exponents, strict default unchanged
    - Repo-root-relative header provenance: byte-identical from repo root vs subdirectory, `--check --verify` PASS from subdirectory
    - CLI `--out`, `--check` (missing -> exit 1, 1-char edit -> exit 1 with short diff), `--verify` -> exit 0, unproven -> exit 2 without writing
    - Emitter mutant refutations via differential `--verify` (all exit `1`): **8/8 refuted** (`reviewRouting` drop-tamper, flip-clearRisk, bad-escalation, half-even->half-up; `echoRounded` half-even->half-up; `budget` drop `Math.min`; `caps` `<` -> `<=`; `feeSplit` `39n/40n` -> `39n/41n`)
    - Hygiene scan: **0 matches** for `\b(import|require|Function|eval)\b` and **0** `// gdp: law` comments in any emitted output
  - `bun examples/review-routing.ts`: **5/5 laws proven + sample run PASS**
  - **Node v24.22.1 CLI note**: running `/opt/node/bin/node dist/core/cli.js emit examples/review-routing.ts#...` failed in Node strip-only mode because `examples/review-routing.ts` imports `../core/dsl.ts` (which uses TS parameter properties). Emitted `.ts` files themselves contain no parameter properties and load in Node 24 strip-only mode; user models importing from `'gdp-wired'` (`dist/core/dsl.js`) also avoid TS parameter properties. (Verified further in Phase 2.)
- **Cross-VM Determinism** (Boat batch `20261126-214218-jpmiyz`, 2 distinct VMs `sc-2e2b3a28-xln5bs03` vs `sc-2e2b3a28-lejf3ti6`, shifted `keyCounter` on box B):
  - **5/5 byte-for-byte identical** across VMs:
    - `budget`: digest `sha256:4e2a2888...`, source SHA `fc330adc...` (1,040 B)
    - `caps`: digest `sha256:e96b7a84...`, source SHA `20710434...` (1,519 B)
    - `accounts`: digest `sha256:06ee2462...`, source SHA `eb4374f4...` (2,148 B)
    - `feeSplit`: digest `sha256:7f5e41ee...`, source SHA `0b58d315...` (3,049 B)
    - `reviewRouting`: digest `sha256:46a6ff00...`, source SHA `9de831f0...` (5,637 B)
- **Full Shards Baseline** (Boat batch `20261126-214218-jpmiyz`):
  - Shards `1/7`, `2/7`, `4/7`, `6/7`, `7/7` **PASS** (5/7); shards `3/7` and `5/7` caught the 3 Phase-1 bugs fixed in `7440e82b5` and `fa78ca47f` (`exports.test.ts` and `emit.test.ts` now both 100% green in `20261126-220238-2k7hjp`). Full 7/7 shards will run once at the end of Phase 2.
- **Private Gitignored Spec Verification** (`private/emit-intent/`, local only, never staged/committed, zero private source/fields/thresholds quoted):
  - Laws proven: **5/5 PASS** (kernel-checked)
  - Differential `--verify`: **PASS** (`1,520` trials, `75` error checks matched, exit `0`, half-even header present)
  - Broken source variants refused with `Unproven`: **3/3 PASS**
  - Emitted mutants refuted by differential `--verify` (exit `1`): **4/4 PASS**
  - Hygiene scan (`\b(import|require|Function|eval)\b`): **0 matches**

### 5. Known Limits / Follow-Ups (Phase 1)

- Quantified runtime flags (`everyKey` / `all` inside `flags`), broadcast `each`-writes on record/variant maps, and fixed-width word-division intrinsics in emitted source (currently handled by `compiled()`/`interpreter()`; unified printer in Phase 2 covers shared expressions/conditions/helpers).
- Docs (`skills/gdp-wired/references/shipping.md`, `skills/gdp-wired/SKILL.md`) intentionally left untouched for Main to author.

---

## Phase 2: One Code Generator & 100% Enforced Expressibility

### 1. Shared Code Generator & Deduplication Architecture

- **`core/codegen.ts` (513 lines)** — single expression, condition, rational, and helper printer shared by `compileJsMode` (`core/machine.ts`), `compileQJs` (`core/rationals.ts`), and `emit` (`core/emit.ts`):
  - `createPrinter(hooks)`: single exhaustive `E` / `C` printer. `compileJsMode` keeps only its encoded slot-binding layer (persistent and in-place modes, `fork`, and its existing `"compileJs takes no tuple key at every key"` refusal); `emit` keeps only its typed named-value binding layer.
  - `createQPrinter(hooks)`: single exhaustive `QE` / `QC` rational printer shared by `compileQJs` (`core/rationals.ts`) and `emitRatRule` (`core/emit.ts`).
  - `JS_RUNTIME` / `runtimeFor` and `renderTypedHelpers`: single helper source for runtime arithmetic/quantifier/collection primitives (`$sub`, `$div`, `$rem`, `$wordDiv`, `$countCells`, `$everyTuple`, `$CountCells`, `$join`, `$sized`, etc.).
  - Compile-time canonical op & machine-part tables: `E_OPS` (12 ops), `C_OPS` (7 ops), `QE_OPS` (11 ops), `QC_OPS` (6 ops), `MACHINE_PARTS` (all 26 `Machine` fields), and `unreachable(x: never): never`.
- **`core/sha256.ts` (50 lines)** — single pure-JS SHA-256 implementation (zero `node:*` imports) used by `core/emit.ts` (`machineDigest`, `qMachineDigest`, `foldDigest`, `loopDigest`) and ready for the hints branch on merge.
- **`core/cli-io.ts` (83 lines)** — shared CLI module loader, flag parser, line diff formatter, and repo-root resolver shared by `core/cli.ts` and `core/emit-cli.ts`.

### 2. Line Counts Before vs After

| File | `origin/main` | Phase 1 (`f53981041`) | Phase 2a dedup (`6e0566994`) | Phase 2 final (`f3fe9de84`) | Notes |
| --- | ---: | ---: | ---: | ---: | --- |
| `core/machine.ts` | 1,525 | 1,525 | 1,453 (-72) | 1,453 (-72) | Delegates `E`/`C`/runtime helpers to `core/codegen.ts` |
| `core/rationals.ts` | 273 | 299 | 286 (-13) | 286 (-13) | Delegates `QE`/`QC` printing to `core/codegen.ts` |
| `core/cli.ts` | 1,481 | 1,483 | 1,466 (-17) | 1,466 (-17) | Shares `core/cli-io.ts` |
| `core/emit-cli.ts` | — | 773 | 540 (-233) | 686 (-87) | Slimmed via `core/cli-io.ts`; +146 for fold/loop/nodes/lists/carries verify |
| `core/emit.ts` | — | 1,903 | 1,735 (-168) | 3,079 | Deduplicated printers & SHA-256, then extended for 100% expressibility + `emitFold`/`emitLoop` |
| `core/codegen.ts` | — | — | 275 | 513 | New shared Machine + Rational printer & runtime helpers |
| `core/sha256.ts` | — | — | 50 | 50 | New shared pure-JS SHA-256 |
| `core/cli-io.ts` | — | — | 83 | 83 | New shared CLI IO/diff/repo-root module |

### 3. 100% Enforced Expressibility

- **Compile-time `never` exhaustiveness**: every switch over `E`, `C`, `QE`, `QC`, `KindInfo`, and `Machine` parts (`E_OPS`, `C_OPS`, `QE_OPS`, `QC_OPS`, `KIND_NAMES`, `MACHINE_PARTS`, `EMIT_MACHINE_PARTS`) terminates in `unreachable(x: never)`. Adding any new AST op, `KindInfo`, or `Machine` property fails `tsc` until `emit` handles it.
- **Zero `'not supported'` refusals**: `grep -n 'not supported' core/emit.ts` returns **0 lines** (asserted both in `core/emit.test.ts` and in the Boat quality gate).
- **Complete runtime coverage**:
  - Runtime quantified conditions (`everyKey` / `someKey` / `all` / `any` / `sizedSort` / multi-key `$join`) emitted as loops over live map keys matching interpreter semantics.
  - Broadcast `each` writes on scalar, record, variant, and kinded maps; tuple keys at every key (`relations`, `$everyTuple`, while `compileJs` preserves its refusal contract); tuples, flags, and quantifiers inside `recur`/`fns`.
  - Full support + crossCheck + `--verify` for `carries`, `carriesList` (with fold loops), `carriesSeq`, `carriesSeqs`, `lists`, `nodes`, `counts` (`$CountCells`), `leasts`, `sums` (`sumRuntime` + recomputed sums), `history`/`log`/`queries`/`prune`, `fixedInt` multi-limb + `wordDivision` (`$wordDiv`), `exists` skolems, Effect `fromSchema` (`Kind.inspect()` on `SchemaKind` and inner kinds in `core/effect-schema.ts`), binary `FoldRule` & `RoseFold` (`emitFold`), and `LoopRule` (`emitLoop`).
- **Canonical op-by-op & kind-by-kind tests** (`core/emit.test.ts`): iterates `E_OPS`, `C_OPS`, `QE_OPS`, `QC_OPS`, and `KIND_NAMES`, constructs one rule per op/kind, emits, and passes differential `--verify`.

### 4. Golden Byte-Identity Check (Phase 1 -> Phase 2)

- Checked all **21** Phase-1 golden fixtures (`budget`, `caps`, `accounts`, `minutes`, `hold`, `seats`, `jobs`, `retry`, `larger`, `room`, `window`, `kinded`, `canEdit`, `approve`, `echoRounded`, `reviewRouting`, `feeSplit`, `limiter`, `ledger`, `orderChart`, `doorChart`):
  - **21/21** produce **100% byte-identical emitted TypeScript code** (`examples/review-routing.generated.ts` is untouched and byte-identical).
  - **20/21** are 100% byte-identical including every header line; **1 explained header-only difference**: `jobs` (items list) has identical emitted code, while line 3 (`// Digest: sha256:...`) varies with prior `keyCounter` calls in the same process because `jobs().machine.step.maps` holds an `each` binder named `k$N` (emitted TS normalizes the loop binder to `$k`, whereas `machineDigest` hashed the raw binder string).

### 5. `compiled()` Unchanged — Paired Same-VM Boat Timings (Forward & Reverse)

Boat batch `20261126-231426-idjwv7` (`paired-compiled-bench`, `research/emit/bench-compiled.ts`, 9 timed rounds per direction on VM `sc-2e2b3a28-yg954f17`, comparing pre-Phase-2 `compileJs` snapshot vs shared-printer `compileJs` on identical inputs):

| Rule | Steps | JS Bytes | `jsIdentical` | `parityOk` | Forward (before / after median ms, ratio) | Reverse (before / after median ms, ratio) |
| --- | ---: | ---: | :---: | :---: | --- | --- |
| `budget` | 150,000 | 2,786 | `true` | `true` | `4.584` / `4.692` (**1.024x**) | `4.870` / `4.520` (**0.928x**) |
| `caps` | 80,000 | 3,446 | `true` | `true` | `4.705` / `4.591` (**0.976x**) | `4.863` / `4.669` (**0.960x**) |
| `accounts` | 80,000 | 3,870 | `true` | `true` | `5.569` / `5.808` (**1.043x**) | `5.562` / `5.573` (**1.002x**) |
| `lock_server_sync` | 80,000 | 3,608 | `true` | `true` | `6.441` / `6.294` (**0.977x**) | `6.446` / `6.724` (**1.043x**) |
| `two_phase_commit` | 30,000 | 8,482 | `true` | `true` | `32.048` / `30.372` (**0.948x**) | `32.799` / `30.411` (**0.927x**) |

Every rule compiles to **byte-for-byte identical JavaScript** (`jsIdentical = true`), passes full step-by-step state parity (`parityOk = true`), and shows zero slowdown (ratios `0.927x`–`1.043x`, purely noise around `1.00x`).

### 6. 100% Expressibility Coverage Sweep on Boat

Boat batch `20261126-231426-idjwv7` (`sweep-1-of-4` through `sweep-4-of-4`, `research/emit/sweep.ts --runs 10 --steps 12`): emit + differential `--verify` against the interpreter on every rule, function, rational rule, statechart, fold, and loop across all 21 domains, all 41 standalone example modules, and the entire 545-law benchmark corpus:

| Suite | Targets | Passed | Emit Refusals | Verify Diffs | Laws Covered | Differential Trials |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `domains` (21 `examples/domains/*.ts` + broken) | 402 | **402** | 0 | 0 | 723 | 51,814 |
| `examples` (41 standalone `examples/*.ts`) | 39 | **39** | 0 | 0 | 39 | 5,357 |
| `realworld` (545-law corpus) | 65 | **65** | 0 | 0 | 357 | 8,450 |
| `duoai` (545-law corpus) | 12 | **12** | 0 | 0 | 12 | 1,560 |
| `duoai-mutant` (545-law corpus) | 10 | **10** | 0 | 0 | 10 | 1,300 |
| `ic3syn` (545-law corpus) | 29 | **29** | 0 | 0 | 33 | 3,770 |
| `ic3syn-mutant` (545-law corpus) | 29 | **29** | 0 | 0 | 33 | 3,770 |
| **Total** | **586** | **586 (100.0%)** | **0** | **0** | **1,207** | **76,021** |

### 7. Final Phase-2 Verification (Boat & Local)

- **Cross-VM Determinism** (`20261126-231426-idjwv7`, distinct VMs `sc-2e2b3a28-5whqahrh` vs `sc-2e2b3a28-6d018w20`, shifted `keyCounter` on box B): **5/5 byte-for-byte identical** (`budget`, `caps`, `accounts`, `feeSplit`, `reviewRouting` — identical digests and source SHA-256s across VMs).
- **Full 7/7 Test Shards & Quality Gate** (Bun `1.4.3`, Node `v24.22.1`):
  - `20261126-232700-7vds0o` (`quality-lint-build-node`, commit `f3fe9de84`):
    - `grep -n 'not supported' core/emit.ts`: **0 matches**
    - `tsc -p tsconfig.build.json --noEmit` + `tsc -p .` outside `research/vendor` + `research/emit/`: **0 errors**
    - `oxlint --type-aware --deny-warnings --disable-nested-config core/ examples/ scripts/ research/emit/`: **0 warnings, 0 errors (748 files)**
    - `bun run build`: **PASS (`dist: 798 entries`)**
    - `bun test core/exports.test.ts core/emit.test.ts`: **49/49 PASS (15,179 expect() calls, 14.26s)** — `core/emit.test.ts` 21/21 PASS, `core/exports.test.ts` 28/28 PASS
    - `bun examples/review-routing.ts`: **5/5 laws proven + sample run PASS**
    - **Node 24 dual-module note**: invoking built `dist/core/cli.js` against repo-internal `examples/review-routing.ts` (which imports `../core/dsl.ts` rather than `gdp-wired`/`dist/core/dsl.js`) loads two `dsl` module instances so `dist/core/dsl.js`'s `funLawCallbacks` WeakMap does not see laws constructed by `../core/dsl.ts` (exit 2: `law was not stated on review routing`). Running `bun core/cli.ts` against repo source or `node dist/core/cli.js` against user code importing `'gdp-wired'` shares a single `dsl` instance; emitted `.ts` files themselves load directly in Node 24 strip-only mode.
  - **7/7 Test Shards** (`20261126-231426-idjwv7` + `20261126-232700-7vds0o`):
    - Shards `1/7`, `2/7`, `3/7`, `4/7`, `6/7`, `7/7`: **PASS**
    - Shard `5/7`: **100% of `core/` tests PASS** (including `core/emit.test.ts` 21/21 PASS in 12.9s, `conformance`, `datatypes`, `folds`, `invoices`, `effect*`, all `count-*`); 1 pre-existing 1ms wall-clock failure in untouched `kernel/epr-clock.test.ts:18` (`EPR debits counted deadlines (rows)`, `withDeadline(start + 1, ...)` — `git diff origin/main -- kernel/` is empty).
- **Private Gitignored Spec Verification** (`private/emit-intent/`, local only, never staged/committed, zero private source/fields/thresholds quoted): re-verified against Phase-2 emitter — **PASS** (5/5 laws proven, differential `--verify` PASS, 3/3 broken variants refused, 4/4 emitted mutants refuted, 0 hygiene matches).

### 8. Follow-Ups

- Alpha-normalize `each`/`all` binder names (`k$N`) inside `machineDigest` so rules using `items`/`each` have call-order-independent header digests across multiple constructions in the same process (emitted code itself is already deterministic).
- Optional: key `funLawCallbacks` / `owned*Laws` by a `Symbol.for(...)` property (or global registry) if running built `dist/core/cli.js` against unbuilt `*.ts` source files importing `core/dsl.ts` directly needs to be supported.
- Investigate/stabilize pre-existing 1ms `kernel/epr-clock.test.ts:18` timing sensitivity under Boat VM load (untouched `kernel/`).
- Docs (`skills/gdp-wired/references/shipping.md`, `skills/gdp-wired/SKILL.md`) intentionally left untouched for Main to author.
- Branch `feat/emit-source` remains local (unpushed) for Main review.
