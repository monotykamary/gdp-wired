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

## Phase 2: One Code Generator (In Progress)

*(To be filled upon completion of Phase 2: shared printer module for `compileJsMode` and `emit`, `core/sha256.ts`, slimmer `core/emit-cli.ts`, golden byte-identity checks, paired Boat `compiled()` timings forward+reverse, and full 7/7 shards.)*
