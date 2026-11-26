# Proposed Trusted Extension: Conditional Zero-Reset Guard (`SumDecl.reset`)

**Status:** DESIGN & LEAN-FIRST PROOF COMPLETE — **AWAITING USER SIGN-OFF** (zero trusted files modified or committed).

## 1. Summary

Extends `Kern.SumDecl` (`lean-kernel/Sums.lean`) and `sumMachine` (`kernel/kernel.ts`) with an optional key-independent zero-reset guard `reset?: C` (`reset : Option C := none` in Lean):

- **Transition (`sumNext`):**
  $$S' = \text{if } R \text{ then } 0 \text{ else } (S + \mathrm{dTerm}(\mathrm{gAfter}, \mathrm{cs})) \mathbin{\dot{-}} \mathrm{dTerm}(\mathrm{gHere}, \mathrm{cs})$$
- **Two-branch side obligations:**
  1. **`S @reset` (`sumResetGoal`, 1 goal per sum with `reset = some R`):**
     Under `assume`, `R` (flags inlined), and `cellLaws ps d` at fresh key `x$S`:
     $$\mathrm{gAfterInlined}(x\$S) = 0$$
     Discharges `∀ k, gAt d.g M' k = 0`, closing the `R = true` branch via existing `Kern.isSum_zero`.
  2. **`S @cover M` (`sumCoverGoal`, 1 goal per `each`-written map `M` read by `d.g`):**
     Under `assume`, `¬R` (flags inlined), `cellLaws ps d`, and `x$S ≠ c_i` for each cover key `c_i`:
     $$w(x\$S) = M[x\$S]$$
     Closes the `R = false` branch via existing `Kern.isSum_change`.
- **Two-branch lemma (`Kern.isSum_reset`):**
  ```lean
  theorem isSum_reset {f f' : Nat → Nat} {s : Nat} (r : Bool) (cs : List Nat) (h : IsSum f s)
      (hzero : r = true → ∀ k, f' k = 0)
      (hag : r = false → ∀ k, k ∉ cs → f' k = f k) :
      IsSum f' (if r then 0 else s + dsum f' cs - dsum f cs)
  ```
  Axioms: `[propext, Quot.sound]`. All machine-level theorems (`sum_step`, `sum_cells`, `sum_holds`, `sum_allowed`, `sum_laws`, `sum_project_laws`, `sumleads_sound`, `sumleads_wf_sound`, `sumleads_sf_sound`) depend ONLY on `[propext, Classical.choice, Quot.sound]`.

## 2. Side Conditions (`resetOk` in Lean, mirrored 1-to-1 in `kernel/kernel.ts`)

When `d.reset = some r`:
1. `naturalC(r)` and `unquantified(r)` (no negative constants/factors, no quantifiers); every flag referenced by `r` is declared on the base machine `m` (never a sum's `cells$S` quantified flag).
2. **Key-independence:** `r` avoids `d.k`, and `inlineC s.f.flags r` avoids `d.x` (`x$S`) and every `each`-write bound key `w.2.1` in `coverWs s d`.
3. **No summed-map reads (conservative trust guard):** `avoidsMaps (mapsE d.g) (inlineC s.f.flags r)` — `r` may not read any map aggregated by `d.g`, directly or via plain/chained flags.
   - *Calibration note:* Mathematically, `isSum_reset` / `sum_step` only needs `avoids [d.x] (inlineC s.f.flags r)` for soundness; adding `avoidsMaps (mapsE d.g)` is strictly more restrictive, explicitly refuses direct/plain-flag guards reading summed cells at any key, and preserves `core/sum-broadcast.test.ts`'s `lowerBoundDual` refusal (`clears = op == clear && M[id] == 0`). (Quantified `all` flags are represented by `?f` under `inlineC`, matching `Progress.lean`, and remain sound under `isSum_reset` because `evalC` of `r` is key-independent.)
4. **Single-key write freshness:** for every `w ∈ s.f.m.writes` writing a map read by `d.g`, `inlineE s.f.flags w.2.1` and `inlineE s.f.flags w.2.2` avoid `d.x` (needed by `postRdInlined` inside `sumResetGoal`).

## 3. Subtle Bugs / Downstream Compatibility Caught During Design

1. **`kernel/kernel.ts:1442` flag-inlining mismatch vs `Progress.lean:eqOrFlag`:**
   Previously `sumMachine` built `lean: Subst` wrapping plain flags as `(if c then 1 else 0) = 1`, whereas `lean-kernel/Progress.lean:31-36` (`eqOrFlag`) inlines `.eq (.var ?f) (.const 1)` directly to `c`. For plain-flag `@reset` and `@cover` goals (like Spark `clears = op.is('clear')`), the proof tree must split on `c` directly so Lean `decide +kernel` accepts exported certificates verbatim. Fixed in the proposed diff (`const lean: Subst = {vars: {}, maps: {}, flags: flagsOf(m)}`).
2. **`lean-kernel/emit.ts:1463` cover-goal matching:**
   Replaced prefix matching (`startsWith(\`${s2} @cover \`)`) with exact `${s2} @cover ${mp}` in `sm.step.maps` order plus exact `${s2} @reset`, avoiding prefix collisions (matching `feat/group-sums` `9c42e65d9`), and updated `checkSums` certificate encoding to `(coverTrees, Option resetTree)`.
3. **`lean-kernel/SemanticSums.lean` & `lean-kernel/RadixSumTransport.lean` & `lean-kernel/lift-simulation/index.ts`:**
   - Kept `sumOk1_parts` at its original 10-tuple signature (adding separate `sumOk1_resetOk`) so downstream destructuring stays intact.
   - Added `(hno : h.sums.all (fun d => d.reset.isNone) = true)` to `SemanticSums.{sum_step,sum_cells,sum_holds,sum_allowed,sum_project,sum_project_laws}` so `SemanticSums` stays sound if a machine carries `reset = some _`.
   - Rejected `d.reset.isSome` in `RadixSumTransport.target` (consistent with `lift-simulation/index.ts:83`, which rejects `each` writes on radix-packed maps).
   - Updated `lift-simulation/index.ts` `SumDecl` literals (8th field `none`) and `SemanticSums` calls (`(by decide +kernel)`).
4. **Generated library & intentional test updates upon sign-off:**
   - Run `bun scripts/gen-lean-library.ts` to refresh `lean-kernel/library.ts`.
   - Update `core/covering.test.ts:53-72` (commit `67e6d8b56` deliberately skipped broadcast clears; replace with a proving `broadcast-covering-clear` test + partial-wipe refusal test) and `core/sum-broadcast.test.ts:84-163,233-267` (`putClear`, `sparkMemoryStore('with-clear')`, and `step-reads-sum` now prove; `lowerBoundDual`, `range-clear`, `shift-all`, and `replayRefutation` remain unchanged).

## 4. Files

- **Committed untrusted work (on branch `trusted/sum-reset-lean`, zero kernel/Lean edits):**
  - `core/sum-reset.ts` — untrusted reset-guard extractor (`extractSumReset`, `sumResets`, `isAdmissibleResetGuard`), handling `when(R, 0, ...)`, `bool` `choose(R, no, ...)` lowering (`(R ∧ 0<0) ∨ (¬R ∧ rest)`), inverted branches, chained resets (`r1 ∨ r2`), filtered multi-field sums, non-zero zeroing constants, and multi-map conjunctions, while refusing all 4 mutant classes.
  - `core/sum-reset.test.ts` — unit tests (registered in `scripts/test-shards.ts`).
- **Scratch Lean 4.34.0 proof & proposal artifacts (NOT wired into kernel):**
  - `research/sum-reset/SumResetScratch.lean` — standalone Lean 4.34.0 proof importing `Sums`.
  - `research/sum-reset/PROPOSED-TRUSTED.patch` — exact unified git diff across all 10 files (`lean-kernel/Sums.lean`, `lean-kernel/SemanticSums.lean`, `lean-kernel/RadixSumTransport.lean`, `lean-kernel/emit.ts`, `lean-kernel/lift-simulation/index.ts`, `kernel/kernel.ts`, `kernel/README.md`, `core/machine.ts`, `core/dsl.ts`, `core/conformance.ts`).
  - `research/sum-reset/verify-proposal.ts` — Boat dry-run harness verifying Spark `MemoryStore` #0/#1, `putClear`, `broadcast-covering-clear`, preserved negative controls, and the full 12-mutant (15-case) battery in both TS and Lean 4.34.0 `decide +kernel`.

## 5. Mutant Battery (Refused in Both TypeScript `kernel.ts` and Lean 4.34.0 `decide +kernel`)

| Class | Mutant | Expected |
|---|---|---|
| 1. Key-dependent guard | M1 `reset = (k$S < limit)` (`d.k`) | Refused (`sumMachine` throw / Lean `sumOk = false`) |
| 1. Key-dependent guard | M2 `reset = (x$S < limit)` (`d.x`) | Refused (`sumMachine` throw / Lean `sumOk = false`) |
| 1. Key-dependent guard | M3 `reset = (k$w < limit)` (`w.2.1`) | Refused (`sumMachine` throw / Lean `sumOk = false`) |
| 2. Partial wipe | M4 `when(clears && k < limit, 0, ...)` with `reset = clears` | Refused (`S @reset` fails / Lean `checkSums = false`) |
| 2. Partial wipe | M5 `when(clears && k != 0, 0, ...)` with `reset = clears` | Refused (`S @reset` fails / Lean `checkSums = false`) |
| 3. Reset that also writes | M6 single-map `when(clears, when(k == id, val, 0), ...)` | Refused (`S @reset` fails / Lean `checkSums = false`) |
| 3. Reset that also writes | M7 two-map `M[k] + U[k]`, `M` clears & `U.set(id, val)` | Refused (`S @reset` fails in `proveLaws`) |
| 4. Guard reading summed cells | M8 `reset = (M[k$S] == 1)` | Refused (`sumMachine` throw / Lean `sumOk = false`) |
| 4. Guard reading summed cells | M9 `reset = (op == 1 && M[id] == 0)` | Refused (`sumMachine` throw / Lean `sumOk = false`) |
| 4. Guard reading summed cells | M10 plain flag `clearsReadingM = (op == 1 && M[id] == 0)` | Refused (`sumMachine` throw / Lean `sumOk = false`) |
| 4. Guard reading summed cells | M11 chained flag `f1 = (M[id] == 0); f2 = (op == 1 && f1)` | Refused (`sumMachine` throw / Lean `sumOk = false`) |
| 5. Certificate tampers | M12a-d dropped `@reset` tree, dropped `reset` decl, swapped to `puts` / `trueC` | Refused (`checkLaws = false` / Lean `checkSums = false`) |

## 6. Boat Verification Results (Node `v24.22.1`, Lean `4.34.0`)

- **Step 1 scratch Lean proof (`lean-step1-v3`, batch `20261126-032936-wdfnqh`, exit 0 in 23 s):**
  `research/sum-reset/SumResetScratch.lean` compiled cleanly in Lean 4.34.0 importing `lean-kernel/Sums.lean` (zero trusted files edited). `Kern.isSum_reset` axioms: `[propext, Quot.sound]`; all 9 `Kern.SumReset.*` machine soundness theorems: `[propext, Classical.choice, Quot.sound]` (0 `sorryAx`).
- **Untrusted extractor quality (`verify-v2`, batch `20261126-035640-4jmzg7`, exit 0 in 56 s):**
  `bun run build`, `tsc -p tsconfig.build.json`, `oxlint --type-aware --deny-warnings`, `gen-lean-library.ts --check`, `test-shards.ts --list`, 29 tests (1,428 expects) across `scripts/test-roster.test.ts`, `core/sum-reset.test.ts`, `core/sums.test.ts`, `core/sum-broadcast.test.ts`, `core/covering.test.ts`, and Lean 4.34.0 replay of updated `SumResetScratch.lean` (with `w.2.1` check + `decide +kernel` mutant check).
- **Ephemeral patched dry-run (`verify-v4`, batch `20261126-040350-vzdq93`, exit 0 in 93 s, 17 receipt files in `lane-receipts/neon-sums/verify-v4/`):**
  - Applied `research/sum-reset/PROPOSED-TRUSTED.patch` cleanly to `/tmp/patched-verify` (leaving worktree `gdp-wired-sums` untouched).
  - `gen-lean-library.ts`, `tsc -p tsconfig.build.json`, `oxlint --type-aware --deny-warnings` (0 warnings, 0 errors), and 68/68 tests (207,061 expects) across 9 files (including `kernel/tamper.test.ts`, `kernel/tuples.test.ts`, `core/conformance.test.ts`, `lean-kernel/axiom-audit.test.ts`, `lean-kernel/export-shape.test.ts`, `lean-kernel/lift-simulation/shape.test.ts`).
  - Lean 4.34.0 compiled `Sums.lean`, `GroupedSums.lean`, `SemanticSums.lean`, and `RadixSumTransport.lean` with 0 errors and standard axioms only (`[propext, Classical.choice, Quot.sound]`).
  - **Positive proofs (all checked + Lean 4.34.0 `decide +kernel` verified):**
    - `putClear`: eq, le, stepLaw proven; `PutClear.lean` (9.5 KB) axioms `[propext]` (`putclear_scheck`) and `[propext, Classical.choice, Quot.sound]`.
    - `broadcast-covering-clear` (`covering.test.ts` pattern): proven automatically with covering helpers.
    - **Spark `MemoryStore + StorageMemoryPool` (`cohort19` `law-2` & `law-3`):** `#0` proven & checked in **398 ms**; `#1` proven & checked in **282 ms**; `SparkMemoryStore.lean` (90 KB) elaborated by Lean 4.34.0 `decide +kernel` (`spark_scheck`: `[propext]`; `spark_exact`, `spark_own`, `spark_sum0`, `spark_sum1`: `[propext, Classical.choice, Quot.sound]`).
    - `step-reads-sum` (with `cleared => sum == 0` helper): proven & checked.
  - **Preserved negative controls:** `range-clear`, `shift-all`, `lowerBoundDual(true)` all remain `unknown` at `@cover M`; `lowerBoundDual(false)` remains `sat` with replayed original-rule counterexample.
  - **Mutant battery & randomized conformance:** all **15** TS checks refused; `MutantBattery.lean` (40 KB, **14** `example : ... = false := by decide +kernel` checks across all 4 required mutant classes + certificate tampers) and `SumConformance.lean` (352 KB, **65** `decide +kernel` checks including `reset` family) elaborated cleanly in Lean 4.34.0 with 0 errors and standard axioms only.
- **Confidence calibration:**
  - **High confidence (~0.98)** in the soundness of the proposed Lean + TS kernel rule (`isSum_reset`, `sum_step`, `sum_project_laws`, `sumleads_*`) and its downstream compatibility (`GroupedSums`, `SemanticSums`, `RadixSumTransport`, `emit`, `lift-simulation`): every theorem and exported proof (including Spark `MemoryStore` and all 14 Lean mutants) was independently kernel-checked in Lean 4.34.0 with only standard axioms.
  - **Known scope boundaries (unknown / deliberately deferred):** partial wipes (`clears && k < limit`), resets that simultaneously write non-zero cells, multi-sum cyclic reset dependencies, and `reset` on radix-packed `SemanticSums` / `RadixSumTransport` (explicitly guarded off by `d.reset.isNone`).
