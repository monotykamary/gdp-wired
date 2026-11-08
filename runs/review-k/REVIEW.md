# Independent review: conditional lemma cuts

**Recommendation: merge after fixes to regression coverage and the mirror contract.** No accepted-false semantic claim was found. The Lean extension has the required statement and clean axioms. Exact TypeScript/Lean acceptance is **not** established: there are concrete, fail-closed differences. Six of twelve TypeScript mutants survived the existing tests, five with independently observable behavior changes.

## Scope and method

Reviewed `git diff 8610af26..0e9afc3d -- kernel/kernel.ts lean-kernel/Count.lean lean-kernel/CountMachine.lean`. Checkout HEAD was `df6f409ebbe5f786759f58b4b9ca8816f5bef6e1`; these trusted files and `kernel/lemma-cut.test.ts` are identical to `0e9afc3d`. No soundness argument relies on search in `core/` or `kernel/prove.ts`. The existing conformance generator/exporter was used as a transport/test, not assumed correct; the zero-row Lean example was written directly.

All builds, test execution and mutants ran on boat, with foreground waits. No Z3/cvc5 or other external solver was invoked. Only this report was written in the worktree. Scratch source, scripts and logs are under `/private/tmp`; no code edits, commits, pushes, merges, or other worktrees were used. Started 2026-11-08 07:47:16 UTC; execution and verification completed around 07:54 UTC, within the 60-minute limit.

Verdicts below concern semantic soundness/assurance. `unclear` is not a claim of a demonstrated unsound certificate: it marks an incomplete guarantee or failed exact-mirror claim.

| question | verdict sound/unsound/unclear | evidence |
|---|---|---|
| 1. Does acceptance with lemmas imply the old semantic claim without an extra unenforced/vacuous premise? | sound | `lean-kernel/Count.lean:334-344,478-482,565-571`: the outer theorem proves unsatisfiability, constructs its model and proves its lemma premises internally. The counted conclusion and count-semantics hypothesis are unchanged from `8610af26:lean-kernel/Count.lean:316-318`. `lean-kernel/CountMachine.lean:239-243,492-495,1841-1842` retain the previous witness-generalized/machine semantics. Full quotations below. |
| 2. Do the new theorems use only permitted axioms, with no sorry? | sound | Fresh Lean compilation and `#print axioms` for every new theorem, both changed counted soundness theorems, and downstream `mc_sound`/`cmachine_sound`: `/private/tmp/review-k-final/review-k-final.log:353-369`. All sets are subsets of `{propext, Classical.choice, Quot.sound}`; `lemmaPath_nil` has none. Neither changed Lean file contains `sorry` or a new `axiom` declaration. Public exported claims also have only those three axioms (`:370-372`). |
| 3. Does TypeScript accept exactly what Lean accepts? | unclear | **No, exact acceptance equality is disproved.** Core cut construction agrees (`kernel/kernel.ts:520-555`; `lean-kernel/Count.lean:202-234`), but TypeScript refuses repeated/constant splits (`kernel/kernel.ts:506,551`) that Lean permits (`lean-kernel/Kernel.lean:1607-1611`; `lean-kernel/Count.lean:229-231`). Additionally `{z:0}` is valid under `lemmaLin` yet is undecided by TypeScript and true in Lean (`kernel/kernel.ts:64-71,514-516,532`; `lean-kernel/Kernel.lean:471-477`). Independent Lean/TS probes confirm both differences. These examples are false rejections, not acceptance of false claims. Detailed boundary audit below. |
| 4. With absent/empty `lemmas`, is exactly the old path taken? | sound | `kernel/kernel.ts:536-539` immediately returns `check(goal, tree)` for the default/empty list, outside the new try/catch. Wrappers preserve their old prechecks and pass the optional field (`:1901-1904,2033-2046`). Lean proves `checkTLemmas_nil`, `checkGoalLemmas_nil`, `checkCounted_nil`, `checkCountedW_nil` (`lean-kernel/Count.lean:238-247,354-359`; `lean-kernel/CountMachine.lean:233-237`). Existing baseline conservation tests passed. |
| 5. Do the requested mutation runs adequately guard this rule? | unclear | Twelve single-change TypeScript mutants were run against **both** `kernel/lemma-cut.test.ts` and `lean-kernel/conformance.ts --lemma-cuts`. Six survived: M03, M04, M05, M06, M07, M09. Five change observable behavior in independent fixed probes. M03 still fails closed downstream and is effectively equivalent on the tested dense inputs. Original results: `/private/tmp/review-k-results/review-k-mutants.log:383-684`; discriminating probes: `/private/tmp/review-k-edges/review-k-edges.log:357-504`. Full matrix below. |

## 1. Statement and semantic prerequisites

The new outer goal theorem, verbatim (`lean-kernel/Count.lean:334-336`):

```lean
theorem goalLemmas_sound (g : Goal) (t : Tree) (lemmas : List CutLemma)
    (h : checkGoalLemmas g t lemmas = true) (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    ¬ ∀ c ∈ g.hyps, evalC env maps c = true := by
```

The old theorem (`lean-kernel/Kernel.lean:2038-2039`) has the same conclusion:

```lean
theorem sound (g : Goal) (t : Tree) (h : checkGoal g t = true) (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    ¬ ∀ c ∈ g.hyps, evalC env maps c = true := by
```

The changed counted theorem, verbatim (`lean-kernel/Count.lean:478-480`):

```lean
theorem counted_sound (g : CGoal) (is : List CInst) (tab : List VDef) (t : Tree) {lemmas : List CutLemma}
    (hck : checkCounted g is tab t lemmas = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hc : ∀ c ∈ g.counts, c.Holds ρ M) : ¬ ∀ h ∈ g.hyps, evalC ρ M h = true := by
```

The only change to its statement is threading `lemmas` into acceptance. `hc` is the **old** meaning of a count, not a new assumed lemma. The goal theorem does not expose `Model`, `PathHolds`, or `CutHolds` as assumptions: `wfTab` is checked, the model is constructed, and all `CutHolds` proofs are obtained from `checkLemma` (`Count.lean:233-234,338-344`). `lemma_sound` uses only the selected hypotheses, via the proved subset property, under the declared `when` rows and the negated cut (`:249-293`). There is no circular premise saying that the desired conclusion already holds.

The witness-generalized theorem retains an important **pre-existing** boundary (`lean-kernel/CountMachine.lean:239-243`):

```lean
theorem countedW_sound (hyps : List C) (cs : List Count) (is : List CInst) (tab : List VDef) (t : Tree) {lemmas : List CutLemma}
    (hck : checkCountedW hyps cs is tab t lemmas = true)
    (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hc : ∀ c ∈ cs, c.Holds ρ M)
    (hH : ∀ ρw : Nat → Nat, (∀ j, (∀ i ∈ is, i.wit ≠ j) → ρw j = ρ j) → ∀ h ∈ hyps, evalC ρw M h = true) : False := by
```

Thus raw `checkMC` is not, and was not, an unconditional unsatisfiability checker for arbitrary witness-dependent hypotheses. The machine wrapper discharges that boundary using freshness: `kernel/kernel.ts:2026-2046,2074-2085` and `lean-kernel/CountMachine.lean:759-774`. The final machine theorem remains:

```lean
theorem cmachine_sound (s : SMachine) (ds : List CDecl) (ps : List CEntry) (h : checkCMachine s ds ps = true) :
    ∀ ρ M, CReach s ds ρ M → ∀ ce ∈ ps, ce.e.Holds ρ (withCnt ds ρ M) := by
```

Source: `lean-kernel/CountMachine.lean:1841-1842`. Neither count interpretation nor reachability semantics changed in the reviewed diff.

## 2. Axiom inventory

Freshly compiled Lean 4.34.0 sources, not merely existing `.olean` files. The query result groups were:

| Theorems | Actual axiom set |
|---|---|
| `lemmaPath_nil` | none |
| `checkTLemmas_nil`, `checkGoalLemmas_nil` | `propext` |
| `lemmaSlice_sub`, `lemmaHyps_sub`, `lemmaPath_holds`, `checkCounted_nil`, `checkCountedW_nil` | `propext`, `Quot.sound` |
| `lemma_sound`, `checkTLemmas_sound`, `goalLemmas_sound`, `counted_sound`, `countedW_sound`, `mc_sound`, `cmachine_sound` | `propext`, `Classical.choice`, `Quot.sound` |

Evidence: `/private/tmp/review-k-final/review-k-final.log:353-369`. The `--public` conformance path passed and printed the same permitted three axioms for `public_conditional` and `public_counted_machine_laws` (`:370-372`). Checks use `decide +kernel`, not a new native-decision axiom (`lean-kernel/emit.ts:474-475`).

## 3. Boundary-by-boundary mirror audit

| Boundary | Result and file:line evidence |
|---|---|
| Eligibility only from original splits | Correct for the current implementation. `kernel/kernel.ts:531-533` filters all lemmas against the unchanged input `path`; only afterwards are cuts prepended. `:548-555` carries only split atoms while descending. Lean does the same at `Count.lean:222-231`. A probe with `c ⇒ a`, `a ⇒ b`, original path `c`, exposes only `a,c`; M04 incorrectly exposes `a,b,c`. Log: edges `:372,414`. |
| Lemma's own path | Correct. The order is **cut false**, followed by every **when true**, with no containing split path and no other cuts (`kernel/kernel.ts:543-546`; `Count.lean:216-219`). M02, which makes the cut positive, was killed. |
| Slice | Correct on inspected inputs. Every index must be a safe integer in `[0, goal.hyps.length)`; only the exact containing expanded goal is indexed (`kernel/kernel.ts:540-546`). Lean uses `getElem?`, returning `none` out of range, and proves membership in the original hypotheses (`Count.lean:205-214,249-271`). Duplicate indices are allowed by both: this is a selected sublist with repetition, not permission to introduce a new hypothesis. The independent `[0,0,1]` certificate passed both checkers; exact-end index was refused. Edges `:358-359`. |
| Duplicate atoms and `@n` | The current helper preserves every row, gives the **first exact canonical atom** the ordinary lookup key, and gives subsequent occurrences distinct `@n` keys (`kernel/kernel.ts:520-527`). A nonempty `canon` contains `:`, while `@n` does not, so it cannot collide with an actual canonical key; the empty canonical key is also distinct. Lean's list lookup chooses the first matching row (`Kernel.lean:460-477`). Independent probes cover repeated cuts, duplicate conditions equal to the cut, and conflicting cut/condition polarity. Edges `:360,374`. M08 was killed only by conformance; M09's altered order survived existing tests but changed frozen-certificate acceptance and direct row order (`:485,498-500`). |
| Witness/instance namespace | A lemma is checked on `{...goal, hyps}` with no new count expansion or instance list (`kernel/kernel.ts:543-546`); Lean uses the same `tab` and selected hypotheses (`Count.lean:216-219`). The outer certificate alone creates count-instance hypotheses (`kernel/kernel.ts:1901-1910,2033-2046`). A lemma **can spell a name absent from the outer instance list**, but it is then just a free natural-valued variable, not a secretly chosen count witness. A lemma proving `-unboundWitness ≤ 0` from naturalness passed with no instances in both TS and Lean; supplying an extra `insts` field on an otherwise invalid lemma granted nothing (edges `:365-367`). No new witness-binding channel was found. |
| Lemmas nested inside lemma trees | The actual checker calls old `check`, not `checkGoalLemmas`, for each lemma (`kernel/kernel.ts:546`). Lean's `CutLemma.tree` is the old `Tree`, whose constructors have no lemma reference (`Count.lean:199-203`; `Kernel.lean:1562-1566`). Extraneous object fields are ignored, not interpreted as assumptions; a tree requiring a nested lemma is refused. Independent nested-tree case: false baseline, true with M05 (edges `:363,426`). Existing tests test `{lemma: n}` placeholders, not a structurally valid split tree with a nested list (`kernel/lemma-cut.test.ts:36-40`). |
| Malformed payloads | Arrays/holes, unsafe coefficients, invalid slices and non-tree references are refused by validation or caught evaluation (`kernel/kernel.ts:537,540-542,557`; tests `kernel/lemma-cut.test.ts:73-80`). Independent null-tree, array-cut, fractional-condition and sparse-slice probes all returned false without throwing (edges `:368-371`). This audit concerns ordinary immutable JSON-shaped certificates, not hostile getters/proxies or concurrent object mutation. Empty-list behavior intentionally retains legacy exceptions rather than adding the new catch. |
| Exact acceptance | **Not equal.** The intentional constant/repeated-split refusals are documented at `lean-kernel/README.md:33`; Lean accepted the independently exported certificates while baseline TS refused them (edges `:361-362`; successful `ReviewEdges.lean` compilation in that job). A second, new-field-specific gap is detailed next. |

### Finding F1: zero-coefficient conditions break exact correspondence

`lemmaLin({z: 0})` passes: all values are safe integers (`kernel/kernel.ts:514-516`). But `decide` marks any key other than `1` as nonconstant, even if its coefficient is zero; with an empty split path it cannot decide `{z:0}` (`:64-71`). Consequently a lemma conditioned on this identically true row is not active. Lean's `dec` uses `allZero l.coefs`, so the corresponding `⟨[(z,0)],0⟩` is true (`lean-kernel/Kernel.lean:471-477`).

A full independent case used hypotheses `a ≤ b`, `b ≤ 0`, `0 < a`, `c ≤ 0`; the lemma proves `a ≤ 0` from slice `[0,1]` under `when: [{z:0}]`. The root proof uses the cut and `1-a ≤ 0`. Baseline TS refuses because it never activates the cut (edges `:364,375`). A directly written Lean certificate, including explicit proof rows, proves both `lemmaActive [] zeroLemma = true` and `checkGoalLemmas ... = true`. This is a **false rejection**, not a semantic unsoundness example. Reproduction source: `/private/tmp/review-k.tQTude/review-edgecases.ts`, direct Lean block in its `--make` branch.

Required resolution: normalize/handle zero coefficients consistently in the new-field boundary, or explicitly restrict the new payload contract and test that restriction. Do not claim exact parity without stating the representable/canonical domain and intentional legacy refusals. There is no reason to remove the legacy split guards to address this finding.

## 4. Mutation matrix

Each mutant was applied **alone** to the original `kernel/kernel.ts`, in boat scratch `/private/tmp/gdp-review-k.UMiIO7/tree`, restored between runs. Substitutions are in `/private/tmp/review-k.tQTude/review-mutants.json`; the runner checks that each replacement anchor is unique. Unit command: `bun test ./kernel/lemma-cut.test.ts`. Conformance command: `bun lean-kernel/conformance.ts --lemma-cuts`, then `lean ReviewConformance.lean` if generation succeeds. `GEN FAIL` means the existing generator detected a violated assertion; Lean was not run on a nonexistent output. It is a killed mutant, not a Lean rejection.

| Mutant | Single change (original source) | Unit | Conformance generation / Lean | Existing-suite outcome |
|---|---|---|---|---|
| M01 | `lemmaPath`: replace eligibility filter with all lemmas (`:532`) | FAIL | GEN FAIL / not run | killed |
| M02 | Lemma proof assumes cut true instead of false (`:545`) | FAIL | GEN FAIL / not run | killed |
| M03 | Allow `slice` index `== hyps.length` (`:542`) | PASS | PASS / PASS | **survived** |
| M04 | Eligibility incrementally reads preceding cuts (`:532`) | PASS | PASS / PASS | **survived** |
| M05 | On old-check failure, recursively try `tree.lemmas` (`:546`) | PASS | PASS / PASS | **survived** |
| M06 | Remove repeated-split refusal in new traversal (`:551`) | PASS | PASS / PASS | **survived** |
| M07 | Remove constant-split refusal in new traversal (`:551`) | PASS | PASS / PASS | **survived** |
| M08 | Replace duplicate-preserving `out.set(...)` with `out.set(id, atom)` (`:525`) | PASS | GEN FAIL / not run | killed |
| M09 | Prepend original path before cuts (`:523`) | PASS | PASS / PASS | **survived** |
| M10 | Ignore slice; always use all goal hypotheses (`:544`) | FAIL | GEN FAIL / not run | killed |
| M11 | Stop forwarding `lemmas` from `checkMC` (`:2046`) | FAIL | PASS / PASS | killed |
| M12 | Skip each independent lemma proof (`:546`) | FAIL | GEN FAIL / not run | killed |

Baseline passed both stages and Lean (`mutants.log:383`). Complete outcome receipts are at `:384,440,522-527,540-541,584,628,684`.

### Finding F2: five observable contract changes are unguarded

Independent fixtures were generated **once from the unmodified checker**, saved as JSON, and replayed unchanged across the six survivors. This avoids allowing the mutated helper to rebuild a matching certificate. Additional direct path assertions used literal expected rows.

- **M04:** changes visible rows from `[a,c]` to `[a,b,c]` by letting one cut enable another (`edges.log:372,414`).
- **M05:** accepts a valid-shaped lemma tree that requires its nested lemma list; the original refuses it (`:363,426`). This fallback is not necessarily logically unsound, but it violates the explicitly non-nested certificate language.
- **M06/M07:** accept repeated/constant split certificates refused by the original new traversal (`:361-362,445,467`). These tests should pin conservation of refusal policy; permitting the splits alone is not evidence of logical unsoundness.
- **M09:** changes row order from `[a,c]` to `[c,a]`, changes duplicate keys' positions, and rejects a frozen duplicate-slice certificate that the original accepts (`:359,373-374,485,499-500`). The existing fixture builds its leaves with the `lemmaPath` under test (`lean-kernel/lemma-cases.ts:31-32`), so it can adapt to the bug instead of detecting it.
- **M03:** still rejects the exact-end index in the independent probe (`:358,379`). Selecting it produces `undefined`; old leaf construction evaluates every selected hypothesis and throws, caught by the new wrapper (`kernel/kernel.ts:426-427,543-557`). This is a fail-closed/effectively equivalent mutant on ordinary dense inputs, not a demonstrated out-of-range assumption leak. Record it rather than inflating the soundness finding. Still add the exact-end boundary test, which the current test list lacks (`kernel/lemma-cut.test.ts:33`).

The changes above must not all be called semantic unsoundness: some extend a sound rule or alter serialization/refusal policy. They **do** show that the current tests do not guard the precise trusted rule that is claimed. Add independent/frozen tests for M04/M05/M06/M07/M09 and explicit slice-end/duplicate-row cases; a passing self-generated conformance fixture alone is not enough.

## 5. Execution receipts and reproducibility

The local scratch snapshot is `/private/tmp/review-k.tQTude`. Relevant files: `review-mutants.json`, `review-run.ts`, `review-job.sh`, `review-edgecases.ts`, `review-edge-run.ts`, `review-edge-job.sh`, `review-final-job.sh`, and the three `jobs-*.json` manifests. All boat test processes exited; no background waiter or review job remains. No other client's VM was stopped or modified.

| Foreground boat batch | Result | Local receipt |
|---|---|---|
| `20261108-144832-9nci35`, `review-k-mutants` | exit 0; baseline, 12 mutants, Lean source builds and initial axiom queries; 79.79 s job time | `/private/tmp/review-k-results/{summary.tsv,placement.json,review-k-mutants.log}` |
| `20261108-145141-eqxnfa`, `review-k-edges` | exit 0; independent fixed probes and direct Lean edge cases; 18.18 s job time | `/private/tmp/review-k-edges/{summary.tsv,placement.json,review-k-edges.log}` |
| `20261108-145323-4fyt5n`, `review-k-final` | exit 0; all new theorem axioms and public conformance; 18.07 s job time | `/private/tmp/review-k-final/{summary.tsv,placement.json,review-k-final.log}` |

All were boat jobs on the existing `sc-f0d8daeee6c3` image, 2 requested vCPUs / 6 GiB, class `gate`; no fallback or VM start was needed. These durations are receipts, not benchmark claims. Final `git diff --exit-code HEAD` and the diff of reviewed files against `0e9afc3d` were empty. `runs/` is ignored, so a clean Git status does not imply the report is absent.

## Final verdict

**Merge after fixes:** add independent, fixed-input regression tests that kill the five behavior-changing survivors (cut-assisted eligibility, nested lemma trees, repeated splits, constant splits, and path/cut ordering), retain an exact slice-end test while recording M03's fail-closed equivalence, and resolve/document the zero-coefficient condition discrepancy and the intentional strict-subset relationship to Lean rather than claiming exact acceptance equality. The Lean statement, axiom inventory, witness boundary and empty-list conservation support the semantic soundness of the implemented extension; I found no accepted certificate for a false semantic claim. The remaining blockers are assurance and mirror-contract gaps, not a demonstrated break of the Lean theorem.
