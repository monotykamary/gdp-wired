# Track P report

Base: `40693c7a`; branch: `claude/track-paxos`.

**Status: active follow-up; original production target NOT proven and not eligible to merge.** The initial checkpoint below is retained as history. Work continues with exported check-only certificates, full wall-time accounting, six minimal-certificate diffs, and per-phase profiling. No gate success is inferred from scheduler exit status.

## Implementation

- Integrated the supplied generic carry, scan-prefix, and counted-support generators and their tests. Prefix generation is consolidated in `core/carry.ts`.
- Added `core/relevance.ts`: bounded deterministic relevance subsets, lifting trees and count certificates back to the exact full context. Subset failure or SAT is not a whole-context result. The old fixed-size 12/24-law tiers remain opt-in; the verified definition-local source context is enabled for structurally supported count goals.
- Improved selected-count proposals: relevant keyless before/after/incoming comparisons, upper-bound nonincrease/overlap priorities, live referenced-read projection, and exact affine remainder matching. Complete original guarded laws are instantiated; no packed-coordinate equality is assumed.
- Start with preferred existing count instances when seeded bounds exist; retain the lazy pool. Deduplicate symmetric complete instantiated term premises rather than filling source slots twice. Reuse count proposal pools when only primitive PRE support grows; follow count-dependent flags transitively for invalidation. Every retained view is reified and final certificates are checked.
- Archival duplicate files in `research/claude-import/` are excluded from type/lint discovery, not from integrated engine tests.
- No kernel, Lean, model, original-law, proof-budget, or external-solver change. Structurally supported count and multi-coordinate goals now try the counted pass first; unrelated no-support scheduling is unchanged.

## Commands and observed results

Every substantive run used boat; timing runs used `--vm-type large --timing`.

### Integration and production recapture

```
supercomputer run --jobs research/track-p-jobs.json --out runs/track-p-import-check --class interactive --vm-type large
supercomputer run --jobs research/track-p/experiment-jobs.json --out runs/track-p-fast-v1 --class interactive --vm-type large --timing --data runs/track-p-data:research/track-p/input
```

Initial integration tests: 53 passed, 0 failed, 1173 assertions. Initial check failures from absent pinned submodules and imported helper typing were repaired; final check result is below.

Original harness `run.ts --ms 60000 --only paxos_epr --skip broken`, tree `f1791b206089`: **unknown**, observed 89,328ms wall, 12,997,648 work. This fails strict 60 seconds. Generated 77 candidates; Houdini ended with 29, with safety C7 open. C7 had proved under the larger context before its supports were removed. Capture: 458 model SAT, 91 model unknown, 148 grow trees, 16 grow unknown. Archive: `runs/track-p-fast-v1/dump.tar.xz`.

`runs/track-p-candidates/candidates.log`: **19/19 reference-family formulas generated** (15 exact names, 4 alpha-equivalent generated names). Historical laws are never injected into production.

### Fast-loop relevance and family baseline

Five historical unknown queries were replayed in pairs at 1500 counted ms. Goals of 174, 196, 204 and 210 hypotheses remained unknown at depth zero; a 104-hypothesis abstraction was SAT. Hypothesis relevance produced **no checked proof flips**. These SATs are not reachable counterexamples.

```
supercomputer run --jobs research/track-p/family-jobs.json --out runs/track-p-family-v1 --class submission --vm-type large --timing --data runs/track-p-data:research/track-p/input
```

Initial generic family replay checked **32/38 obligations**, in both full-hypothesis and relevance modes. The complete v5 replay (`runs/track-p-family-v5/`, tree `f11a474c1b70`) still checked 32/38 in each mode. All INITs checked. STEP indices 7, 10, 11, 17, 33, 66 remained open (10 returned SAT for an incomplete abstraction; others unknown). This is standalone generic-proposal replay, not production family admission. Tree results were checked with `checkMC` against original obligations.

### C9 and C11: independently checked

Evidence: `runs/track-p-gaps/REPORT.md`, `recheck-run/recheck.log`, retained requests/trees, and complete investigation source in `runs/track-p-gap-source/`. Fixture SHA256:

```
ee4bee5547e52dc7222e210f1a188e9adb1b81fe542eb01396cacba26e7007f1
```

- C9 STEP checks with its own PRE law (17 hypotheses, observed 163ms), and with family19 (22 hypotheses, 115ms). Two comparisons suffice: old-minus-post and incoming-minus-post, at actual selected reads. Removing a count witness rejects retained certificates.
- C11 STEP checks with family19: 37 encoded hypotheses, observed 205.63ms. Reduced alternative: **32 hypotheses, 364.05ms**, using C33[a,b,pv] and C45[wMeet,a,b], without quantified C3/C61 instances.
- Fresh replay regenerated the original goal, verified source binding, and checked certificates again. These are derivability results, not production discovery or whole-family admission.
- Existing arithmetic proves equality of the packed prefix and low digit from equal full keys and low-digit bounds. Individual node/round cancellation is false; explicit SAT counterexamples are retained. No unsound coordinate identity was added.

### Concrete search failures and final bounded changes

The emitter audits identified:

1. Four cold C33 coordinate proposals filled its four slots before needed C33[a,b,pv] arrived. Whole-premise symmetry deduplication in a standalone scheduling control emitted that tuple on the next pass.
2. Repeated pool construction consumed the shared **65536-work** generation limit before C70's next closure pass. C70 appeared with the hand-selected request.
3. A temporary two-slot reservation failed because the first sparse pass refilled the slots. A coarse all-flags cache was invalidated by primitive rowOk because an unrelated flag read counts.

The final implementation instead deduplicates symmetric term premises at both admission sites and follows only actual/transitive count-dependent flag instances for pool invalidation. The v5/v6 regression caught lower-quality cold sources backfilling freed slots, including through the generic partial-read fallback. The final selector preserves exact write-key donor priority in both paths; its regression requires both distinct roots with no symmetric or unrelated-value backfill. Budgets are unchanged.

V5 and V6 strict checks passed (0 errors/warnings); each had 53/54 targeted tests pass before the complete backfill fix. V5 generic C9 checked at 53 hypotheses (227ms full, 269ms relevance). C11 remained unknown at 99 hypotheses, zero case splits (1524ms full, 1301ms relevance). This is a proof-search timeout, not the six-round observation ceiling or a counterexample.

Final command:

```
supercomputer run --jobs research/track-p/focused-v7-jobs.json --out runs/track-p-final-validation --class interactive --vm-type large --data runs/track-p-data:research/track-p/input
```

The exclusive-timing v7 batch (`20261107-235739-41327e`) remained wholly queued behind other real work and was explicitly cancelled/closed with zero VMs or starts. Final validation uses shared large-VM slots; its timings are **not benchmark evidence**.

Final source tree `28dca86ad30b`, `runs/track-p-final-validation/`:

- `bun run check`: **passed**, zero warnings/errors (903 files).
- Targeted support/carry/prefix/relevance tests: **54 passed, 0 failed, 914 assertions**.
- Generic C9 INIT and STEP: **checked** in both modes; STEP uses 53 encoded hypotheses.
- Generic C11 INIT: **checked**. C11 STEP: **unknown**, 99 encoded hypotheses, zero case splits, round 3; this is a proof-search time exhaustion, not the six-round observation ceiling.
- The residual wall is now explicit: the generic search still fails on a 99-hypothesis C11 context while a source-bound 32-hypothesis certificate checks. The five other open family obligations in the complete v5 replay also prevent family admission. Hypothesis-pruning experiments did not turn those into checked production proofs.

No final-run timing is used as benchmark evidence because that validation shared its large VM.

## Follow-up: certificates and 89.328-second wall-time accounting

Both requested certificates are exported to `runs/track-p-certs/{c9,c11}/{goal.json,proof.json}` in the C14 pack format. Fresh boat check-only replay returned true for both, with `searchWork: 0`, no nonzero search costs, and witness-removal controls rejected. C9 has 17 encoded hypotheses; C11 has 32. Hashes and source bindings are in that directory.

The original `DUMP_MIN=0` ledger contains **713 root queries**. `research/query/dump.ts` records wall milliseconds, and the root hooks suppress nested logging; these totals are disjoint. Exact accounting source: `runs/track-p-fast-v1/timing-accounting.json` (ledger SHA256 `c2b2ba00d188f9c1698448f7b89368fbe143fe5a53859d7c06ffff86e7762c37`).

| Root outcome | Queries | Total wall ms |
|---|---:|---:|
| proved (`tree`) | 148 | 1,379 |
| unknown | 107 | 7,347 |
| SAT | 458 | 47,516 |
| all roots | 713 | 56,242 |
| outside root queries | — | 33,086 |

549 model queries consumed 54,862ms; 164 grow queries consumed 1,380ms. Thus the six open STEPs' failed proof attempts are **not the entire overshoot**: SAT/model search and time outside the root queries dominate. The 187 traced per-law attempts total 73,060ms, comprising 56,242ms in root queries and 16,818ms between/around their queries. Another 16,268ms lies outside those traced attempts.

**Generation of the 19 laws was not wall-timestamped in this capture.** The log's `candidates at 0 ms` uses the counted `clock()`, not wall time, and cannot support a zero-generation-time claim. The 16,268ms outside attempts includes generation, early small-state work and other admission/control overhead; it cannot honestly be assigned to generation alone. Generation-only replay (`runs/track-p-generation-timing/generation-only.log`, pinned large VM, zero root queries) measured **18,387.93ms** through the same admission path: model 0.29ms, caller laws 1.27ms, guard laws 3.78ms, initial small-state warmup 6,742.40ms, caller small filter 48.10ms, candidate generation plus small-state filtering 11,590.58ms. It generated 77 candidates and matched 19/19 family formulas. This is a current-source isolated measurement, not a retroactively invented timestamp for the historical 89.328-second run.

| Rank | Ledger index (zero based) | Kind / recorded name | Hyps | Outcome | Wall ms |
|---:|---:|---|---:|---|---:|
| 1 | 459 | model / counted | 122 | unknown | 2,068 |
| 2 | 362 | model / counted | 318 | SAT | 1,967 |
| 3 | 157 | model / counted | 289 | SAT | 1,728 |
| 4 | 453 | model / counted | 279 | SAT | 1,727 |
| 5 | 474 | model / counted | 223 | SAT | 1,357 |
| 6 | 329 | model / counted | 219 | SAT | 1,258 |
| 7 | 419 | model / counted | 252 | SAT | 1,244 |
| 8 | 471 | model / counted | 195 | SAT | 1,157 |
| 9 | 122 | model / counted | 152 | SAT | 1,138 |
| 10 | 340 | model / counted | 238 | SAT | 997 |

The dump records these goals as `counted`; it does not preserve their owning law name. The ledger indices above identify them exactly. No invented law attribution or retrospective generation timestamp is used.

## Six open STEPs: checked support and emitter diffs

All six now have source-bound hand certificates checked against the unchanged original fixture (SHA256 `ee4bee5547e52dc7222e210f1a188e9adb1b81fe542eb01396cacba26e7007f1`). Each fresh check regenerates the raw goal/declarations/encoded goal and calls `checkMC`; no search is used for authentication. Deletion experiments characterize these retained requests, not globally minimal proofs: an abstract SAT result after deleting a premise is **not** a reachable protocol counterexample.

**Important audit limitation discovered during comparison:** the historical `family.ts`/`audit-support.ts` loop seeded *all* input terms, called `polaritySelection` for every target, and reselected after each closure. Production filters input terms to actual map keys, uses `smallSelection` for primitive POSTs, and retains semantic selections through reservation. Thus the table below describes the recorded emitter-only audit—not an assertion that production loses its selections. In particular, C10's lost ternary is a replay artifact. `countedAttempts` now exposes the unchanged production attempt to `research/track-p/production-replay.ts`, eliminating this divergence for the next 38-obligation replay. The hand certificates and source-matcher omissions remain independently checkable evidence.

Notation: `C<i>` is the original fixture index; `a,b,c,d` are the target's original bound keys; `k(a,b)=64a+b`. Every count instance below has `below=size`; unit is zero except the C11 meet (unit -1). No guards, assumptions, or packed-coordinate equalities were added.

| STEP | Checked raw/encoded; exact retained PRE instances | Required count expressions / witnesses | Missing or late in the historical emitter audit | Extra PRE tuples (each exact tuple is listed in the linked ledger) |
|---|---|---|---|---|
| **7** | **28/39**. C7(a,b,c,d); C10(a,b),(c,d); C17(a,b),(c,d); C11(a,b,r,v),(c,d,r,v),(r,v,a,b),(r,v,c,d); C33(a,b,v),(c,d,v); C45(wNew,r,v). | wNew: `members[0]-missing[0]`; wA/wC: `members$Decision[k]-can$Vote$members[k]` at k(a,b),k(c,d); wR: `members[0]-missing[0]-can$Vote$members[k(r,v)]`. | First 11 PRE tuples in prepare; C45(wNew,r,v) never selected generically, appears in closure:0 with hand cert. All four needed count signatures exist in full pool (indices 16,25,32,77), but polarity-only selection omits them. | **64**: flags 4x10; C2:3,C4:4,C9:1,C10:1,C14:4,C17:2,C33:2,C45:4,C61:1,C74:2. [Exact diff](track-p-six/seven-seventeen/c7/diff.json). |
| **10** | **17/23**. C10(a,b). | `members$Decision[k(a,b)]-members$Decision#[k(a,b)]`; `members[0]-missing[0]-members$Decision#[k(a,b)]`. | PRE present in prepare. Both count signatures selected in closure:0; repeated exhausted selection loses the ternary in closure:1. No-flags emitter control retains both and independently checks its 54-hypothesis goal. Production already retains selections. | **62**: flags 4x8; C4:3,C7:4,C9:1,C11:4,C14:4,C17:4,C33:2,C45:4,C61:1,C70:2,C74:1. [Every phase](track-p-six/ten-sixtysix/c10-all-audit.json). |
| **11** | **27/32**. C2(64*wMeet+a); C4(4096*wMeet+64a+b); C9(0); C11(a,b,c,d),(a,b,pmaxr,pv); C14(wMeet,k(a,b)); C33(a,b,pv); C45(wMeet,a,b); C70(wMeet,pr,a); C74(wMeet); ?rowOk(k(a,b)). | wDiff: `can$Vote$members#[k]-can$Vote$members[k]`; wMeet: `members$Qs[0]+can$Vote$members[k]-size` (unit -1). | C9 and both C11 tuples prepare. C2,C4,C14,C45,C74 and rowOk at closure:0. C33(a,b,pv), C70(wMeet,pr,a) missing when shared generation reaches65536. | **51**: flags 4x10; C2:1,C3:1,C4:1,C10:3,C14:1,C17:1,C33:2,C45:1. [Exact recorded audit](track-p-six/c11/c11-current-emission.log). |
| **17** | **19/22**. C17(a,b); C3(k(a,b)); C45(wNew,r,v). | wNew: `members[0]-missing[0]`. | First two PRE tuples prepare; C45 never selected generically, appears in closure:0 with hand cert. Needed count signature exists at base/full pool index2 but polarity-only selection omits it. | **69**: flags 4x8; C2:3,C4:4,C7:4,C9:1,C10:3,C11:4,C14:4,C33:2,C45:4,C61:3,C70:2,C74:3. [Exact diff](track-p-six/seven-seventeen/c17/diff.json). |
| **33** | **21/21**. C33(a,b,c); C3(k(a,b)),C3(k(a,c)); C61(b),C61(c). | **Empty** reads/instances/picks. | No final missing PRE. C61(b),C61(c) first closure:0; other three prepare. Generic final goal also independently checks (98 raw/106 encoded), so this is avoidable context/selection cost rather than unsupported semantics. | **77**: flags 4x9; C2:3,C4:4,C7:4,C9:1,C10:3,C11:4,C14:4,C17:4,C33:3,C45:4,C61:1,C70:2,C74:4. [Normalized phase ledger](track-p-six/thirtythree/emission-diff.json). |
| **66** | **18/18**. C45(w,maxr,v); C3(64*maxr+v). | **Empty** reads/instances/picks. | Both tuples absent throughout generic all/no-flags and fixed-empty controls, even with work remaining. Actual free PRE read `Vote[4096*w+64*maxr+v]` occurs in nonquantified `step.flags.proposes`; complete matching yields C45, whose Proposal read yields C3. This is a real missing source class, not a projection or new lemma. | **60**: flags 4x6; C2:4,C4:4,C7:4,C9:1,C10:2,C11:4,C14:4,C17:3,C33:1,C45:4,C61:1,C74:4. [Every phase](track-p-six/ten-sixtysix/c66-all-audit.json). |

[**Every one of the 383 extra PRE tuples**](track-p-six/EXTRA-INSTANCES.md) is named explicitly, including each individual flag argument. Full count mappings, semantic witness normalization, and phase lists remain in the linked JSON. Certificate directories: `track-p-six/seven-seventeen/c{7,17}`, `track-p-six/ten-sixtysix/c{10,66}`, `track-p-six/thirtythree`, and the previously exported `track-p-certs/c11`.

### Shared mechanism to test

Use **live obligation/transition reads and selected count witnesses** as source anchors; instantiate whole original laws, including all guards. Complete free transition reads must participate even for scalar targets; their newly exposed primitive reads need ordinary range closure. Delay broad quantified-flag seeding and speculative discarded cold count witnesses. Primitive targets should try primitive support before optional counts, but must retain a count fallback: C7/C17 demonstrate that a primitive POST can still need transition count reasoning. First measure and replay the exact production selector/reservation path, rather than implementing fixes for research-only selection loss.

## C11 phase profiling: zero final tree depth was not zero CDCL decisions

Pinned boat large, AMD Ryzen 9 9950X, 2 of 8 vCPUs, exclusive placement with zero co-tenants. Every request retained the same 1500ms counted allowance and <=2500ms wall ceiling. These are single fast-loop diagnostics, not a 60-second benchmark. Batch queue time was 637s; actual job time was 8.8s total and is not confused with proof time. Source: `research/track-p/profile-step.ts`; complete receipts and serialized input packs: `runs/track-p-phase-profile/`.

| Mode | Final result/context | Total wall ms | Instance generation | Pool | Selection | Closure | Encoding | grow/search |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| Historical replay, exact 99-hyp failure | unknown; lost count selection after work exhaustion | 959.15 | 19.68 | 2.84 | 3.94 | 3.96 | 6.15 | **911.68** |
| Retained initial two count instances | unknown, 85 hypotheses | 936.13 | 22.44 | 2.68 | 2.00 | 2.42 | 2.07 | **903.69** |
| No blanket initial flags (still simplified replay) | abstract SAT, 52 hypotheses | 239.73 | 19.36 | 3.89 | 4.10 | 5.72 | 5.95 | 190.33 |
| Checked hand request | **tree, checkMC=true**, 32 hypotheses | 175.94 | — | — | — | — | 0.64 | **141.42** |

The 99-hypothesis run made **12,556 CDCL decisions and 216 conflicts in 3 sessions**. Their first decisions occurred 28.47ms, 10.03ms and 8.85ms after each session's search began. CDCL setup total was 0.16ms; Boolean propagation was 7.28ms; reader row construction 140.58ms; theory solve 269.57ms (including 179.65ms FM leaf work); ordering 123.45ms; bound extraction 70.55ms. These nested diagnostic timers must not be summed as disjoint phases. The final `0 case splits deep` refers to the plain proof tree's current depth, **not** the number of CDCL decisions. Thus the premise that C11 spends its allowance before the first decision is falsified. Most wall time is search over the admitted context, not instance preprocessing.

Retaining the count view removes the replay bug but does not close C11: its 85-hypothesis search still makes 5,293 decisions and 172 conflicts. The hand request makes 554 decisions, 112 conflicts, and checks. The next generic work is to supply the exact transition/selected-witness source closure with fewer irrelevant premises; merely speeding preparation or preserving a stale selector is insufficient. The exact production-attempt baseline below independently separates the real remaining gaps from replay artifacts.

The optional diagnostic counters passed their timing-on/off verdict and kernel-check regression (`cdcl-counters.log`: 1 test, 9 assertions). The trusted checker `kernel/kernel.ts` is unchanged.

## Faithful production-attempt baseline (before demand-driven changes)

The extracted `countedAttempts` closure preserves production keyed-input filtering, primitive-vs-count selector choice, reservation, MBQI and proof search. Its fixed-family baseline checked **10/12** INIT/STEP requests for the six investigated targets; this is not yet a full-38 result.

| Target | INIT | STEP | STEP wall ms |
|---|---|---|---:|
| C7 | checked | checked | 399.28 |
| C10 | checked | checked | 140.48 |
| C11 | checked | unknown | 1101.47 |
| C17 | checked | checked | 151.10 |
| C33 | checked | checked | 172.60 |
| C66 | checked | unknown | 883.05 |

Thus four historical open STEPs were artifacts of the simplified replay. C11 still has a real context/instantiation problem; C66 still lacks the free transition-read source. Baseline receipts: `runs/track-p-production-baseline/`. All returned proofs were rechecked with `checkMC`. Its initial strict check found six TypeScript diagnostics in three newly added audit-only scripts; those explicit undefined-return/binding checks have been repaired, with the next full check pending.

The next test batch uses one generic rule for both remaining gaps: no blanket initial flag terms for supported goals, no discarded cold count-witness preparation, complete free reads reachable from the target's actual updates, and whole original range laws at exact PRE reads exposed by that closure. Existing selector/reservation code and every proof budget remain unchanged.

## Demand-driven fast loop, first implementation

`runs/track-p-demand-v1/` returned **35/38 checked**, not acceptance. C66 flipped to a checked production proof (201.94ms), confirming the missing free-transition-read source. C11 remained unknown. C14 and C45 failed in this full replay after blanket flags were removed; C14's source needs its own root-key flag argument, not an arbitrary input seed. This failure is not hidden or called a final wall.

The regression suite was 43 passed / 2 failed (1127 assertions). One new test had an invalid forward flag reference in its synthetic machine; declaration order is corrected. The other correctly caught cold constant range reads consuming all four slots: kind closure is now restricted to newly matched original premises, retaining the previous cold-read guardrail. The nonisolated full check timed out at 60s without a compiler diagnostic; the next check is isolated.

Next mechanism (implemented for the second replay): derive quantified flag arguments from corresponding actual root reads, retaining the flag's original fixed globals and all guards; cache count proposals by exact count-read spellings plus declarations and the unchanged POST, rather than invalidate them merely because another PRE tuple repeats an existing count read. Reservation and final checking still run against every current goal. No selector, source cap, proof budget or trusted rule was changed. `demand-v2` reruns the full 38, regression tests and an isolated full check, and retains source-bound failure packets for the next comparison if needed.

## Demand-driven second replay and remaining validation

`runs/track-p-demand-v2/` checked **37/38**, including all six originally open STEPs. C11's production counted-pass proof checked in 183.47ms; C66 in 147.46ms. C14 also recovered. C45's combined counted-pass attempt exhausted its allowance before the two-hypothesis INIT goal; a separately checked INIT still passes. This replay had forced pass1, whereas production ordinarily tries pass0 then pass1. The next replay now uses that actual order, sharing the same 1500ms deadline—not granting a second allowance.

TypeScript passed. Lint found nine audit-only unused-variable/type-formatting issues, now fixed. The support suite's only failure was a test requiring one AST addition order for an affine remainder; it now checks the exact normalized term and separately requires the entire original flag body with the emitted term, including unchanged fixed globals. No assertion about guards or nonaliasing was removed.

A further code review found the complete two-read, current-witness join was still rejected unless its tuple happened to mention a write-key variable. The existing stale/wrong-map test only used such a write anchor. A new no-write-anchor variant passes after correcting that eligibility guard; stale, different-witness and wrong-map controls still pass (`runs/track-p-live-join/bridge-controls.log`). Its focused production C11 replay also checks (361.38ms). This is a source eligibility repair, not an added premise, coordinate equality or larger budget.

## C45 follow-up: corrected hypothesis and next mechanism

The ordinary pass order **did not** fix C45. The initial two-hypothesis INIT timeout was a symptom: the new before-decision observation shows the allowance goes into a 47-hypothesis STEP decision search. Shared-slot correctness probes return unknown; their wall times are not benchmark claims (`runs/track-p-pass-order-probe/`, `runs/track-p-relevance-probe/`).

The existing relevance path skipped the 19-law family entirely because its early return was `laws.length <= 24`, despite having a 12-law tier. Allowing that existing tier gives a 39-hypothesis query, but it also remains unknown (`runs/track-p-relevance-medium/`). Its regression test passes. This does not justify a production-success claim.

The retained C45 packet exposes a concrete source-priority defect: all four range slots for its second root map are consumed by ambient/transition terms before the actual root read gets a range. The next change ranks exact root and reachable free-transition reads ahead of ambient reads, within the unchanged four-per-law and 64-total caps. A direct whole/subset `grow` control of the saved query runs alongside that focused test. No guard or packed-coordinate equality is added.

The isolated v3 suite waited unplaced for 13 minutes; that zero-placement interactive batch was explicitly closed before resubmission as a gate. The gate batch remains pending behind shared worker work. Focused probes use shared boat slots and are labeled correctness-only.

## C45 direct-search control and bounded preflight

The range-priority regression passes, but that priority fix alone does not close C45. The same saved, unchanged production STEP query **does** close through `grow`: full 47-hypothesis goal and both relevance subsets check after lifting back to the original goal. In particular, the 22-hypothesis subset produces an original-context checked certificate. These are shared-slot correctness controls, not isolated timing claims (`runs/track-p-range-priority/c45-captured-grow.log`). The serialized control is `runs/track-p-certs/c45/{goal,proof,source}.json`.

The next generic change uses one sixth of the existing attempt allowance for one relevance-first `grow` before model construction, only on supported goals with no current count witnesses. A subset model is ignored; only a tree widened to the exact whole STEP can be reused. The producer also keeps an actual tree returned by decision search rather than growing it again. Neither path raises an allowance or changes kernel acceptance. A true-invariant/false-update regression and the full 38-obligation replay are now queued.

The isolated gate batch expired without placing any item and was explicitly closed. The new suite uses available shared boat slots for correctness only. Strict isolated 60-second runs still remain required.

## Full fixed-family closure

`runs/track-p-preflight/family38.log` and the corrected `runs/track-p-preflight-v2/family38.log` both report **38/38 checked**, with **`closedFamily: true`** from `checkCountedLaws` on the assembled 19-law certificate. This is the production attempt implementation and ordinary pass order, not the old simplified replay. These are shared-slot correctness results, not 60-second whole-harness results.

After correcting three strict typing issues and a test-only bound-name collision, **49 targeted tests pass (1191 assertions)**. The serialized C45 certificate independently authenticates with zero search, and an empty-tree corruption is rejected (`runs/track-p-preflight-v2/c45-auth.log`; goal SHA256 `d1d6bc84db235a1c968f4572df7d9abf237a9d5028ee7e3b69990403d6e635d0`, proof SHA256 `7c6d353a29a46825a6a55f38a3f0aeaccf21e18106e52c085c38ad86cdb1656c`).

The combined type/lint command hit its shared-slot wrapper's 210-second execution limit without a diagnostic. It is being rerun with an appropriate compile-only deadline; no prover allowance changed. The original-harness target and all subsequent merge gates remain pending.

## Integrated admission after fixed-family closure

The first new isolated original-harness diagnostic is **unknown at 137,507ms**, not a pass. `runs/track-p-integrated-v2/placement.json` records one large VM, all 8 vCPUs pinned, no co-tenants. This uses the repository's whole-large-VM resource shape; the earlier one-slot timing request never placed and was closed before replacement.

Production still generates **19/19** reference-family formulas among 77 candidates (`generation-comparison.json`). The retained ledger has 647 root queries: 124 proved (4,320ms), 96 unknown (13,849ms), and 427 satisfiable (51,348ms). Total query time is 69,517ms; traced admission attempts total 100,490ms. The 37,017ms outside traced attempts must not be called generation time: this capture did not wall-timestamp generation. The full top-ten table is `timing-accounting.json`.

The failing scale is now the 77-candidate admission context, not derivability of the 19-law family. Current law-level relevance ranks many same-map empirical cubes before count and transition support; for the caller safety law, the 12-law tier contains none of the other checked-family laws, and its 24-law tier contains only one. The next fast-loop experiment compares the actual full context, existing law tiers, and a generic source/transition-width core. No hand-selected family is substituted into production. Three clean target repeats and all later merge gates remain unrun.

## Wide-context controls and witness ownership

The alpha-matched generic source/transition core contains 45 of the 77 candidates and all 19 reference formulas. At the original initial 779ms share it checks 18/19 laws; C11 is the sole remaining failure (`runs/track-p-core-context-v2/`). A 1500ms diagnostic identified **`reservation different witness owner`**, rather than merely a time or work-cap exhaustion (`runs/track-p-c11-rejection/`).

The producer now preserves every live owner and alpha-renames only an independent regenerated cold binder that reused its spelling. Any use of that binder in a read, bound, or pick still rejects; duplicated owners and captured/source names still reject. The focused regression passes all eight assertions (`runs/track-p-owner-focused/owner-test.log`). C11 no longer raises that reservation error but still does not close in this wider context: its counted queries grow from 97 to 202 hypotheses. This is a repair, not a target pass.

Research-only proof-directed admission did not close: treating every emitted instance as a dependency needed 176 queries/full-context or 82/needed-first; inspecting actual tree premise use reduced this to 28 queries, but C11 still failed before its own prerequisite closure was present (`runs/track-p-demand-admission/`, `runs/track-p-demand-used/`). No experimental admission policy has been enabled in production. The next controlled mechanism is to warm the existing structural prefix/carry proofs before demanding count guards, then follow only actual proof dependencies. It retains the original allowance helpers and requires a final `checkCountedLaws` closure; it is not allowed to substitute the known 19-law list.

### Ownership repair checkpoint

The full type/lint command passed (`runs/track-p-owner-validation/check.log`, snapshot `2168180817ed`). A shared-slot regression run timed out in two existing multi-proof carry tests; the isolated rerun passes **56/56 tests, 967 assertions** (`runs/track-p-spine-v2/targeted-isolated.log`). The first shared family replay was 36/38; the isolated replay after making collision dependency scanning lazy restores **38/38 and `closedFamily: true`** (`runs/track-p-owner-isolated-family/`, snapshot `abb62a4698e6`). These fixed-family results are not integrated timing claims.

Warming every structural candidate did not solve admission: both warm variants still failed after 46/53 queries. A definition-source frontier reduced wasted calls but also remained open. The remaining controlled question is which additional candidate sources perturb an otherwise checked C11 proof; the next fast-loop comparison adds each extra source separately to the same generated 19-law control. No experimental admission scheduler is enabled in production.

## Single-source contamination and source-budget diagnosis

The next control uses the *generated* 19 formulas, not the handwritten family. All four 779ms controls checked C11. Adding each of the 26 other generic-core formulas separately produced six failures (`runs/track-p-contamination/summary.json`). Candidate order alone is not the cause: both reference-order and production-order versions of the same generated 19 checked (`runs/track-p-order-control/`). Four failing additions exhausted the ordinary pass before any counted query; two reached 68/70-hypothesis counted queries, with the expected two count instances still present. Count-first made the 19-law controls faster but did not close either the 45- or 77-law context (`runs/track-p-count-first/`).

A replay anchored at the actual negated POST, rather than the final appended count axiom, also did not prove the wide goal. Its subsets were satisfiable: the final wide source table was missing the required co-write tuple at the actual intersection witness. Thus further hypothesis ranking alone is not justified (`runs/track-p-anchored-v2/`).

Direct preparation measurement shows why a live-source phase can be starved: the 77-law context admits **64/64** sources before any count witness exists; the 45-law context admits 46. Its ordinary pass also admits 64/64. These are measured counts, not an inferred timeout (`runs/track-p-initial-source-budget/`). Reserving half of the same 64 slots until witnesses exist, prioritizing exact same-witness read/read joins, and restoring selected entries from their owned semantic identities preserves the checked family, but does **not** by itself close the 45-/77-law contexts. The first-query snapshots show both still consuming 64/64 sources before the necessary C33/co-write instances arrive (`runs/track-p-live-source-probe/`). Restricting speculative cross-map slots also regressed C7 and was reverted.

The next generic rule operates on the **source context**, not proof budgets. It expands the target's actual count definitions, keeps keyless count sources and structural support, avoids derived binary source families duplicated by a direct family of the same footprint/arity, and filters unrelated primitive state guesses and clauses wider than any concrete update key. The resulting C11 context has **26 laws**, selected without protocol names or reference-family indices. In the standalone control it checked in 328–431ms; the old 45-/77-law searches remained unknown.

Production now tries such a context first inside the existing counted-attempt allowance, then widens and calls `checkMC` on every full-context obligation before returning the proof. Failure falls back to the original context while allowance remains. Count-bearing and multi-coordinate goals with structural support try the counted pass before the ordinary pass; no-support scheduling is unchanged. With this path, C11 checks against **both 45 and 77 original laws** in 540ms and 516ms respectively; **38/38** unchanged-family obligations check; **48 tests / 933 assertions** pass (`runs/track-p-context-integration-v2/`). These are not three-repeat acceptance results. The subsequent original integrated harness returned **unknown in 77,449ms**, with 34 candidates remaining (`runs/track-p-context-integrated/`, snapshot `8739cfe06fe7`). The strict C11 law initially survived; later, at the 38-law Houdini context, both it and C45 were dropped and safety subsequently failed. The captured machine and all 77 initial laws are byte-for-byte identical to the fast-loop fixture, ruling out fixture drift. At 38 laws the initial two-thirds size gate disables the useful 26-law source context. Removing that gate alone was insufficient when a fixed half-share cut off a valid local proof. Giving the preferred context the existing remaining allowance (no deadline extension) checks C11 at the exact late 387ms budget and against all 77 laws (`runs/track-p-late-context-v3/`). The exact C45 packet also checks in direct tree search (24–39 hypotheses, 91–184ms), while the old path spent only one sixth of its allowance on a truncated preflight and then timed out in model construction. Small, already-reified goals now receive full-goal tree preflight, capped by the original attempt deadline. The late 38-law C45 request checks in 200ms and the full 77-law request in 270ms; C11 still checks across those contexts at the same captured 387ms allowance (`runs/track-p-packet-probe/`, `runs/track-p-direct-preflight/`). The frame-only context remains research-only; no special C45 rule was added. This preflight change passes `bun run check`, **38/38** family obligations, and **48 tests / 946 assertions** (`runs/track-p-direct-preflight-validation/`, snapshot `9a66101e8de3`). The type/lint check and 38/38 replay passed at checkpoint `285dfd9cca17` (`runs/track-p-context-validation-v2/`); the final count-demand refinement also passes type/lint, **38/38**, and **48 tests / 937 assertions** at snapshot `48e47f296abf` (`runs/track-p-context-validation-v3/`).

## Dependency-closed candidate admission

The first bare, no-capture run after the preflight change was killed by the strict 60-second limit (`runs/track-p-direct-bare/`). The next fast-loop control showed why merely proving more isolated obligations is insufficient: a caller certificate can use a stronger but false empirical helper, then fail when that helper is removed. After removing two such guesses, the full 75-law caller context failed while a generic 45-law context—caller laws, structural sources, count laws, and primitive relations within concrete write width—still checked.

The new admission loop first proves callers in that generic coarse context, then follows the actual hypotheses used by their certificates. It proves the transitive dependency set, invalidates certificates whose required helper is dropped, and transports all surviving proofs to one retained family before `checkCountedLaws`. Unknown or missing dependency analysis falls back conservatively. No-support search keeps the original scheduling; budgets and all final kernel checks are unchanged.

The research pilot closed 26 laws in 18,195ms. The exact production admission entry point then closed **26 checked laws** from all 77 candidates in **20,722ms**, and from the post-drop candidate set in **13,590ms** (`runs/track-p-admission-replay/`). These are query/admission replays, not complete harness timings. Validation passes `bun run check`, **56 tests / 987 assertions**, and **38/38** unchanged-family obligations (`runs/track-p-admission-validation/`, snapshot `4269e72bd2c6`). The original strict, no-write harness is being measured again before any repeat or merge-gate claim.

## Gates and disposition

The target has not passed 3 x strict 60s. Thus later paired IC3Syn 29 x 3, DuoAI ten paired, 29 broken, seven test shards, and quick-bar gates were **not advanced or claimed**. No main-branch merge or publish action. Checked hand proofs establish that the C9/C11 barrier is search scheduling/instantiation, not an unsupported trusted lemma.
