# Track P report

Base: `40693c7a`; branch: `claude/track-paxos`.

**Status: the original production target passes all three strict 60-second repeats; the first paired IC3Syn gate found six protocol regressions, now under fast-loop investigation.** The initial failures below are retained as history. The engine uses no injected historical law, trusted-checker change, or larger proof budget. No gate success is inferred from scheduler exit status.

## Implementation

- Integrated the supplied generic carry, scan-prefix, and counted-support generators and their tests. Prefix generation is consolidated in `core/carry.ts`.
- Added `core/relevance.ts`: bounded deterministic relevance subsets, lifting trees and count certificates back to the exact full context. Subset failure or SAT is not a whole-context result. The old fixed-size 12/24-law tiers remain opt-in; the verified definition-local source context is enabled for structurally supported count goals.
- Improved selected-count proposals: relevant keyless before/after/incoming comparisons, upper-bound nonincrease/overlap priorities, live referenced-read projection, and exact affine remainder matching. Complete original guarded laws are instantiated; no packed-coordinate equality is assumed.
- Start with preferred existing count instances when seeded bounds exist; retain the lazy pool. Deduplicate symmetric complete instantiated term premises rather than filling source slots twice. Reuse count proposal pools when only primitive PRE support grows; follow count-dependent flags transitively for invalidation. Every retained view is reified and final certificates are checked.
- Archival duplicate files in `research/claude-import/` are excluded from type/lint discovery, not from integrated engine tests.
- No trusted-checker, Lean, model, original-law, proof-budget, or external-solver change. `kernel/cdcl.ts` has optional search-phase timing counters only (disabled by default), with an on/off verdict and checked-tree regression. Structurally supported count and multi-coordinate goals now try the counted pass first; unrelated no-support scheduling is unchanged.

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

The original no-write harness first returned **proven in 50,290ms** (`runs/track-p-admission-bare/`). Three subsequent clean process repeats, all at the original 60,000ms budget and under an external `timeout -s KILL 60s`, returned:

| Repeat | Harness verdict | Harness wall ms | Retained laws | Strict exit |
| --- | --- | ---: | ---: | ---: |
| 1 | proven | 46,924 | 26 | 0 |
| 2 | proven | 36,420 | 26 | 0 |
| 3 | proven | 38,898 | 26 | 0 |

Receipts and `placement.json`: `runs/track-p-strict-repeats/`, tree `00fa79612bed`, large VMs, all eight vCPUs pinned, **zero co-tenants**. No diagnostic capture or hand-written invariant was passed to the harness. Production implementation checkpoint: `38cfd68c`.

The paired IC3Syn **29 x 3**, DuoAI **ten paired**, **29 broken**, **seven test shards**, and quick-bar gates are now in progress against main `40693c7a`. They are not yet claimed as passed. Manifests are generated by `research/track-p/make-gate-jobs.ts`; paired jobs alternate candidate/base order, use the same VM for both sides, and cap each side at the unchanged 60-second limit. No main-branch merge or publish action has been taken.

### First regression-gate pass (not acceptance)

The local coordinator deadline expired at 1,000 seconds. The scheduler had durable receipts for all **87 IC3Syn pairs** and **10 DuoAI pairs**; these were recovered without rerunning the jobs, retaining exact stdout/stderr SHA256 hashes and original placements (`recovery.json` in each suite directory; `research/track-p/recover-batch.ts`). One IC3Syn pair had no usable verdict log and is incomplete.

The first paired pass is **not green**: candidate 66/87 versus baseline 79/87, with losses on `consensus_epr`, `consensus_forall`, `consensus_wo_decide`, `majorityset_leader_election`, `naive_consensus`, and `simple_election`. The three Paxos pairs are gains. All ten DuoAI pairs prove on both sides. The common symptom in the six losses is a primitive point-guard support activating the new count-specific admission path even though no structural support law reads a declared count. The next fast-loop test retains all generated candidates but enables count-specific scheduling only when the structural support actually uses a count.

Four co-tenant test shards failed, mainly at Bun's default wall timeout. An isolated same-VM main/candidate control of the search and Python-reader tests passes, as do the isolated carry tests, with no budget or assertion changes. All seven shards are being rerun on exclusive VMs. The initial broken suite had 24 returned non-proven verdicts and five outer supervisor timeouts: the runner subtracts 30 seconds from a job's configured timeout. Those five are retried with enough supervisor overhead to record the unchanged strict 60-second inner timeout. The quick bar also lost its local coordinator and is not claimed complete.

### Semantic support roles

Disabling count-specific scheduling for primitive-only support restored five of the six failed families in captured-candidate admission. For the remaining `consensus_forall` family, retaining the two added primitive guards still lost its ordinary proof; using the original 46-candidate family restored **three checked proofs**, in 23,565ms, 16,972ms and 10,553ms (`runs/track-p-primitive-isolation/`). The generic production rule now preserves the ordinary candidate family first unless an active structural support law reads a declared count. Primitive-only proposals may widen a failed ordinary search, but do not replace it. The original shared deadline remains unchanged. Names and protocol identities are not inspected.

The role change passes **57 tests / 1,005 assertions**, and the captured Paxos admission still closes 26 checked laws in **11,120ms** (`runs/track-p-support-role-validation/`). Initial full checks found only typing/lint issues in newly added research scripts; these were repaired before the next validation sequence. The prior implementation's isolated seven-shard rerun passes all seven shards (**745 tests**), and all 29 broken variants remain non-proven: **11 refuted, 16 unknown, 2 strict timeouts**. The full gate sequence will be rerun on the role-fix commit, with each gate required to pass before the next launches (`research/track-p/run-gates.sh`). The first restart stopped correctly at the tooling check: two concurrent checks hit their 210-second worker limit. The check job is now isolated with a longer tooling-only supervisor cap; all prover budgets and strict target limits remain unchanged.

The direct-count-only role test was too narrow: all three renewed strict target runs timed out. The target's essential scan/global guards support count proofs through global state and quantified definitions, without directly reading a declared count. The refined, still generic role test therefore keeps a count read **or a non-pointwise mutable-global-state condition**. Constant tautologies do not qualify. The frozen replay now goes through the production role selector, avoiding the earlier test blind spot. All six regressed families check with that selector (`runs/track-p-global-context-regressions/`), while the full 77-candidate target retains its structured support and checks a 26-law family (`runs/track-p-global-context-validation/`). Type/lint and the targeted tests pass. The complete sequential gate run will be repeated on this refinement. Its first restart passed the full check and returned target proofs at 21,212ms and 32,236ms with identical search work; one worker hit its outer 60-second cap without a verdict. The worker cap incorrectly included dependency installation as well as the inner strict harness limit. The supervisor now leaves setup overhead outside that inner limit and logs setup/harness boundaries; the actual harness is still killed at exactly 60 seconds. No assumption is made that the missing verdict was a proof.

The separated supervisor confirmed one genuine 60-second harness timeout, alongside two proofs; setup took under one second. Current generation-only controls account for **21.5–34.4 seconds**, dominated by small-state sampling (9.9–16.2s) and cube inference (10.5–16.9s), with zero root proof queries and all 19 formulas still generated. Frozen admission profiles showed repeated broad helper attempts consuming additional time. Applying the same goal-local coarse context to each required helper, always including that helper and retaining full-context fallback, closes **25 checked laws in 27 attempts** rather than 26 in 33. Three research controls took **6.4s, 7.8s and 13.2s**; the exact production replay took **10.4s**. The unchanged checker accepts the smaller family. Type/lint and 57 tests / 1,011 assertions pass (`runs/track-p-helper-context-validation/`). No budget or sampling coverage was changed.

---

# Track M — implementation log (2026-11-07)

Base: `40693c7a`, branch `claude/track-mldr`, worktree `gdp-wired-trackM`.
All substantive computation below ran on boat. No trusted-checker, Lean,
proof-budget, or safety-law change has been made. The untrusted search/proposal
code is changing. This is **not** a completed target/gate claim.

## Diagnosis

The production capture at `../gdp-wired/runs/claude-capture-v1/out/mldr-capture.log`
contains 23 laws, ending unknown on `one primary per term`. Its candidates express
kind/range and zero/nonzero cubes, but not the published relational/count family.

Published reference: Endive `8b6f2abd1988eeb308f965813635e9871f253e2d`,
`MongoLoglessDynamicRaft_IndProofs.tla`. Source receipt:
`runs/track-m/diagnosis-v2/source.log`. The archived translation and Step 0 report
were recovered on boat from `gdp-wired-paused-20261103` /
`gdp-wired-dbae-astra.tgz`, SHA256
`f9cc6b4b98e70c6c7d7f799e56086295f89e3655c2e89e8e195eda3c1f993556`.
Correct-path receipt: `runs/track-m/atomic-v1/published.log`.

| Clause | Shape required | Candidate status |
|---|---|---|
| TypeOK | role range; positive metadata; nonempty initialized rows | kinds cover role; remaining floors/cardinality not all generated |
| Safety | two primaries at equal current term have the same key | unchanged caller law |
| Inv866 | role-guarded equality of two numeric fields at one key | new generic field family |
| Inv3915 | role guard + equal first field across keys implies second-field order | new generic field family |
| Inv1758 | equal two-field metadata tuple implies equality of relation rows | new generic tuple-row family |
| Inv2973 | two active relation rows have overlapping majorities; inactive alternative determined by an ordered-field-qualified count | missing generic count/disjunction family |
| Inv3246 | every majority of an active row meets a field-order-qualified subset, equivalently a cardinality bound | missing generic count/disjunction family |

The row predicate is a three-key universal formula, not a Boolean two-literal
cube. The last two clauses need state count definitions as well as new laws.
All proposed field/row laws still pass sample filtering and ordinary checked
induction; no published law is imported into the engine.

## Port correction

`research/track-m/port-audit.ts` executes the old port's real transition function:
init; `pick S={0}`; `copy i=0`. Equal config terms/versions then coexist with rows
`{0}` and `{}`, so Inv1758 is false. Receipt:
`runs/track-m/port-audit-v1/phase-counterexample.log` (also reproduced in focused
suite). Historical factory is kept only in `research/track-m/phased-mldr.ts`.

The old port's projected BFS nevertheless has 5,362 states / 18,327 nonstutter
edges, 0 bad states, while the broken variant reaches 5 bad states:
`runs/track-m/diagnosis-v2/port.log`. Therefore projected correspondence alone did
not establish that intermediate auxiliary states satisfy source invariants.

New `research/protocols/ic3syn/mldr.ts` uses native tuple relation keys, one atomic
Init request, and one step per subsequent source action. `models.ts` uses it
through the original harness and updates only MLDR's request enumeration and
projection. Source fields reset together at Init; no source invariant is assumed.
The strict-majority broken variant remains. `runs/track-m/atomic-v2/tlc.log`
confirms TLC and the new port both have **5,362 states / 18,327 edges / depth 10**,
with no bad state. The new port has only 5,363 raw states (one dummy plus source
states); the broken variant reaches 5 bad states at depth 3.

## Tests and failures

- `runs/track-m/diagnosis-v2/fields.log`: 63 initial field templates, 5 survive
  samples (32/1,504 states); direct field equality and its two order consequences
  were checked. The printed `proven:true` there concerned **kind laws plus generated
  helpers only, not safety**. That diagnostic no longer runs a full search.
- `runs/track-m/focused-v1/tests.log`: **8 tests pass**, 0 fail, 39 expectations.
  Covers positive checked field proof, broken write rejection, scope/capture,
  deterministic generation, ambiguous-domain refusal, row candidates, atomic
  initialization, actual majority election, and the broken-majority control.
- `runs/track-m/focused-v1/check.log`: **`bun run check` passes** (0 warnings/errors).
  Vendor sources are supplied from the pinned main submodules using `--data`.
- Earlier static check failed because the initial worktree snapshot contained no
  vendor submodule sources (`diagnosis-v2/check.log`). Not an engine regression.
- First new-port correspondence attempt stopped before TLC: the runner already
  mounts `/src/gdp-wired` read-only, so creating a symlink there was wrong
  (`atomic-v1/tlc.log`). Retried without the symlink.
- `atomic-v1/check.log`: typecheck passed; type-aware lint subprocess was SIGKILLed.
  `focused-v1/check.log` subsequently passed. A latest-tree retry requests 4 CPUs /
  14 GB explicitly.
- `published-v1/given.log`: research audit failed to parse (extra parenthesis);
  no proof result. Fixed, and shell changed to `set -e` so packaging cannot mask
  this failure. The next attempt exposed missing count references in law scope;
  explicit `MapRef`s fixed that research-only construction error. Completed
  audits and their failures are below.

## Final diagnostic / named wall

The five published clauses are translated only in `research/track-m/published.ts`
for a given-family inductiveness diagnostic (`GDP_COUNTS_GIVEN=1`, ordinary
`proveRule(..., {search:false})`). Note: the existing counted branch of proveRule
still invokes counted search even with `search:false`; GIVEN disables extra
candidates, not checking. The final fixture also includes explicit TypeOK role,
relation range/domain, positive version and initialized nonempty configuration
clauses. These are research callers only, never engine facts.

`diagnostic-v3/given.log` showed all eight then-supplied clauses true on 141/1,767
sample states but no checked full family. A concrete completeness bug was isolated:
`certFor` found known count members only at whole map keys, not in tuple key
components, and proposed no singleton lower bounds. `count-witness-red` fails that
specific test. The implemented structural member-key proposal plus singleton
picks passes it through **checkMC**, while the wrong-row negative case stays
unprovable. This changes only untrusted certificate proposals.

- `witness-fix-v1`: full static check and **59 focused tests pass**. The complete
  11-clause given family still fails safety/Inv1758/Inv3915/Inv2973/Inv3246; importantly,
  **nonempty configuration after Init now proves**, unlike before the fix.
- `region-fix-v1`: integrate existing untrusted Boolean-region **three-count
  partition** certificates into the wide pool (same cap, same budget, unchanged
  checker). Static check and **60 tests / 957 expectations pass**; includes the
  new checked partition identity and frozen count/countermodel fixtures. The same
  five target obligations remain open.
- `replay-v1/nonempty.log`: old captured 51-hypothesis goal is SAT in 157 ms;
  it lacks the newly generated picks. `replay-v1/row-agreement.log`: old captured
  251-hypothesis Inv1758 goal remains unknown after its 7,500-ms counted allowance
  (1,876,416 work). These are standalone `grow` replays, not protocol reruns.
- Final production-family diagnostics: safety reaches 13 model rounds / 1,480
  accumulated hypotheses before unknown; Inv1758 reaches 802, Inv3915 1,006,
  Inv3246 599. Inv2973 still leaves a SAT augmented goal. None of those SAT
  abstraction models is claimed to be a reachable protocol counterexample.

**Named wall:** with the port corrected and the published family supplied, the
existing bounded count/quantifier-instantiation path still does not discharge
that family. The missing automatic active-row/quorum candidate families cannot
alone close production until these explicit-family obligations flip. Further
work must target those captured count/instantiation goals, not increase budgets,
weaken safety, or assert the family as facts.

Final static/test receipt: `runs/track-m/region-fix-v1/check.log`.
Final failed-family receipt: `runs/track-m/region-fix-v1/given.log`.
Correspondence receipt: `runs/track-m/atomic-v2/tlc.log`.
Each run includes its jobs, placement and summary; relevant shipped tree hashes
are `93566a56f012` (diagnostic-v3), `412bf2630610` (witness fix), and
`b5f644aaf280` (partition fix). Raw failing goal archives are embedded as xz/base64
in the given logs, unpackable with `research/track-m/unpack-goals.py`.

No `MLDR-DESIGN.md` was present in the shared handoff at the last check. Full 3x60s
production and paired IC3Syn/DuoAI/broken/shards/bar merge gates are **not passed
or claimed**; per the handoff they were not launched without a target proof.
Track M is blocked, not merge-ready. No changes were made to main or other
worktrees, and no trusted checker/Lean change, external solver or budget increase
was made.

## Fable design — Step 0 passed (P*)

Following `private/handoff/claude-tracks-20261107/MLDR-DESIGN.md`, Section 3.
The production `mldr` port now uses P*: CV starts at 0; pick writes row 0 and
sets its CV to 1; copy writes another row and sets its CV to 1; start requires
all CVs to be 1. There are no C0/Copied/picked variables. Previous native-tuple
atomic experiments remain reproducible via `research/track-m/atomic-mldr.ts`.

- `runs/track-m/pstar-port-v1/bfs.log`: original `check.ts --only mldr --edges`
  gives **5,362 states / 18,327 edges**, raw 5,391, done true, bad 0 (37,577 ms).
- `runs/track-m/pstar-port-v1/broken.log`: original `--broken` gives bad **5**.
- `runs/track-m/pstar-port-v2/capture.log`: original 60,000-ms harness capture
  completed in 42,262 ms, with 171 queries. No C0/Copied/picked candidates;
  `never 1 <= CfgT[x] and started is 0` remains. Safety is still unknown.
- `runs/track-m/pstar-port-v2/stages.log`: sampling 46/1,205 states, 7,218 ms;
  direct candidate diagnostic finished in 28,352 ms.
- Port initialization/election regressions pass, included in the 72-test
  `runs/track-m/count-proposals-v1/tests.log` run.
- The first capture was killed at its shell deadline, and the first check had
  missing vendor snapshots. The corrected capture succeeded. Latest static
  checks found only two unreachable `cur` comparisons in the new research
  hand-set probe; these were removed before starting Step 1. Static retry pending.

Step 0 changes no source action, safety law, trusted checker, or proof budget.
The hand-set proof (Step 1) is now the gate; no new production families or merge
claims follow without it. Section 1.5 remains pending as of this checkpoint.

### SHA256 receipts

```text
4046c3bb72374cb3622ca429917a7a9156c3ba04823908fe6b10277c516957d1  core/counts.ts
5ddbfd84053b0a3ced4970fc986dc364f445d946db0f75124a903a7266c0d67f  core/field-laws.ts
ac85e04a15c1e25b2c8acc2c1352f138cd3564ce2a98cc2aa63dc9a92071dc4e  research/protocols/ic3syn/mldr.ts
71acbf0f40bc86c1e37f9f28bca5ac6dc77f0245aa0faa5aa141608a9bff1b9a  runs/track-m/atomic-v2/tlc.log
edf4b396e249396d8c5d29507ec7e923aa43702efbb235b1b2a55e15681d3f80  runs/track-m/region-fix-v1/check.log
d21ef126ad3cb849b2c102ebe68c3a37b6bb53a46b89688c6f7919bc3035acff  runs/track-m/region-fix-v1/given.log
```

## Fable design — Step 1 in progress (not passed)

Step 0 is commit `938ee238`. Section 1.5 now reports zero bounded CTIs and
zero encoding mismatches for I-A/I-B, including P*. None of the stated
fallback triggers has fired. These bounded checks are not an induction proof.

The initial explicit I-A run is `runs/track-m/pstar-hand-v1/given.log`:
`GDP_COUNTS_GIVEN=1`, 900,000 ms overall. Four laws are kept: Inv866,
Config-cell kind, p1 and p2. Safety, Inv3915, Inv1758, Inv2973 and Inv* remain
unknown; **the step-1 gate is not passed**. The captured queries and input
are in `runs/track-m/pstar-goals-v1/`.

Controlled standalone replays of the five final step goals at 5,000 ms counted
all remain unknown (`runs/track-m/pstar-replay-v1/`). Their sizes are 203, 237,
304, 334 and 243 hypotheses, respectively. The overlap goal has 293,249 AST
nodes: the current lazy pool is too large to assume that adding more instances
will improve its five-second result.

A concrete missing proposal is universal flag instances at selected count
witnesses. `core/count-witness-flags.ts` proposes those instances without changing
the checker. Its isolated regression passes (one test, seven assertions,
`runs/track-m/witness-unit-v1/witness-unit.log`). But adding all relevant flags
to the captured safety and overlap goals does **not** close either in five
seconds. The safety goal grows from 203 to 505 hypotheses; overlap from 334 to
1,329. Adding the goal's own induction instance also does not close them.
Receipts: `runs/track-m/witness-flags-v1/{safety,overlap}.log`. Broad seeding has
therefore **not** been wired into production search.

Next controlled experiments are checked action-first splits and the design's
minimal four-comparison safety certificate plus structural read instantiation.
They are research probes, not new trusted rules or claimed proofs.

The minimal safety query now **checks in 500 ms counted**, with 98 hypotheses
and four CInsts plus their witness flags (`runs/track-m/minimal-safety-v1/minimal.log`).
Without witness flags it is satisfiable; broad structural read instantiation grows
it to 1,605 hypotheses and leaves it unknown. This checks a conditional induction
goal, **not** the whole hand set. A protocol-independent focused selector and
cold-start count-law bridge seeding are being tested before integration.

The focused suite in `count-proposals-v3` passed; its static job failed because
vendor snapshots were omitted from that boat upload, not because of a reported
Track M type error. The Track M `vendor/` directories turned out to be empty;
validation now uses the populated `../gdp-wired/vendor:vendor` data path. Superseded
queued snapshots were cancelled by exact task ID.

The generic single-carried-set family reproduces the safety proof in **622 ms
counted**, 103 hypotheses and five CInsts (family 0 in
`runs/track-m/focused-families-v2/families.log`). The other family is satisfiable;
Inv3915 and Inv1758 are not yet proved by this replay. A broader cold-start
selector still timed out or returned small abstraction models. In particular,
the row-agreement capture has Inv* instances at rows `a` and `j`, but **none at
request row `i`**. The next refinement supplies those request-to-goal bridges
without enumerating unrelated row tuples.

Arithmetic-only quantified variables now remain numeric constants even when a
boundary equals a row key's current model value. The new aliasing regression and
related tests pass: 14 passed, zero failed (`runs/track-m/model-alias-v2/models.log`).

`GDP_COUNTS_FOCUS=1` enables an experimental, ordinary-kernel-checked small-certificate
recovery before growing a widened goal. It is off by default. The bounded
60,000-ms hand-set diagnostic (`focused-hand-v1/given.log`) keeps Safety through
this path: 539 ms profiled in recovery, after the main attempt reached its
5,001-ms decision cap. Inv3915, Inv1758, Inv2973 and Inv* remain unknown and the
whole call ends at its 120-second wall guard. **Step 1 is still not passed.**

The populated-vendor validation (`count-proposals-v6`) passes `bun run check`
(zero warnings/errors, 918 files) and **76 tests**, zero failures. These receipts
precede the latest focused-bridge and carried-flag refinements.

Action-local replays (`count-cases-v1/cases.log`) isolate Inv3915's remaining
failure to BecomeLeader; the other seven branches produce trees within a total
3,281 ms counted. Inv1758 still fails at Copy, BecomeLeader, Reconfig and
SendConfig under this five-second combined budget. These are partial trees,
not a checked combined proof. The next replay asks action-local models for
ordinary field-law instances and rebases all branch proofs before checking the
unchanged combined obligation.

The newest snapshot passes TypeScript and four focused regressions in
`typecheck-v1` (including column preservation). Starting from only structural
bridges reduces the two field goals to **83 / 97 hypotheses** (`cold-cases-v1`).
The row-agreement BecomeLeader branch now yields a tree, but the entire law is
still incomplete. In `core-cases-v1/cold.log`, CDCL refutes Inv3915's BecomeLeader
branch in **199 ms**, returning a 22-hypothesis core; reconstruction of that core
still times out. Thus that particular branch now has enough logical instances
for the decision procedure, but has not produced a checked proof. The next
controlled comparison enables the existing `atPoint` proof-search mode, which
these counted replays did not inherit. No new trusted rule or larger budget is
used.

`pointed-cases-v1/cold.log` constructs all eight Inv3915 branch trees in
**1,486 ms counted**, and conclusion-last ordering constructs them in 2,325 ms
(`ordered-cases-v1`). Both combined certificates were **rejected**, not proofs.
The replay was rebasing conditional trees as though their source path were empty;
that call now retains the source path. The revised replay checks each branch,
the combined ground tree, and the counted certificate separately. This is a
research-harness correction, not a checker change.

The corrected run **passes**: `pointed-cases-v2/cold.log` has all eight branches,
the combined ground tree, and `checkMC` true for Inv3915, in **1,398 ms counted**.
The standalone path-rebasing regression passes as well (`path-test-v1`). This
verified recovery is now integrated behind the existing opt-in focus flag; its
real hand-set run and new positive/negative boundary tests are running. Inv1758,
Inv2973, and Inv* still block Step 1. No Step 1 commit or later-step claim yet.

The integrated `focused-hand-v2` diagnostic keeps both Safety and Inv3915. It
still returns `proven: false`; the full attempts also exceed the desired
five-second step budget, even where the focused recovery itself is below it.
`typecheck-v2` passes TypeScript and seven focused tests. This is not the final
validation snapshot.

`row-cores-v1` isolates the remaining row-agreement actions. The SendConfig
branch checks in **1,177 ms counted** (722 ms model/core query, 455 ms tree
reconstruction). Reconfig is refuted by CDCL with an 11-hypothesis core but is
not reconstructed within budget. Reordering that fixed core ten ways does not
produce a checked Reconfig proof (`row-order-v2`); the copy core checks in every
ordering. Explicit row-alias splits also do not close Reconfig (`row-alias-v1`).

The count-law probes expose further missing proposals: packed count-key
coordinates were omitting the second row from phase-law bridges; higher-arity
count laws need copied-row instances that preserve their arithmetic witnesses;
and the focused selector was dropping all three-/five-term partition and union
instances. New proposals address these structurally, without adding axioms.
Broad post-frame/structural pools still overwhelm the counted goals
(`count-frames-v1` through `v4`, `count-algebra-v1`); several runs hit the existing
10-second wall guard before spending the full five-second counted allowance.
Their missing final branch trees are not proofs or invariant counterexamples.
A grow-returned count model is now recorded in `count-models-min-v1`, but asking
more instances there still does not close the hand set. New partition regression
and type checks were run in `proposal-tests-v1`: all 14 tests passed, and two
TypeScript diagnostics in the research replay result type were fixed.
`proposal-tests-v2` then passed both TypeScript and the expanded focused tests.
The Step 1 gate remains open.

The row-agreement proof is now complete: `row-rebase-diagnostic-v1` checks all
eight branches, the combined ground tree, and `checkMC`, at **3,739 ms counted**
and 25,198 ms wall. This explicitly labeled diagnostic kept the 5,000-ms counted
limit but allowed up to 60 s wall to isolate rebasing overhead; production
budgets were not changed. Disabling redundant unit discovery only for the
point-guided reconstruction was decisive. Branch-local instance sets keep the
SendConfig core small; all used instances are merged before the final check.
`saturated-cases-v1/rows.log` also checks the full row certificate at **3,716 ms
counted**, 17,740 ms wall, using ordinary linear proof branches for added action
bounds. Neither result is a full hand-set proof or a downstream gate pass.

A separate encoding audit found the research hand-set probe still used Ov_uw.
The design prefers the equivalent Ov_h with explicit half-cardinality premises.
The probe now exposes a reusable research builder with Ov_h by default and
retains Ov_uw under `LAB_OVERLAP_FORM=uw`. `canonical-capture-v1` contains the
fresh Ov_h fixtures. `canonical-replay-v2/rows.log` checks all eight row branches
and the combined `checkMC` certificate at **3,716 ms counted**, 17,517 ms wall.
The two count laws still fail: Inv2973 closes no complete action branch and
Inv* closes five of eight in that replay. Safety and protocol transitions are
unchanged. The two encodings were also compared with actual majority-quorum
intersections for all 1,024 pairs of subsets of a five-element universe; the
machine and every other hand law agree up to hygienic bound-variable names.

`canonical-coarse-v1` and `canonical-stutter-v1` isolate the remaining gap.
Inv*'s UpdateTerms branch checks at 229 ms counted, but BecomeLeader first asks
for an Inv2973 instance at a self-pair with numerical half witnesses. A fixed
focused certificate does not initially name those new count reads. The research
replay now has opt-in identity-preserving certificate growth (`LAB_GROW_CERT`),
which appends new reads/witnesses rather than renumbering ones used by earlier
branches. `count-progress-v1/grow.log` exercises it without completing the
leader branch; no Step 1 pass is claimed.

A separate opt-in frame-lemma experiment factors each candidate count-frame
inequality into an ordinary proof-tree split, retaining its checked pointwise
alternative. The initial full-context version timed out on every attempted
frame (`count-progress-v1/frame.log`). A narrowed field context checks the
UpdateTerms overlap branch at **1,072 ms counted** (`count-progress-v2/frame.log`);
folding its exact action first lowers that to **763 ms counted**, 8,210 ms wall
(`pinned-frames-v1/stutter.log`). Every folded proof is transported back to the
original goal/path before checking. Plain action folding also checks Inv*'s
first four action branches in 107–162 counted ms each (`pinned-cases-v1/all.log`).
Neither experiment yet checks a whole count law; full replays still run out of
budget. A single shared counted deadline now bounds implicit widening searches
as well as explicit queries.

The canonical encoding, arithmetic-witness filtering, stable certificate growth,
Boolean partitions, self-intersection view matching, frame proof, and proof-path
regressions pass the focused tests and TypeScript in `proposal-tests-v5`.
`frame-tests-v1` separately checks both Boolean partition directions and the
positive/negative frame-proof cases. New post-count subset proposals and pinned
model-query experiments remain under validation. These are untrusted proposals,
not new axioms or production budget changes. **Step 1 remains the gate; no
subsequent step is passed.**

### Step 1a: integrated non-count laws recovered (2026-11-08)

`integrated-row-v3/row.log` checks both the start and step obligations for
Inv1758 through `proveFocusedCounts` and `checkMC`, at **3,717 counted ms**.
The integration discrepancies were instance ordering and point-guidance scope:
small extracted cores need point reconstruction, but the full fallback needs
ordinary reconstruction. The same compact proof is not obtained by turning
point guidance on everywhere. `core/count-cases.ts` exposes this as an untrusted
strategy option, with scope-restoration and satisfiable-goal negative tests.

The real `GDP_COUNTS_GIVEN=1 GDP_COUNTS_FOCUS=1` search initially consumed the
row's share in broad MBQI before invoking recovery (`focused-hand-v3`). Moving
the opt-in non-count recovery ahead of that broad search fixes this integration
problem. `focused-hand-v4/given.log` retains all seven non-count laws:

| Law | counted attempt ms | result |
| --- | ---: | --- |
| Config kind | 5 | kept |
| one primary per term | 532 | kept |
| Inv866 | 181 | kept |
| Inv3915 | 2,352 | kept |
| Inv1758 | 3,713 | kept |
| p1 | 861 | kept |
| p2 | 67 | kept |

The overall result is still **not proven**, naming only Inv2973 and Inv*.
Those two attempts still exceed the desired per-goal bound and remain unknown.
`proposal-tests-v7` passes TypeScript and **27 tests / 2,154 assertions**. The
production strategy remains opt-in until the full hand-set and paired gates pass.

`count-model-audit-v4` records a concrete BecomeLeader model with the candidate
row aliased to the leader row, an abstract row size of one, and several distinct
known members. Two missing proposal shapes are now explicit: a three-term
post-remainder + carried-set / stored-row cover, and C3 lower bounds from the
model's distinct known members. The former is retained by the focused selector;
the latter is exercised by `model-count-picks.ts`, prioritizing pre-state rows
and retaining symbolic member witnesses. Its test checks both a valid distinct-
member proof and rejection when the members alias. `model-picks-v1/v2` and
`field-bounds-v1/picks.log` do not yet close the branch.

A separate research-only field-ceiling cut experiment derives candidate bounds
from a strict-successor per-member guard and an ordered count predicate. Its
cuts are never trusted: every accepted cut must have an ordinary reconstructed
proof and the final tree must check against the original goal. The first two
experiments do not prove the cuts within their query windows; further narrowing
is in progress. No complete count-law proof is claimed.

Fable's now-completed Section 1.5 confirms both hand sets on the bounded checks
and P* against TLC. None of its stated design falsifiers fired, so the prescribed
fallback is not indicated. **Step 1 remains the gate.** Step 0 is committed as
`938ee238`; no Step 1 completion commit or downstream gate claim has been made.

### Step 1a checkpoint and Step 1b proposal audit (2026-11-08)

`step1a-checkpoint-v1` repeats the real given-hand-set run and retains the same
seven non-count laws, including Inv1758 at **3,713 counted ms**. Both count laws
remain unknown (16,943 and 18,477 counted attempt ms); the complete hand set is
not proven and does not satisfy the five-second target. This checkpoints the
passed **sub-step 1a**, not Step 1 or any downstream gate.

Validation: `step1a-checkpoint-v1/check.log` passes `bun run check` with zero
warnings/errors; `tests.log` passes **31 tests / 2,171 assertions**. The exact
vendor gitlinks were staged from the initialized main worktree using
`--data /Users/monotykamary/VCS/working-remote/open-source/gdp-wired/vendor:vendor`.
The initial fresh-VM check lacked these uninitialized submodule contents
(`proposal-tests-v8`); a remote Git fetch timed out (`check-v1`). With the pinned
sources staged, `check-v2` exposed two unnecessary quote escapes in the research
member picker; those are fixed, and `check-v3` plus the checkpoint check pass.
No type-check exclusions or production budgets changed.

The subsequent count audit found a concrete selection bug:
`count-inventory-v1/inventory.log` contains **90 five-term candidates, zero
selected**. Earlier partition identities occupied all 16 algebraic slots. The
selector now reserves slots for union bounds and prioritizes their matching
partitions **within the same 16-slot cap**. Its regression is included in the
passing checkpoint tests.

Research-only cut factoring verifies six directed partition cuts in **23–34
counted ms each** and the required five-term union in **50 counted ms** under the
explicit active-leader guard (`symbolic-overlap-v7/active.log`). These cuts are
individually checked against their original goal and current path. The full
count obligation still times out. The Ov_uw symbolic-witness probes remain
separate from the default Ov_h hand set; active-only probes are explicitly
labeled and are not accepted as unrestricted proofs. The incomplete probes
remain outside the Step 1a implementation checkpoint.

### Step 1b research checkpoint — bounded pool and checked proof transport

The second bounded-selection issue is now fixed: per-positive-pair primitive
covers are interleaved with relational union covers, so a preceding irrelevant
pair cannot starve the carried set's three-term self-row cover. The existing
pool cap is unchanged. `modelSequence` also accepts an immutable copied path;
tests verify that subsequent caller mutation and empty-path queries cannot
inherit the path's assumptions. These are untrusted proposal/query changes,
not changes to the trusted kernel.

`count-regression-v4` passes **201 tests across 21 files** and `bun run check`
(type checking plus type-aware lint: zero warnings/errors, 945 files). The
pinned vendor gitlinks were staged exactly as for Step 1a. The narrower
`fold-path-v1` suite passes 27 tests; `path-guard-v5`'s test job timed out before
printing a test result, so that receipt is not counted as validation.

Research helpers now construct explicit linear recipes through count-read
bindings, including their lower-coordinate domain guards. Missing bindings
and missing domain assumptions are rejected. A single checked inactive-frame
proof can be reused across all failed activation conditions. In
`shared-guard-v1`, the active leaf checks in **3,615 counted ms**, and the
complete *pinned* activation tree checks after 221 ms of shared inactive work;
its transport to the original unpinned phase still fails at the 5,000 ms cap.
This is not an unrestricted law proof.

The direct original-path experiment avoids that transport. It exposed a real
slice omission: the active assumption `S subset X` was lost together with a
count comparison inside an operation-guarded conjunction. Path-aware
conjunct extraction restores it; the two carried-subset cuts (indices 35/36)
then check. The remaining five-term cut (index 12) reaches a native refutation
with **six hypotheses**, but does not reconstruct a checked tree in the
existing **250 ms local allowance**. `union-core-v1` reproduces this failure
for all eight raw/folded, ordinary/carried-first, unit-order variants. The
exact core and path are `runs/track-m/union-core.json`; the replay command is
in `research/track-m/jobs-union-core.json` (stage its containing directory as
`replay-input`). `jobs-fold-path.json` reproduces the direct full-phase probe.
No time budget was increased and no native refutation was accepted as proof.

**Step 1 remains open.** Neither count law is accepted as proved, the hand set
is not proven, and candidate-generation/3-by-60-second/merge gates have not
been attempted as passed. This checkpoint preserves validated generic fixes
and the exact reconstruction blocker, not completion of Step 1b.

### Step 1b continuation — checked Boolean cores and row-local count proofs

The six-hypothesis union core now has an ordinary checked proof. The untrusted
`boolean-core.ts` helper proposes bounded Boolean membership cases, uses linear
recipes or bounded ordinary search at their leaves, and checks the resulting
tree. It introduces no trusted rule. A standalone source-verified replay took
132 counted ms (`boolean-core-v3`). In the original, unpinned leader phase,
closing the phase path under the remaining constant upper bounds prevents
inactive later actions from leaving spurious offset reads. The five-term cut
then checks in 144 counted ms (`saturated-guard-v1`), although the complete
activation goal in that run remains unproved at its original 5,000 ms cap.

The remaining arithmetic models identify two additional needs: equal-row
cardinality reads must agree, and a post-state bad-quorum count on an unchanged
row is bounded by that row's old-membership count. The latter CInst was already
in the proposal pool; the research proof selector had skipped cross-declaration
post/pre pairs. The selector now considers it. Equal-key read cuts are proved
from the two actual read bindings, transported without fresh whole-goal search,
and checked against the original goal. Composite count terms, including natural
subtraction, are also transported through explicit bindings; missing bindings
and missing domain premises are still rejected by regression tests.

`startup-progress-v1/new-term.log` proves the hardest explicit leader-row case
(a > i, j = i) at **2,599 counted ms**, with 47 count instances. Both equal-key
read cuts check, the residual arithmetic core has 15 hypotheses, and its
transport checks all three count-read domain guards. This is a **diagnostic
row case**, not a whole-law proof: the output labels its extra assumptions and
sets the unrestricted `checked` result to false. The earlier unchanged-target
row case (`leader-rows-v1/frame.log`) checks at 1,883 counted ms. A generic,
checked row-case combiner has unit coverage; its integration, factoring common
cuts before all row cases, is still being tested on the full original phase.

Validation: `count-regression-v5/tests.log` passes **208 tests / 4,411
assertions across 23 files**, including the new Boolean, composite-transport,
row-case, and equal-key-read tests. Its isolated large VM placement is recorded
in `placement.json`. `progress-v1/check.log` passes the full TypeScript and
lint gate, zero warnings/errors (950 files), after `prepare-vendors.sh` restores
the pinned vendor revisions. `checkpoint-check-v1/check.log` repeats the full
check at the checkpoint source and also passes with zero warnings/errors.
The initial unprepared full check failed on absent
vendor trees and found one research helper's extra `withDeadline` argument;
that argument was corrected before the passing full check.

Several diagnostic runs hit their finite job deadlines before printing a proof
result; these are not counted as proof failures or successes. The runner's
command allowance is its job timeout minus 30 seconds: the first short runtime
isolation batch accidentally supplied too small a job timeout and was rejected
before executing its probes. The corrected `runtime-isolation-v2` passes the
basic and composite proxy probes, both Boolean tests, and the field-ceiling
probe. `runtime-diagnostic-v2` independently checks all relevant imports.
An asynchronous snapshot also lost a scratch file while indexing; subsequent
runs wait for the source-manifest receipt before further edits. The runner
replaces stderr on process timeout, so progress diagnostics now use stdout;
missing stderr markers alone do not identify a startup stall. The factored
proof diagnostic retains its 5,000 ms counted and 60,000 ms internal wall
limits; its outer runner allowance includes setup and result-collection time.

**Step 1 is still open.** No count law or complete given hand set is newly
accepted. The 3-by-60-second, candidate-generation, and downstream merge gates
remain unpassed. All new proof search remains untrusted and every accepted
recipe is checked by the existing kernel; no proof budget was increased.

### Step 1b: action guards, inactive-path reuse, and witness-key congruence (2026-11-08)

The machine-shaped guard proposal now selects the requested action and its
active carried set, rather than assuming the leader action or the first input
map. Per-member equalities also propose field ceilings; these remain ordinary
checked cuts. With both carried inputs considered, the existing capped pool
already retains the required Q2/request-row union: no pool-size increase or new
union family was necessary (`action-guard-v1/inventory.log`).

The first reconfiguration failure was an inactive-frame probe consuming its
leaf allowance before trying the actual false-guard path. The shared probe now
stops after two unsuccessful cuts, and a concrete inactive-path tree is reused
only after transport and a fresh kernel check. In `reconfig-v2`, all inactive
paths check; the remaining failure is in the active count proof. The natural
row-offset key and direct member key then exposed a missing key-congruence
proposal. Boolean-core search now proposes equal keys sharing the same witness
and checks both ordering branches. Its regression proves the natural-subtraction
alias only under the row-equality path and rejects the unrestricted goal.
Row-dependent post-count cuts are deferred to the structural row cases instead
of first trying them in a context where they are false.

`row-keys-v1/leader.log` checks the primary-equal and different/equal row classes
(reporting 1,233 and 1,217 counted ms), but not different/different; the full
original branch remains **unknown**. `row-keys-v1/reconfig.log` likewise remains
unknown at the active Q2 union core. These were non-timing diagnostic placements,
not timing-gate runs. The unchanged limits are 5,000 counted ms and 60,000 ms of
internal wall time. The earlier isolated timing request for the superseded
prototype remained queued; it was gracefully cancelled through its exact client
PID after the non-timing diagnostic falsified that prototype. The scheduler
confirmed removal of that request, without cancelling other workloads.

Validation at this checkpoint: `step1-key-check-v1/tests.log` passes **214 tests /
4,422 assertions across 24 files**; `check.log` passes TypeScript and type-aware
lint with zero warnings/errors (952 files). `row-keys-v1/tests.log` separately
passes all 18 directly affected tests. Section 1.5 was reread: its completed
bounded induction and encoding checks still support I-A/P*, with no stated
fallback triggered. **Step 1 and every downstream gate remain open.**

### Step 1b: checked source facts and witness-domain cuts (2026-11-08)

The residual Q2 union core now checks in isolation at **181 counted ms**, within
its unchanged 250-ms helper bound (`boolean-replay-v6/replay.log`, guided mode).
The score, membership-first, and key-first controls still fail. The decisive
proposals are checked cuts for the source's own forced facts and for arithmetic
row-update guards implied by the row equality and witness domain. These do not
consume the eight Boolean-candidate slots. Discovery still reads the original
syntax: pinning a nonlinear fact must not hide the membership conditions inside
it. Every opposite branch and the final source tree are checked by the kernel.

Portable captures now include the semantic expressions behind process-local
term columns. The first replay without these definitions failed with an unknown
term column; that invocation is not counted as a proof result. The corrected
replay re-registers the expressions and renames the captured path consistently.
The negative regressions continue to reject a missing subset premise and an
unjustified row equality. A frame's new Boolean helper is opt-in; enabling it on
the previously working inactive-frame probe was tested, failed, and reverted.

`row-frames-v3/reconfig.log` checks the Q2/request-row five-term cut in the actual
branch at 284 counted ms, including source transport. The full reconfiguration
branch remains unknown: the current certificate has no pair equating the copied
row's post-cardinality with the parameter set's cardinality. The existing
request-frame proposal option is the next item to exercise. The leader's first
two row classes still check; its final class reaches the unchanged 60-second
wall guard, so no complete branch or law is claimed.

Validation: `step1-domain-check-v1/tests.log` passes **219 tests / 4,433 assertions
across 24 files**, and `check.log` reports zero warnings/errors (953 files).
All probes retain the 5,000-ms counted goal cap, 250-ms Boolean helper cap, and
60,000-ms diagnostic wall guard. **The complete given hand set and downstream
gates remain unpassed.**

### Step 1b: request frames, numeric aliases, and capped partition selection

The copied-row cardinality now receives both checked comparisons with the
request-set cardinality. Membership syntax is normalized before selecting these
request-frame proposals. A structural post-count range bound is retained too.
The next numeric models identified disconnected original guard count cells,
missing request partitions, and an input-keyed row view rejected as non-stored.
The numeric slice now keeps only read bindings reached from its incoming path
(including natural-subtraction columns); source transport still checks their
read domains. A binding that substitutes to zero is reconstructed from opposite
source rows with positive weights. The initial zero-weight attempt failed the
checker and its new regression, and was replaced, not accepted.

The existing sixteen algebraic slots now deduplicate equivalent proposals and
rank pointwise Boolean partition identities ahead of unrelated triples. Request
partitions and exact pre-count aliases are retained without increasing the cap.
Carried-set comparisons also recognize their declared input-keyed row views.
Every resulting count cut and complete source tree remains kernel-checked.

Pre-rebase baseline: `request-frames-v6/reconfig.log` remains unknown at **5,028
counted ms / 31,645 wall ms**. `leader.log` remains unknown at **5,009 counted ms /
35,037 wall ms**; its equal-row class checks in 417 counted ms, but the next class
hits its 1,500-ms slice. Neither full branch nor the given hand set is proved.
These are diagnostic placements, not timing-gate runs. All original time limits
remain unchanged. Earlier request-frame iterations and the minimal proxy-path
fixture are retained as diagnostics.

`step1-request-check-v2/tests.log`: **226 tests / 4,452 assertions**, all passing
across 24 files. `check.log`: TypeScript and type-aware lint pass, zero warnings
or errors on 954 files. The request-frame batch separately passes 49 focused
tests. Section 1.5 was reread and no design falsifier has appeared.

Coordinator update: checkpoint this work, then rebase onto Track P **699b5160**,
keeping both lanes' changes. After the rebase, repeat static checks, focused tests
and this step-1 replay; future merge gates also require paxos_epr 3/3 and paired
IC3Syn 29×3 against **699b5160**, not main. Those post-rebase gates are pending.

### Track P integration checkpoint (2026-11-08)

The pre-rebase checkpoint was `a8d69064`; the replayed commit is `de9dbdd9`.
`claude/track-mldr` now descends from **699b5160**. Conflicts were resolved by
retaining both lanes: Track P's support/carry/relevance modules are byte-for-byte
unchanged from the base, its supported preflight/direct proofs and goal-local
helper contexts remain, and its deadline checks also bound Track M's additional
partition/union proposals and packed-key witness scans. Both lanes' test lists
and reports are retained.

`rebase-check-v1` passes TypeScript and type-aware lint (zero warnings/errors,
1,014 files), **226 Track M tests / 4,452 assertions** and **67 Track P tests /
1,071 assertions**. `rebase-request-v1` repeats the same branch proof status and
counted work as the pre-rebase baseline: reconfiguration **5,028 counted ms**,
leader **5,009 counted ms**, neither source goal proved. Their diagnostic wall
times were 25,755 and 29,323 ms; this wall reduction is not a closed proof gap.
The leader's equal-row class still checks in 417 counted ms and the next class
still exhausts its 1,502-ms slice. No step-one completion is claimed.

The original strict Paxos harness passes **3/3** on the merged tree
(`rebase-paxos-v1/paxos-r{1,2,3}.log`): all return `search.verdict = proven` and
`STRICT_EXIT=0`. Measured harness wall times are **26.690 s, 23.451 s, 29.947 s**;
all three jobs ran alone on their VMs with no co-tenants. These results protect
Track P's target on this tree. The paired IC3Syn 29×3 comparison against 699b5160
has not yet run and remains a merge gate, along with the unfinished MLDR gates.

### Step 1b: natural-subtraction cases and the shorter partition basis

Two clamping-threshold proposals now give an ordinary checked arithmetic tree
for the overlap contradiction. The new helper is research-only and opt-in, with
at most two splits and the unchanged 400-ms arithmetic recovery allowance.
The initial tiny fixture omitted the original guard expression, leaving its
path-only term columns uninterpreted; it was corrected to include that source
guard and explicit natural-number premises. The missing-union negative still
fails, as required. No term definition or arithmetic fact was trusted.

The full inventory exposed two redundant four-term identities taking the slots
needed by `cfgSize(a) = xm(a,i) + xn(a,i)`. Shorter three-term identities now take
precedence within the same sixteen algebraic slots. An adversarial regression
checks this against longer true identities and unrelated candidate noise.

`natural-cases-v3` checks all three logical reconfiguration row classes in one
ordering, then runs out of the goal allowance while covering the opposite
ordering. Its complete source goal is still not proved. Deferring duplicate
row-tree checks to the composing field proof preserves the final kernel check
and a negative regression rejects an unchecked deferred proposal. The v4 full
results remain unknown: reconfiguration 5,106 counted ms / 45,368 wall ms;
leader 5,000 counted ms / 39,489 wall ms. Earlier v2/v3 receipts independently
check the leader's equal and different/equal row classes. These are not timing
gate successes.

`active-rows-v1` is explicitly assumption-scoped. Its last reconfiguration row
checks at 1,963 counted ms; the leader's last row is still unknown. A portable
three-hypothesis Boolean frame core was captured for the latter; the next
hypothesis is a missing witness-related source premise in the reduced core.
A bulky Boolean dump exceeded the log tail in v2, so v3/v4 disable only that dump
and retain complete bounded verdicts.

`natural-checks-v1`: **229 Track M tests / 4,464 assertions** and **67 Track P
tests / 1,071 assertions** pass. TypeScript and type-aware lint report zero
warnings/errors across 1,016 files. Step 1 and the paired 29×3 gate remain open.

### Step 1b: actor-diagonal ceilings and a checked leader-action branch

The small failed leader core omitted the active witness's can-vote premise.
Restoring only existing source hypotheses for that witness is sound, but was
not sufficient: its next model identified the witness with the actor and left
the actor's old configuration term above its current term. The certificate had
no actor/actor instance. `countLawSeeds` now optionally prioritizes request
self-tuples within the same 32-tuple cap. The corresponding count comparison
proves the actor's own ceiling, alongside the target-row ceiling. This option
is currently selected by the research replay, not enabled as production policy.

Field-domain cuts are proved from the source before conditional ceilings are
linearized. Direct bounded arithmetic proves these domains, and the eight
pre-state partition instances now check directly without a native query.
Row-dependent carried comparisons are deferred to row children; duplicate
conditional ceilings and pre-only arithmetic queries are avoided. Source
hypotheses are never fabricated. Deferred children/cuts remain proposals until
the complete guard tree passes the unchanged checker. Negative regressions
still reject missing subset/union premises and unchecked proposals.

The leader-action entry now checks, including all row orientations and inactive
guard cases. `deferred-arithmetic-v1` is an isolated, pinned-large run (placement
recorded, zero co-tenants): **3,626 counted ms / 80,200 wall ms**;
`branches[4] = true`, `guard-complete.checked = true`. The top-level `checked`
remains false because this `LAB_CASE=4` run intentionally omits all other action
entries. This is a checked encoded action branch, not an admitted Inv* law or a
full hand-set certificate, and its wall cost is still far above the desired
production cost.

The same isolated batch leaves reconfiguration open at **5,086 counted ms /
33,166 wall ms**: every row tree is proposed, but final source transport does
not complete in the allowance. `source-active-v1` tests removing the redundant
active premise and relying on the original goal/path: leader still checks,
but reconfiguration's first row then fails. That route remains diagnostic and
is not the default. Earlier large Boolean dumps exceeding the 400-KB worker
stdout cap were replaced by bounded premise-delta and tree-rejection traces.
No missing receipt or timeout is counted as a proof.

`diagonal-checks-v4` passes **236 Track M tests / 4,492 assertions**, **67 Track P
tests / 1,071 assertions**, and TypeScript/type-aware lint with zero
warnings/errors on 1,018 files. One earlier shared-VM Track P run timed out two
five-second carry tests; the unchanged command passed with an isolated CPU
reservation and in the subsequent complete v2/v3/v4 checks. No timeout or proof
budget was raised. Step 1, production generation, and the downstream gates
remain open; the next work is the remaining count proof and its source-context
cost.

### Step 1b: smaller instance contexts close both hard action entries

`LAB_THIN_FIELD_CONTEXT=1` omits initial non-count instances with additional
quantifier keys and their field bridges for a count target. It does **not**
remove any law from the hand set, add a premise, change the target, or prevent
ordinary model-guided instantiation from recovering an omitted instance. It
asks the prover to use less of the available precondition. The option is a
research proposal strategy, not yet a production default.

`thin-fields-v1` (isolated, pinned large, zero co-tenants) checks the encoded
leader entry in **2,827 counted ms / 77,262 wall ms** and the encoded
reconfiguration entry in **4,152 counted ms / 81,685 wall ms**. Both complete
source guard trees check and the selected `branches` entry is true. No whole
Inv* or hand-set certificate is claimed: each run selects one action, the
symbolic overlap instance is still supplied by the diagnostic harness, and
wall-time source checking remains too expensive.

`remaining-cases-v1` surveys the other entries with the same context and fixed
five-second allowance. Entries 2, 3, and the final unchanged-action remainder
check (1,276 / 1,851 / 316 counted ms). Setup entries 0 and 1 and the send entry
6 remain open at the allowance. Together with `thin-fields-v1`, five of eight
entries have checked encoded trees; these are separate replays, not a combined
certificate. The setup countermodel keeps both the target config term and the
actor term at zero, suggesting that the singleton empty-post-count witness
already in the certificate must be used; the current field helper filters
those singleton witnesses out.

`one-row-v1` shows that dropping the secondary-key split alone does not prove
reconfiguration. `field-frames-v1` and `folded-frames-v1` add checked-proposal
attempts for an unchanged target field, but still fail to close that broader
row branch. Those options remain diagnostic and disabled by default. Three
regressions test frame candidate selection, the valid equality case without
fixing the target key, and rejection when the supporting equality is absent.

`thin-fields-checks-v1`: **239 Track M tests plus 67 Track P tests pass**;
TypeScript/type-aware lint reports zero warnings/errors on 1,020 files. The
latest Section 1.5 confirms no design falsifier: P* and the bounded induction
checks still support I-A. Step 1 remains the gate; no later candidate family
or downstream merge gate is claimed complete.

### Step 1b: setup emptiness recovered; send copy remains open

The setup models had zero target configuration term but a positive post-state
count. The ordinary certificate already contained the required singleton
`+postCount <= 0` CInst; the field helper excluded one-term proposals.
`LAB_EMPTY_COUNTS=1` now attempts these for post-count definitions with field
comparisons. `empty-counts-v1` checks setup entries **0 and 1** in **627 / 711
counted ms**, respectively (31,584 / 35,248 wall ms). A source-level counted
regression checks the zero-threshold proof and rejects the same conclusion
without that premise. Seven of eight action entries now have checked encoded
trees in individual replays, with their recorded options; no combined Inv*
certificate is claimed.

The remaining send entry exposed three concrete proposal gaps. Its activation
contains a disjunction, so the conjunction-only guard splitter returned before
trying it. Boolean guard coverage now follows both branches and checks the
complete source tree. The row selector then chose the copied **source**, not
the destination: live Boolean-valued writes must ignore dead arms and must not
mistake membership-read keys for write-index comparisons. Finally the selected
certificate lacked `post bq[a,j]` against `pre bq[i,j]` / `pre bq[i,i]`, and
`post cfgSize[a]` against `pre cfgSize[i]`. `focusCountCert` has an opt-in,
16-cross-pair-capped same-definition copy family, with both directions as
ordinary CInsts. The equal-primary row can also split its secondary key.
These options and their default-preservation/negative tests are checked, but
are not yet a production policy.

`active-writer-v2` confirms destination selection, and `copy-frames-v1` reaches
the correct equal/equal row but cannot reconstruct the copy count comparison.
`copy-model-v1/v2` captures its precise remaining failure: the model can set the
post indicator to 1 and pre indicator to 0 while source/destination keys are
fixed. The key-order candidates, source scalar-domain recovery, and direct
copy-point retries do not yet close it. The opaque column definitions identify
the unexposed numeric/Boolean indicator conditions as the next diagnostic
surface; these are not protocol counterexamples or accepted proofs.

`copy-checkpoint-v1` passes **253 Track M tests + 67 Track P tests**, and
TypeScript/type-aware lint reports zero warnings/errors on 1,020 files.
Independent rechecks still accept leader and reconfiguration in **2,827 /
4,152 counted ms** (85,037 / 83,458 wall ms). The long wall times remain a
problem, not a passing end-to-end timing gate. No budget, trusted-kernel rule,
safety law, or invariant was weakened.

Coordinator baseline update: remaining gates compare with **main 8610af26**.
The worktree already includes 699b5160; `git diff 699b5160 8610af26 -- core kernel
scripts` is empty. The later main commit changes reports/research packaging,
not the Track P code already present here. Step 1 and all downstream gates
remain open.

### Step 1c: checked copy indicators; source-instance size is decisive

The copy point prover now enters conditional operands even when their enclosing
comparison is forced, while still pruning inactive condition arms. Arithmetic
read-key closure emits an ordinary refutation for the opposite of each proposed
key fact; nothing is assumed by the checker. After key closure, only the unused
slots in the existing eight-choice pool are refreshed. The copy selector keeps
unchanged coordinates and shares its existing 16-pair cap across result counts,
so the larger quorum family cannot starve configuration-size copies. New tests
cover both directions, packed offsets, missing version guards, and unfair pools.

`copy-frame-points-v1` and `copy-deferred-transport-v1` construct all send row
cases but reach the external 90-second command cutoff during source checking.
The latter removes redundant intermediate transport checks only for callers
that check the complete original-goal tree. Default transport checking remains
on; a regression explicitly shows that a deferred invalid proposal is rejected
by the ordinary checker. Search and wall limits were not increased.

`copy-tree-metrics-v1` quantifies the remaining cost: **4,435 nodes / 2,218
leaves**, with **466 source hypotheses**, before the final source check. It
still times out, so this is a proposed tree, not an accepted proof. An attempted
reduction to only conditional-guard cuts passed unit tests but failed the real
equal/equal copy row (`copy-relevant-pins-v1`); that change was reverted.

A diagnostic keeps only the 17 count instances used by the previous proposal,
before witness flags and the encoded goal are built. `copy-thin-instances-v1`
then checks **the complete send action entry**, including all 18 row leaves and
both activation alternatives: `branches[6] = true`, `guard-complete.checked =
true`, **2,664 counted ms / 51,578 wall ms**. Its source goal has **140
hypotheses**; the tree has 4,359 nodes / 2,180 leaves. This is not an admitted
Inv* law or a whole hand-set certificate: every other action entry is omitted
in that run. The numeric keep-list is diagnostic, not a production policy. A
structural copy-key starting subset now replaces that numeric diagnostic:
`copy-compact-v2` checks the send entry with **22 instances / 172 hypotheses**,
**3,552 counted ms / 58,805 wall ms**. Sources are inferred from same-map value
branches, excluding inputs seen only in guards. It retains pre-state partition
instances, post-empty candidates, same-key frames, and coordinate substitutions
by one source input. It is an opt-in starting subset, not a replacement for the
full fallback pool or a claim about every kind of action.

`copy-checkpoint-v2` passed **270 Track M tests + 67 Track P tests**, but its
leader repeated a whole-tree check and hit the wall cutoff. The replay now
keeps unchecked proposals distinct from acceptance and delegates to one final
source/MC check. `copy-verification-v1` checks leader, reconfiguration and the
numeric-subset send entries at **2,827 / 4,152 / 2,664 counted ms**, respectively;
wall times are **36,292 / 41,688 / 41,480 ms**. The full, unthinned send still
hits its 90-second external cutoff; that failed job is not counted as a proof.

Final source validation (`copy-final-checks-v2`, tree `676f0c11613b`): **274 Track
M tests + 67 Track P tests pass**, and `bun run check` reports **zero warnings /
errors on 1,022 files**. The structural send receipt is `copy-compact-v2`
(tree `1db03186879e`). Reproducible job manifests are
`research/track-m/jobs-copy-checks.json`, `jobs-copy-verification.json`, and
`jobs-copy-compact.json`; replay data is the unchanged
`runs/track-m/canonical-capture-v1/fixtures` snapshot.

All eight action entries have now checked in individual replays with their
recorded options. They have **not** been assembled into a complete Inv* proof,
the full nine-law given set has **not** passed, and no production 3-by-60-second
or downstream merge gate is claimed. No trusted-kernel rule, original invariant,
safety law, or proof budget was changed.

#### Combined-action check after the copy checkpoint

Checkpoint commit: `ba821e48`. `all-actions-v1` removes the isolated action
selector and enables the already checked empty-count proposals, but retains
one **5,000-ms counted goal allowance**, the **60,000-ms diagnostic wall guard**,
and the unchanged external command limit. It is **not complete**: three early
source trees are proposed, later active cases remain open, and checking the
available partial branches reaches the external **90-second cutoff** before a
final result is printed. No proposed tree from that run is counted as a newly
accepted branch. The source context still has 466 hypotheses. Reproduction:
`research/track-m/jobs-all-actions.json`, receipt/tree `5e2838a0aa6e`.

This is the remaining evidenced wall: action-specific checked proofs and the
compact copy selection have not been integrated into a complete, sufficiently
small counted induction query. The existing production focused-count recovery
(`core/count-focus-proof.ts` / `core/count-cases.ts`) still needs that integration
and a checked whole-law result; summing isolated successes is not a proof.
Step 1's all-laws-kept and per-goal timing gates remain unpassed, so no later
family-generation or downstream merge gate was attempted.

### Wall-time profile requested by the coordinator

The integration work is paused until action wall time is small. Research-only
wrappers measure exclusive wall time (subtracting nested measured phases), with
CDCL's existing native unfold timer and a preload timestamp that includes module
loading. They do not replace the checker, change arguments, or change budgets.
`wall-profile-v1` uses the exact `copy-verification-v1` leader settings on an
isolated large VM. Profiled/control runs both check action 4, consume **2,827
counted ms**, and produce the identical final tree: **1,485 nodes, 743 leaves,
depth 59**. Their replay walls are 43,203 / 41,829 ms, respectively. The profile's
end-to-end time including loading/output is **43,325 ms** (timing tree
`c694f86f1242`; placement saved with the run).

| Exclusive phase | Wall ms |
| --- | ---: |
| Fixture reading | 0.528 |
| Instance/certificate generation | 56.225 |
| Goal construction | 12.028 |
| CDCL/model/core search | 1,884.107 |
| Native CDCL DAG unfolding | 0.000 |
| Direct arithmetic search | 133.779 |
| Prover row construction outside the above calls | 702.021 |
| Boolean/tree reconstruction and proposal control | 866.346 |
| Transport/reindexing | 5,116.291 |
| Intermediate source checking | 11,656.450 |
| Final source-tree checking | 22,825.043 |
| Final checkMC | 0.000 (not called in an isolated, incomplete-law replay) |
| Profile bookkeeping | 7.229 |
| Loading/output/unattributed residual | 65.224 |

**Checking is 79.6% of wall time; checking plus transport is 91.4%.** The gap
between counted time and wall is not expensive fixture construction or native
CDCL DAG unfolding. The final checker reconstructs rows for all 743 leaves.
An isolated action is still not a complete MC certificate: its final acceptance
is the original-goal `check(goal, tree, branchRoot)`; the profile does not pretend
that `checkMC` ran.

Tree sizes at phase boundaries (totals are work processed, not distinct nodes):

| Phase | Tree calls | Total nodes / leaves processed | Largest tree nodes / leaves / depth |
| --- | ---: | ---: | ---: |
| Search-returned trees | 51 | 593 / 322 | 95 / 48 / 14 |
| Boolean reconstruction | 12 | 596 / 304 | 127 / 64 / 20 |
| Row-case reconstruction | 1 | 803 / 402 | 803 / 402 / 30 |
| Guard composition | 1 | 1,481 / 741 | 1,481 / 741 / 57 |
| Transport | 155 | 4,059 / 2,107 | 1,149 / 575 / 50 |
| Intermediate checks | 122 | 1,484 / 803 | 191 / 96 / 20 |
| Final source check | 1 | 1,485 / 743 | 1,485 / 743 / 59 |

Leaf labels are structural provenance, not different trusted rules: a *count-row
leaf* is below the failing side of a CInst inequality or a split mentioning its
arbitrary row witness; other leaves are *arithmetic/control*. Both end in ordinary
linear refutations. The classification is exhaustive and the two columns sum to
the leaf count; it is not a count of a new trusted proof rule.

#### All eight action shapes (baseline, before wall optimizations)

`action-profiles-v1` (tree `892586f686fc`) runs all eight **individually** on
isolated large VMs with their previously checked settings. Every selected source
branch checks. All rows retain the five-second counted allowance and original
wall limits. Wall below includes module loading, fixture/build work, proof work,
and final source checking. No row invokes `checkMC`, because each is an isolated
action of an incomplete whole-law replay.

| Action | Counted ms | Wall ms | CInsts | Nodes | Leaves | Depth | Count-row leaves | Arithmetic/control leaves |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0: pick initial configuration | 627 | 24,405 | 69 | 515 | 258 | 37 | 172 | 86 |
| 1: copy during setup | 711 | 28,689 | 69 | 525 | 263 | 37 | 172 | 91 |
| 2: start | 1,276 | 33,381 | 69 | 715 | 358 | 39 | 273 | 85 |
| 3: update terms | 1,851 | 35,411 | 69 | 839 | 420 | 35 | 354 | 66 |
| 4: become leader | 2,827 | 47,163 | 53 | 1,485 | 743 | 59 | 597 | 146 |
| 5: reconfigure | 4,152 | 55,417 | 69 | 1,587 | 794 | 59 | 671 | 123 |
| 6: send configuration | 2,664 | 53,931 | 17 | 4,359 | 2,180 | 53 | 2,056 | 124 |
| Remaining/no-op inputs | 316 | 1,905 | 69 | 9 | 5 | 4 | 4 | 1 |

Action 6 uses the explicitly documented 17-instance diagnostic, matching the
4,359-node reference. It is not a generated production policy; the separately
checked structural subset has 22 instances. This table is not an assertion that
all actions fit one shared protocol deadline.

Checking dominates actions 0–5 (approximately 78–85% of wall). In action 6,
source checks take **32,046 ms**, transport **11,567 ms**, and explicit prover row
construction **5,508 ms**; these three account for **91.1%** of its wall. The
remaining/no-op case is already about two seconds. The next work is therefore
smaller/less-repeated checked reconstructions and source contexts, **not** an
integration into `count-focus-proof.ts` or any larger search budget.

The profiler's own bookkeeping is 2–21 ms per action; its source-check and
transport timings are disjoint. Run manifests: `research/track-m/jobs-wall-profile.json`
and `research/track-m/jobs-action-profiles.json`. Type/lint and all 57 focused
profiling/helper tests passed in the paired leader batch.
