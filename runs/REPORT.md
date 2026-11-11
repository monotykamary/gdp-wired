# LATEST — native admission speedup measured; I6 observation-gated

Admission-only source `3d0256f0` against `00b58ee5`: same-VM native ABBA
finite wall 238,301.09 -> 14,491.01 ms (16.44x) at identical 5,246,726.06 units;
compiled wall 374,287.09 -> 14,999.52 ms (24.95x) at identical 6,372,169.16 units.
Raw vectors and native results match exactly. No batching or price change;
these are measured workloads, not a final-source calibration. See
`research/lane-i/admission-perf/RESULT.md` and `results/native/`.

I6 source `1066f267` adds actual `tableCells`, `checkSteps`, `cubeTests` writers.
121 tests / 1,356 assertions and 1,791-file static pass; AST-erased checker
algorithms, other 132 identities and prover body exact. Census: 10 checked
proofs / 18 unknown; all 28 flags-off receipts exact and zero forbidden reads.
`simple_election` and `client_server_ae` change budgeted verdicts. Ten same-source
controls identify accounting-driven local/outer stops, not persistent proof
failure: both prove with writers on at a lifted cap; shadow/off old vectors and
normalized results match. See `i6/CAUSAL.md`.
`sharded_kv` reaches 15,120,328.2561, violating the previous 1,024 slack.
**Observation-gated, not accepted; no calibrated W or no-loss claim.**
B's exact B9 capture `cace38bc` is now available for native Inv*/K3 check replays.

Scoped A helper integration: `320092ba` imports the exact `620a3596` helper
and tests (D gate `12cfdab4`), not its missing generation-dispatch closure.
144 tests / 1,900 assertions pass; `f7edaefb` fixes inherited roster omissions
and passes roster/static (1,796 files). B/F RED payloads are not promoted.
See `research/lane-i/rolling-integration/STATUS.md` for scope and gate receipts.
Final D composition approval and calibration remain outstanding.

# Previous — combined counter/hard-cap candidate ready for D review

**Exact source00b58ee54b4e5b8c4967fdbde35d1ff0f38d91e7** on
claude/mldr-integ; D pin is **PLUMBING ONLY**, not calibrated/accepted.
raw-work-v1 adds six explicit positive-weight counters, native tiny work and
exclusive reach evaluation buckets, with pre-admission and inherited refusal.

All on supercomputer: **25tests/111assertions**, **1,783-file type/lint**,
**134 protected identities exact**.28strict+28flagsoff audited: **12 checked
proofs,16unknown**, no loss of10prior proofs; new client_server_ae and
simple_election. **Max15,000,385.9024 <=15M+1024**. Strict wall reads0;
old20-field flags-off projection exact and6newfieldszero. Entire raw schema
is intentionally additive, not a claim of unchanged JSON shape.

E1/E2 audited native statistics and drop/broken sets preserved; tiny nodes
and term/interval work are observed. **Prices remain provisional**: tiny
clock/wall~59–80, reach~.06–.09; per-evaluation admission has material overhead.
D must fit/bind weights and reconfirm the fitted-profile cap quantum.
Guest small9700X evidence sent to D; native+guest hardware qualification
still its gate. All owned batches terminal. No main merge/push.

Details: `research/lane-i/counter-fix/{RESULT,SCHEMA,D-HANDOFF}.md` and
`results/`. Original13 overrun cases/file:line/units-between-checks remain in
`research/lane-i/hard-cap/LOOPS.md`. Final report does not claim MLDR proved.

# ACTIVE — hard cap verified; counter correction required before calibration

Hard-cap runtime **efd70276**, evidence `research/lane-i/hard-cap/`: all 28
originals retain 10 checked proofs/18 unknowns; max 15,000,430 at 15M against
stated 1,024 slack. Pre-endpoint query/event prefixes and flags-off normalized
receipts exact. 22 tests/100 assertions; type/lint 1,776 files; 134 protected
identities. All owned batches terminal. Details: `hard-cap/RESULT.md`.

**D calibration HELD. Do not use efd70276 as its pin.** Added user task: count
tiny nodes, reweight reachability, measure E1/E2 units vs wall, integrate and
validate, then send one exact claude/mldr-integ pin to ic3-lean for both 174
calibration cases and 29 confirmations. A/D notified; next-work details in
`hard-cap/STATUS.md`. No counter source edits yet. Fable runnable fixture:
claude/fable-tiny f9923ed0.

# RESUME — COMPLETED 2026-11-11 common counted API

## LATEST — compatible API validated; new clock composition PENDING-D

On `claude/mldr-integ`, source **646811df** ports A's raw meter, counted clock,
profiles/ledger and work-budget surface onto **be661632** without restoring A's
prover. B's admitted exporter fixture dependency chain is supplied. Runtime
port: **4e13e5f9**; test/harness corrections: **9a5a80e4**, **d3294be2**,
**646811df**. Initial failed controls remain in the evidence archive.

Final native validation: **20 tests / 95 assertions passed**; full type/lint
**zero errors or warnings across 1,770 files**. Independent erasure checks
preserve the common prover body, CDCL/EPR logic and machine computation.
**131 other admitted/checker identities remain exact**, including all Lean,
`kernel/kernel.ts`, `core/check.ts`, and the original-model source blob.
Only admitted files changed: `kernel/prove.ts`, `kernel/cdcl.ts`, `kernel/epr.ts`.
Minimal new D review patch: `research/lane-i/common-counted/admitted-clock.patch`.
This is NOT covered by the older A-only clock receipt. No new D GREEN claimed.

At a requested **15M uncalibrated units**, all **28 other originals** retain
verdicts: **10 proved+checked, 18 unknown, zero lost proofs or refutations**.
All 28 were repeated with an independent pre-import Date/performance tripwire:
**zero forbidden reads**, identical verdicts and raw vectors. All **56**
receipt hashes, source/profile, weighted totals and root/exclusive ledgers pass.

**Important measured gap:** this preserved prover has cooperative polling,
not a hard dispatch cap. Thirteen cases exceed 15M by over 1%; maximum search
work is **38,611,286.018** (`lock_server`), rejected as unknown at `rule result`.
Do not present the API port as complete metering, calibrated W, bounded native
execution or a generation-termination fix. A/I need separately reviewed
polling/admission work; any checking/body changes must go through D.

Evidence and per-case units: `research/lane-i/common-counted/RESULT.md`,
`CENSUS.md`, `D-HANDOFF.md`, `identity.json`, and `results/`.
Native batches: validation `20261111-031018-ljjlzp`, census
`20261111-031200-idmdv6`, audit `20261111-031531-u61fuq`, commitlint
`20261111-031028-z333w0`. All are terminal. No owned job remains.
Candidate branch remains at its previous checkpoint; no unreviewed port was
silently promoted there. No main merge or push. `.reflex-saved/` untouched.

A still owns generation termination; F/B still own lifted transport routes.
The historical candidate MLDR measurements below are not new-source results.


## HISTORICAL — D-admitted trees integrated; counted composition blocked

Historical checkpoint retained for provenance. The latest common-counted
section above supersedes the integration branch status here.

D gates: reconciliation **72377361**, clock **565ecd01** (353713c9 on A's exact
5aa76818 parent only). Reconciliation is no longer PENDING-D.

- `claude/mldr-integ`: runtime checkpoint **be661632**; full common trees.
- `claude/mldr-candidate`: runtime checkpoint **7eccce26**, status commit
  **13055c89**; full common trees, no A kernel-file exceptions.
- `kernel/`: `db5bc38ac2e08e25d392d7a7daa748c7a6c8245a`.
- `lean-kernel/`: `b9039b851d59b7621e322a797096fcd724019f68`.
- Trusted checker: `6f6c9526003afcfc3ea1e48106ee44b4bf8649fd`.

**Actual current-tree validation is blocked**, not green: Boat batch
`20261111-024930-2cn0kn` verified 133 exact files with zero exceptions, then
candidate tripwire/typecheck failed on missing raw-meter and counted API
imports. Integration check failed on the B exporter research fixture chain.
`D-HANDOFF.md` records the boundary. No checking-path edit, restored A prover,
unreviewed full-strategy merge, push, or main merge was made to hide it.

Historical measured candidate **db14ee14** (three A kernel files retained):
- Smoke `20261111-024207-1m939c`: 86 focused tests, counted-clock tripwire and
  type/lint on 2,036 files PASS. Original consensus proved and checked.
- Paired census `20261111-024427-9vtkoe`: 57/57 native jobs exit 0. Including
  smoke, all 28 other originals pair up: **10 proven+checked on both A and
  candidate, 18 unknown on both, no proof regression, error or refutation**.
- Original MLDR UNKNOWN at 15M / 150M / 1.5B allowances. Search units:
  **4,424,579 / 38,174,787 / 375,674,773**. Sampling alone:
  **3,749,042 / 37,499,250 / 374,999,236**. Every run stops in generation before
  any proof query. A at 15M also unknown, 4,424,769 units. All UNCALIBRATED.
- These historical results are NOT evidence for the current exact-tree source.
- Receipt audits `20261111-024727-in1plr`, `20261111-024954-4lpa9o`: six negative
  controls and 60 hashed raw/exclusive-phase conserving receipts PASS.

Full per-model and per-obligation tables, raw compressed receipts and failed
native logs are under `research/lane-i/candidate/` (`RESULT.md`, `CENSUS.md`,
`MLDR.md`, `D-HANDOFF.md`, `results/`). Ranked next work: A/I counted API on the
common tree (D review); A sampling generation; F/B lifted-route registration;
B proof obligations; B/I full dependency integration and new-source census;
D/calibration owners for W. No unattempted leaf is called exhausted/proved.

All owned batches are terminal. Final batch `20261111-025225-grpnep` passed
the strengthened 60-receipt exact-source/profile audit, six negative controls,
and all nine commitlint messages. Native receipts and message hashes are
archived under `results/validation/`. Earlier F3/four native windows remain
separate unfinished work. `.reflex-saved/` is untouched.

## RESULT — counted-scope clock patch ready on A source (2026-11-11)

Checkpoint first, before implementation. Current integration HEAD is
`badc0242`, following `55c8ed96`; all previous owned batches are terminal.
B/F common-kernel overlays are with lane D for semantic audit: DO NOT merge
until D supplies the GATE receipt. `.reflex-saved/` remains untouched.

Read lane D's `../gdp-wired-verifyP/research/verify-all/f4-f5-cd671ac1/RESULT.md`
and lane A's `claude/mldr-gen` source at `5aa76818` before editing. D found
legacy clock reads at `kernel/prove.ts:222`, `:253`, `:263`, and direct timing
in `core/counts.ts:54`. Route those through A's counted admission scopes,
borrowed unreserved work and bounded dispatched generation so that
`GDP_WORK_FULL=1` search never reads Date.now/performance.now. Wall limits
must exist only outside the work scope. Add a counted-scope tripwire test
which throws on any such search-path wall read.

Trusted checking logic must stay byte-identical. If the fix needs a change
to checking rather than the clock, STOP that change and report it to D.
All tests/builds through supercomputer. Commit incremental verified work.
Working clock-only patch and tripwire assets are in `research/lane-i/clock-scope/`.
The active branch's checker differs from A (e557bc6c vs A's 5a5973de), so no
checker or A-source bulk copy is allowed. A disposable exact `5aa76818` archive
is the integration target; only core/trace-clock.ts, core/wall.ts and the
pre-grow() clock helpers in kernel/prove.ts change. A's counts ptime already
uses traceNow; its bound real clock was a hole, now replaced by unavailable
telemetry (zero) inside counted work. The tripwire preload also catches
functions captured before test imports. A's counted deadline semantics stay.

First boat batch `20261111-023011-tsckvj`: unpatched A baseline correctly
REJECTED (captured wall telemetry 26.91, not zero); both patched jobs stopped
before tests because a manifest named nonexistent `core/work-budget.test.ts`.
The explicit exists check caught it. No test success claimed. That path was
removed, source/patch receipts retained. Retry `20261111-023045-0hmxa6` then exposed a literal-newline serialization
error in the generated telemetry file, now fixed. Both failure receipts are
retained. `20261111-023122-3q6z3e` then PASSED all 26 full-work tests / 563 assertions,
but overall was not green: legacy had 36 pass / 1 fail, revealing telemetry in
an unscoped step-only search, and full typecheck lacked git-archived submodules.
Telemetry now suppresses wall reads in the step-only profile too; exact A
vendor submodules are archived at their gitlink pins. These are not checker
changes. Final `20261111-023225-a7qmv5` passed **37 legacy tests / 622 assertions**,
**26 full-work tests / 563 assertions**, and full type/lint on **1,730 files**.
Its exit 1 was solely commitlint requiring a Git root in the disposable archive;
that infrastructure prerequisite is corrected. The isolated commitlint retry
`20261111-023343-69iuf9` PASSED. No solver/type checks were duplicated for it.
All 131 other kernel/Lean files and the entire grow()-onward prover tail remain
byte-identical to A's pin. No checker changes, weights or W calibration.

**For lane A / D:** apply-ready source commit **`353713c9`** on
**`claude/lane-i-counted-clock`**, parent **`5aa76818`**. Only three clock modules
and two tripwire test files change. `core/counts.ts` already used traceNow in
A's source, so its sampling/generation ptime path is fixed transitively and
is directly exercised by the new tripwire. Preload catches captured clocks;
telemetry is deliberately unavailable (zero) inside work, not measured time.
The active integration checker (e557bc6c) is untouched; source branch checker
stays A's `5a5973de`. Do not bulk-merge A's differing checker into this branch.
B/F common-kernel semantic promotion still awaits D's GATE receipt.

All owned batches terminal; temporary Git worktree removed. Exact replay:
`research/lane-i/clock-scope/{prepare.sh,clock-only.patch,verify.ts}`. Preserved
receipts under `runs/lane-i/clock-scope*`. No mainline kernel merge claimed.



## For lane D — B/F kernel-adjacent semantic audit BEFORE merge

Pins: B `69b8ef2b`, F `cd671ac1`. Their trusted `kernel/kernel.ts` is identical
(blob `6f6c9526003afcfc3ea1e48106ee44b4bf8649fd`); integration currently has
an older kernel blob, so simply copying the five differing files is NOT a
complete source integration.

Two semantic differences need your audit:
- F's `kernel/cdcl.ts` uses each root row's canonical orientation, not the
  path map's key, which may be an `@` duplicate alias (`831d89dba`). B still
  has the old orientation test. Proposed common choice: F's fix and all
  three duplicate-root regression tests.
- B's `lean-kernel/emit.ts` registers columns mentioned only in `frame.when`:
  monomials, cells, and term columns. F lacks that registration. This affects
  emitted certificates, not just import order. Proposed common choice:
  retain B's registration, with both export suites.

Keep B's stronger frame-activation negative assertions; combine documentation
without the stale claim that TypeScript frames are not wired. A source-only
merge preview also found a non-kernel conflict: B's frame helper supports
`deferCheck`, F's supports `extraWhen` and zero-coefficient normalization.
Neither feature may be silently dropped in the full strategy merge.
No production merge has occurred. The common-kernel overlay PASSED on both
exact lane sources (`20261111-021552-pnmybx`): B passes the three frame-only
column regressions before patching, F fails all three, and both pass them
after patching, alongside selected kernel/export/helper tests and full
type/lint. Common kernel subtree: `db5bc38ac2e08e25d392d7a7daa748c7a6c8245a`;
common Lean subtree: `b9039b851d59b7621e322a797096fcd724019f68`.
Exact patches and replay driver: `research/lane-i/kernel-reconcile/`.
The semantic choices remain pending your audit, not silently merged.

## For lane A — original EPR preflight units (2026-11-11)

Frozen source `cd00524f`, original `consensus_epr`, unchanged inputs and
allowances. The full ledgers are now retained in
`runs/lane-i/epr-preflight-phases-routed/receipts/`; their raw vectors and
verdicts match both previously preserved runs exactly.

| Diagnostic allowance | `guards` | `small` (incomplete) | Other exclusive work | Total |
|---:|---:|---:|---:|---:|
| 15,000,000 | 158 | 12,782,486 | 2,217,518 | 15,000,162 |
| 50,000,000 | 158 | 47,782,526 | 2,217,518 | 50,000,202 |

The extra 35,000,040 observed units are entirely `small`, not EPR or solving.
`core/counts.ts:528` calls `core/exists.ts::smallOf(m,m0)` before the counted
attempt. The observation-only split (`20261111-021017-ieeuup`) identifies
**BFS**, not random walks: `small.bfs` costs **12,782,447 / 47,782,487**;
`small`'s remaining setup costs 39. The earlier fixed remainder is
**2,216,476** in `rule.refute-by-runs`, 25 in law construction, and 1,017
elsewhere in `rule.prove`. Request construction and sample initialization
cost zero under this vector. Their wall must still be tested by F3; zero
priced work is not evidence that these operations are free. The broken input
has the same failure class. No EPR, FM or plain-row work is reached.

**For the 25% endpoint:** the cap must enclose sampling, not merely candidate
emission. At the same diagnostic model, quarter endpoints are 3,750,000 and
12,500,000; sampling alone crosses both. These use eight explicit all-one
extra weights plus the fixed twelve legacy coefficients: they are NOT the
mini-calibrated W vector or a claim about 15,000 calibrated units. Once D
freezes weights, re-price the retained raw phase vectors without rerunning
sampling. In particular `small` contributes 12,781,007 evals + 1,440 ticks +
39 AST nodes at 15M, and 47,777,111 evals + 5,376 ticks + 39 AST nodes at 50M.
Independent boat audit PASSED (`20261111-020951-etjnxx`); the observation-only
subphase split also matches both preserved raw vectors and verdicts. The first
dispatch failed only on a wrong source-pack alias and is retained in
`runs/lane-i/epr-preflight-phases/`. No allowance was increased or input changed.

Weighted F3 controls now distinguish zero-price raw activity from advancing
units. A global seqlock starved under the zero-price control; that failure is
retained. Atomic monotone counter scans pass silent, zero-price and priced
controls, with complete profile archives independently replayed
(`20261111-021651-lipa30`). See `research/lane-i/work-meter/f3/UNIT-OBSERVER.md`.
This is Node capability, not original-model/reference-host full F3. Extended
`certFor`/`walkOnce` attribution finished (`20261111-021337-yl5wyh`):
49,327,232 spans, no overflow, exact raw/verdict/phase equality, two timestamp-valid
raw-silent windows, but **zero accepted native attributions**. The operation
span had ended before the profiler reply in both, so the native fence correctly
refused attribution. Three complete profiles (including the invalid 1,708,585-byte
profile) survived hash-bound transport and independent reselection. The original
four windows are not claimed resolved by a different capture. The extended
identity test exposed only a fixture typing error on `constructor`/`toString`;
its corrected retry PASSED (`20261111-022047-wua0xx`): 103 identity cases,
388 observed calls, equal original/wrapped-off/wrapped-on results and raw
counters, plus composed-source type/lint. The successful profile was not
rerun. Final lane tooling passed 25 tests / 48 assertions and type/lint on
1,741 files (`20261111-021756-6z3agm`). All owned batches are terminal; no
production kernel merge, mini repin, calibrated W or full F3 is claimed.


## For lane D — mini calibration / strategy intake (2026-11-11, active)

Your `reference-mini/run-mini.sh` CHILD already consumes the meter directly:
`core/work-ledger.ts::{withWorkLedger,WorkPhase}` and
`core/work-meter.ts::{rawWork,workKeys,withCompleteWorkWeights}`. Preserve the
full `events` array, especially `id`, `parentId`, `name`, `depth`, `completed`,
`exclusiveRaw`, `exclusiveWallMs`; do not substitute the aggregated F3
`phases` map. The 20 raw keys and 250 legacy work-units/ms convention match.
Ledger blob `ed88401af1577ac0fc4e5cbb270ec305274ee3e0` is identical in your
pinned `aeef6091` and my verified `32a59b2a`. Independent executable contract
checks are being prepared here, with no change to your one-shot mini policy.

**Important source gap:** `aeef6091` has no lane-B Section 20 production
strategy hook. Lane B's verified hook is `37d006af`, opt-in under
`GDP_COUNT_STRATEGIES=1`; lane F's live composition is still separate. Thus
174 cases at the current pin do not establish the price of that strategy path.
Do not transfer fitted strategy coverage across source SHAs. I am preparing
an isolated metered composition and strategy phase tests in parallel; do not
wait for a review, and do not change your frozen source or weights implicitly.
The kit also clears inherited `GDP_*` variables. Even after a pin change,
`GDP_COUNT_STRATEGIES=1` must therefore be an explicit recorded choice in
both calibration and confirmation if the opt-in hook is to run; otherwise
strategy phase coverage must fail closed rather than be assumed. My planned
phase names are `strategy.prepare`, `strategy.attempt`, `strategy.operations`,
`strategy.row`, `strategy.guard`, `strategy.compose`, `strategy.goal-build`,
`strategy.search`, and `strategy.check`/`strategy.final-check`. They share the
existing 20 raw dimensions; there are no phase-name coefficients.

**Exactly what to read:** each fit observation is
`{phase: e.name, raw: e.exclusiveRaw, wallMs: e.exclusiveWallMs}` from one
`WorkPhase` event. The `withCompleteWorkWeights` argument has **exactly eight**
keys: `tableCells`, `checkSteps`, `astNodes`, `evals`, `cubeTests`, `ticks`,
`cdclNodes`, `epr`. The twelve legacy coefficients remain fixed; do not pass
all twenty raw keys as a weight vector. `calibration/contract.ts` checks
counter dimensions, nesting and exclusive reconciliation directly.

The 174-case format run now completed on `aeef6091` in
`20261111-013419-oblh9u` (29 original/broken pairs, three repetitions), using
**explicit all-one diagnostic weights for those eight extras** and a 100,000
fixture allowance. This is format/partition preparation, not calibration,
not unweighted-path equivalence, and not original-protocol qualification.
Independent audit `20261111-013540-hq5zlp` passed: all three raw/phase
signatures match, and duplicate-case, mixed-weight, changed-signature and
wrong-source controls are rejected. **None of these cases had positive EPR
work**, so they do not close actual EPR-path coverage. The preceding
unweighted run did not complete; its three null-status child failures are
preserved in `runs/lane-i/mini-phase-contract-routed/`. Its old assertion
omitted signal/error/case identity; the new driver records those fields and
partial case receipts. No specific termination cause is asserted from that
old evidence. The rejected 20-key diagnostic-vector attempt is preserved too.

The metered composition is now frozen separately as **`cd00524f`** on
`claude/lane-i-strategy-meter`, tree
`6d1453342ca15df8bf948465c13cbf9a1aedf8a2`. Validation and all eight bounded
source-part builds passed in `20261111-014057-0li8e1`; transport reconstruction
reproduced the exact tested tree. Typecheck, five selected test files and
zero-warning lint passed (1,853 files including fixtures).
The row-strategy proof is checked, with 83 reconciled phase events,
166,615 table cells, 529 checker steps and 2,798 AST constructions;
fresh off/on raw counters and verdicts match. Direct ordinary and real EPR
sat/unsat fixtures also match off/on, with nine phase events and 38 EPR counter increments.
These are **direct fixtures, not original-protocol qualification**.

See `research/lane-i/work-meter/strategy/VERIFIED-SOURCE.md`. The complete
`WorkPhase[]` diagnostic data is in
`runs/lane-i/strategy-source-materialized/phase-data.json`, at
`results.find(r => r.on).events` and `paths.find(r => r.on).events`. Do not
fit from these Linux diagnostic wall times. The mini CHILD can read the same
source API directly; changing its pin/opt-in remains your explicit decision.
The shared composer is covered, but lane F's later prototype is not claimed
as part of this source. No active production source was changed.

Additional original-path evidence on `cd00524f` (`20261111-014806-1pinis`):
original **consensus proved and checked** in two repetitions, with identical
raw/results/phase summaries (212 FM units, 863 plain rows). The broken variant
remained non-proven. The `consensus_epr` runs instead exhausted the explicit
15M diagnostic allowance in preflight (14,845,783 evaluations, zero EPR work);
those failures are retained, not counted as EPR coverage. The separately labeled
50M follow-up also stopped in preflight (49,841,887 evaluations, zero EPR work),
with matching raw/results in both repetitions. No further allowance bump is
being used to manufacture coverage. None selects calibrated coefficients.

The first invocation-level F3 follow-up (`20261111-014727-41pz5e`, source
`32a59b2a`) preserved the original MLDR raw vector, verdict and phase totals.
Its three stable windows have valid timestamps, but the 10-million-span guard
saturated: zero operation attributions were accepted. The independent audit
preserves that limitation. The 100-million-span follow-up completed in
`20261111-015254-rydo8b`: all raw counters, verdict and exclusive phase totals
still match; 31,172,052 spans, **no overflow**, five timestamp-valid stable
windows and eleven changed windows. One stable ~304 ms window is attributed
to **`kernel/kernel.ts::canonFlip` → `flipMemo.set` (`WeakMap.set`)**. This is
an invocation boundary (including reflection/callbacks/possible GC), not an
exact native instruction. The other four stable windows remain unattributed
(two `certFor`, two tree-walker `go` frames). One invalid profile was excluded;
only its hash/size metadata was retained because its full payload exceeded
the diagnostic log limit. This limitation remains explicit.

Replayable audits are in `runs/lane-i/native-profile-100m/audit.log`,
`runs/lane-i/original-path-coverage/audit.log`, and
`runs/lane-i/original-epr-50m/audit.log`. Final tooling passed six controls,
22 assertions and full type/lint across 1,727 files (`20261111-015523-rjj9on`).
All owned batches are terminal. Full F3, remaining native attribution,
original EPR coverage and calibrated W are **not** claimed.

Fable's **35% strategy-pool share remains provisional**. No calibrated price
per strategy unit is being supplied. The new phase labels expose that work to
D's fit, but source/opt-in coverage, full F3 and the frozen mini vector are
still prerequisites for treating that share as priced.


## Verified raw source available; integration and full accounting still pending

Latest verified raw-meter source: **`94b65671`**, request-allocation observations
on parent `41d39043`. The CPU diagnostic below remains on **`41d39043`**,
canonical patch `f59720c766a6`; it does not qualify the changed source.
The original raw source below is retained as the first step of that chain.
Ordinary work-mode execution and actual EPR-path coverage are still missing;
no all-29 or calibrated-W qualification is claimed.

Frozen source: **`9a36137ece0525d077ecf4509b686b2e6bdf3058`**,
`claude/lane-i-complete-raw`, tree `2a21332d3fb0717cf0d4f0f3ba502ffd4d1f9a22`.
The source includes the retained isolated A2 entry and raw counters; it is
**not merged, not GATE GREEN, and not a completed W implementation**.
`research/lane-i/work-meter/complete/VERIFIED-SOURCE.md` binds its evidence.

Corrected tooling passed erasure/roster/decoder/type-lint in
`20261110-201440-608dz0`; 132 targeted and 3×267 mutation tests had passed
on the same production source. All first failures are retained below.

### For lane D

The immutable raw-source commit is ready for parallel instrumentation audit.
Checker erasure and zero/double/random acceptance suites passed. No calibrated
weights or W are supplied. Do not let this audit block ledger/coverage work.
The active integration branch remains research-only changes beyond the pause.

All three Bun raw pairs now agree on both Ryzen 9 9950X and EPYC 4585PX,
with independent audit `20261110-212826-0yywzw`. However, `consensus` refuses
with `work mode: plain-path migration pending` (51 AST
constructions, no solver work), and `consensus_epr` has zero EPR-counter units.
Do not treat either name as proof of path coverage or fit an ordinary-path
weight from the refusal. `mldr` exercises the counted path and stops at the
legacy work allowance. Details: `research/lane-i/work-meter/f4/README.md`.

### Ledger and boundary progress

The raw+ledger composition passes **151 selected tests**, checker erasure,
roster, decoder and type/lint (`20261110-201507-9tl8lf`), with independent
source/receipt audit `20261110-202057-8r5tcl`. Its source export was
hash-checked against that exact tested composition in `20261110-202257-o544wu`
and frozen as **`feeaccf26f945b8ec9ff19990ffe32e72023ec2c`** on
`claude/lane-i-complete-ledger` (parent `9a36137e`). Its six-file delta adds
the reconciled raw ledger and explicit, non-default extra-weight API; no
calibrated vector or W is selected.

The first boundary and bitmap compositions passed 151 and 155 selected tests,
respectively, but both failed typecheck at `kernel/prove.ts:1908`: the optional
`o.witness` narrowing was lost in the new synchronous phase callback. The
preceding branch rejects a missing witness; the repair is a type-only `!`
inside that callback. Both full rechecks passed (`20261110-202131-3i78uh`),
including 151 boundary and 155 bitmap tests, erasure, roster, decoder and
type/lint. First failures remain in `runs/lane-i/resume-composition-validation/`.
The independent repaired-receipt audit and both source re-exports passed in
`20261110-202451-eom7lj`; transport hash audits and the three full-composition
mutation controls passed in `20261110-202611-ljsgom`. Verified source commits:
`4550377f` (`claude/lane-i-complete-boundaries`) and `84ffacf2`
(`claude/lane-i-complete-bitmap`), in order after `feeaccf2`.
They remain separate source branches, not a final-gate-qualified integration.

The full active-worktree check exposed two old staged-only imports of
`kernel/meter.ts` in the research preloaders (that module intentionally is not
on the active branch). `1ca971d7` resolves these from the restored candidate
at runtime. The failed check is preserved in `runs/lane-i/resume-checkpoint-check/`;
that recheck passed typecheck but exposed one old unbound `ts.sys.readFile`
callback in the AST generator. `5b0453f5` binds the callback; the full final
check **passes with zero warnings/errors across 1,682 files** in
`20261110-202902-ciyd4v`. All nine existing source/research commit messages
also pass commitlint. The intermediate lint failure remains in
`runs/lane-i/resume-checkpoint-recheck/`.

### Raw-determinism pilot, not full F4

A six-job Bun pilot now uses frozen source `41d39043`: fresh-process pairs for
`consensus`, `consensus_epr` and `mldr`, on `default` and `large` VM classes.
Actual CPU labels and every raw counter are recorded; the fixed legacy
15,000,000 allowance is not a selected final W. The first dispatch was aborted
by an input-file upload race, with no census result rows. Its retry uses an
immutable 25-file runner and one reusable 147 MB input snapshot, not another
full worktree. Recipe: `research/lane-i/work-meter/f4/freeze.sh`.

Census tooling passes type/lint with zero warnings/errors across 1,687 files
and all prepared commit messages pass (`20261110-205639-plp2u8`). The initial
subprocess typing failure is retained. The initial tooling result alone did
not establish real CPU coverage; the subsequent audit is recorded below.

Recovered large-VM pairs pass source/transport/raw/phase/verdict audit
`20261110-211756-rm4lfj`. The pool contains Ryzen 9 9950X and EPYC 4585PX CPUs.
The diagnostic comparisons used an explicit different-CPU gate before any
solver run; a same-CPU allocation exited 75 without execution. All three IDs
now match across those CPUs (`20261110-212826-0yywzw`). Empty backend CPU labels
on the second placements are disclosed; their gate and both child records
agree. The three redundant, unstarted default jobs were cancelled after
retaining receipts; the original batch and its exact waiter are closed.
The ordinary refusal and unobserved EPR path keep all-29 qualification closed.

### Isolated ordinary-clock prototype — not admitted

The five-file prototype passed 22 tests and type/lint in
`20261110-212430-q24kdg`; its exact-parent, 109-blob patch roundtrip passed in
`20261110-212826-0yywzw`. It retains default refusal and requires explicit
positive test weights. Original `consensus` reaches 47,294 preflight
evaluations, then returns `unknown` / `work budget (completion)` with `fm = 0`.
This is not complete ordinary-solver or EPR coverage. No production vector,
W, source admission or integration promotion is implied.

### F3 progress, not completion

The heartbeat-fenced original-MLDR Node follow-up is now bound to canonical
patch `f59720c766a6`, with source blobs checked before and after observation.
Its tooling check passes (`20261110-211606-615p6t`, 1,689 files, zero warnings
or errors). The off/on run and strict audit passed in
`20261110-211555-pdxwgb`, preserving the raw vector, verdict and source blobs.
It found 11 changed-during-capture windows and three stable windows: one
application stack and two GC stacks. Rebuilding the same canonical bundle in
`20261110-213128-eh7sxk` maps the application frames to Cartesian request
construction in `core/infer.ts`, before `combosMax` truncation. That work was
unmetered in `41d39043`. This is not Bun F3 or complete-coverage qualification.

An isolated `requests` composition now adds only a discarded allocation
observation there. Six controls evaluate the actual production expression
and adjacent truncation, including overwrite semantics, map identity and RNG
order. All three zero/double/random acceptance controls pass 267 tests each,
with receipt audit `20261110-214151-wkgi21`. The selected run passed its 158
inherited tests but the new fixture failed to parse a TypeScript `!` inside
`new Function`. The transpiler repair passed all 164 selected tests, erasure,
roster and decoder, but lint rejected the `Function` constructor. The final
fixture loads an isolated compiled ESM module instead, retaining the lint rule.
The final selected-source retry passes all 164 tests, erasure, roster, decoder
and type/lint (`20261110-214513-kscywo`). Independent audit and exact-parent
export pass in `20261110-214802-hwwfgg`; source is frozen separately as
**`94b65671`** (`claude/lane-i-complete-requests`, parent `41d39043`). Only the
unused exact fixture differs from the audited mutation sources; every other
blob matches. No integration or production promotion is implied. The two
pre-dispatch input failures
(minimal census tools, then a cross-filesystem hard link) ran no solver and
are retained. The checkpoint tooling run `20261110-213410-0tn1qx` passed both
audits and commitlint, but lint rejected an untyped default sort in the plain
artifact auditor. The explicit string comparator passes type/lint and
commitlint in `20261110-213747-66qkkg` (1,695 files, zero warnings/errors).
That batch's artifact-only job failed because its recovery-input alias
pointed at commit messages; the correctly routed independent roundtrip passed
in `20261110-213829-djrxck`. First failures are retained, including a clipped
source-receipt prefix when export chunks were mixed with validation output.
The retry keeps source export separate from checks.

The source-pinned original-MLDR Node off/on diagnostic on `94b65671` passed
in `20261110-215020-uebure` (`runs/lane-i/resume-request-f3`): identical raw
vectors and `unknown: work budget (completion)` at the same legacy allowance.
The strict audit found two stable captures (GC and `canon2`) and four moving-
heartbeat captures. This is bounded Node evidence, not complete F3. Exact-source
mapping `20261110-215918-9x05eq` places `canon2` in `kernel/kernel.ts:canon`,
via `kernel/reader.ts:form` / `addCopy`; it does not identify an exact instruction
or native operation. Its tooling passed `20261110-215020-wempu0`.

A separate numeric probe reproduced finite-weight/finite-allowance overflow
on `94b65671`. The fail-closed fix is now verified and frozen as `32a59b2a`
on `claude/lane-i-finite-budgets`, changing only the work clock, five regression
tests and their shard registration. `20261110-215908-wplx8m` passes **169 tests**,
checker erasure, roster, decoder and type/lint, plus **267 tests per mutation
mode** on identical complete source. The same five regressions produce three
required failures and two passes on unchanged `94b65671` in
`20261110-220315-mmyn0j`. Independent source/receipt auditing and exact-parent
three-file export pass in `20261110-220408-fj9hms`; audit-tool type/lint and
commitlint pass in `20261110-220331-o8j51x` (1,698 files, zero warnings/errors).
See `research/lane-i/work-meter/numeric/VERIFIED-SOURCE.md`. The integration
production tree is unchanged; fresh F3/F4, wider floating-point proof, weights
and W remain unqualified.
Source-pinned Node follow-up `20261110-220701-qqbo9c` passes off/on equality
and raw/verdict/exclusive-phase equality with parent `94b65671`. Its strict
audit retains two stable captures (`canonFlip`, `canon2`) and seven moving
captures, so full F3 remains open. Tooling passes `20261110-220701-v35lw0`.
In parallel, the experimental five-file ordinary-clock prototype on exact
`32a59b2a` passed all 27 clock/budget controls and type/lint in
`20261110-220932-u5aqln`; exact five-file, 111-blob roundtrip auditing passes
`20261110-221145-sl6hyo`, and the stricter auditor passes type/lint. Its original
consensus case still has 47,294 preflight evaluations and `fm = 0`. No prototype
promotion or complete ordinary/EPR coverage is implied; F4 expansion remains
closed. A deeper original-consensus probe, `20261110-221416-q6185o`, does reach
solver entry at the first fixture allowance (500,000): 212 FM operations,
14 FM cells and 38 CDCL nodes, but zero EPR. It ends `unknown: work budget
(completion)`, keeps all 111 source blobs unchanged, and forbids wall-clock
and unseeded-random reads. No larger fixture allowance was attempted.

**For lane A (whole-entry work mode):** the unpromoted ordinary-clock prototype
is rebased onto `32a59b2a`; its five-file delta is `35344c91aa21`, with 27
clock/budget controls and exact-parent roundtrip checked. The original consensus
model reaches FM/CDCL at a 500,000 fixture allowance. This is not a production
budget change. Preserve the finite-cap/score rejection in the `32a59b2a` source
chain when integrating whole-entry clock changes.

**For lane D (meter admission):** `32a59b2a` is a separate verified source
branch, parent `94b65671`, not the integration production tree. It has 169
selected tests, three 267-test mutation runs on identical complete source, and
three genuine old-source negative controls. The latest Node original-model
raw/verdict/phase comparison at that point was equal, but two stable
canonicalization captures remained without timestamp filtering. The later
timestamp-bounded diagnostic is recorded below. No new
all-29 census, final W, Bun F3 or GATE GREEN claim is made.

Timestamp-bounded stack selection now passes eight adversarial fixtures and a
real before-release blocking-loop probe (`20261110-222458-ek322b`), plus
1,703-file type/lint and commitlint (`20261110-222458-r9py84`). A quiet interval
with no recent samples stays explicitly unattributed. The original-model timed
runs below use the recorded same-source off baseline; they are not an
overhead comparison or a complete F3 claim. Its source-pinned on-only driver
passes type/lint and commitlint in `20261110-222705-ud08x7` (1,704 files,
zero warnings/errors). The original timed result is now collected in
`runs/lane-i/resume-timed-f3`: raw vectors, verdict and exclusive-phase vectors
match, with source unchanged, but strict audit **fails on an invalid sample
delta**. It is not a qualified timed result. A single bounded diagnostic retry
in `runs/lane-i/resume-timed-diagnostic` retains the invalid sample's index and
delta plus at most two hash-bound raw profiles. Negative/non-finite deltas remain
rejected; no audit relaxation or timestamp normalization is used. Its unit and
blocking controls and parallel tooling results are recorded below. The first diagnostic
dispatch (`20261111-005922-mew7r5`) ran no solver: the default data destination
nested inputs under `data/`, while the commands expected top-level aliases.
Its three missing-file failures remain in `resume-timed-diagnostic`; the same
immutable inputs are resubmitted with explicit per-directory destinations as
`resume-timed-diagnostic-routed`. Independent archive tooling includes one
positive fixture and six rejection controls; no invalid timestamp is repaired.
The diagnostic observer's type/lint and commitlint pass in
`20261111-005947-ht6lpo` (1,710 files, zero warnings/errors). The explicitly
routed diagnostic, **`20261111-010216-e0ogvi`**, now passes all three jobs.
The original `mldr` Node run preserves the raw vector, verdict and exclusive
phase vectors on exact `32a59b2a`, with all selected timestamps valid. It retains
**three stable application windows** (`canon2`, `canonFlip`) and twelve changed
windows; no invalid-profile archive was emitted. The nine timestamp controls
and blocking-loop capability also pass (30 recent samples, before release).
The earlier invalid-delta failure is unreproduced, **not fixed or erased**.
Independent positive/negative log audit, exact-source stack mapping and final
tooling **pass** in **`20261111-011036-rhom40`**, all five jobs in
`runs/lane-i/resume-timed-evidence`; no solver was rerun there. The negative
control still rejects the original invalid-timestamp receipt. Type/lint reports
1,732 files, zero warnings/errors; commitlint passes. Source-bound call chains:
`kernel/kernel.ts:canon` via `kernel/reader.ts:form/addCopy/sync`, and `canonFlip`
via `dec/equal` and `dec/truth0`. Source blobs remain unchanged before/after
reconstruction. These function-level samples do not identify an exact native
operation. No owned batch is left running.

**Next:** distinguish native key enumeration/sort, memo lookup, serialization
and GC using bounded before/after attribution on the same frozen source;
retain strict invalid-timestamp rejection. Ordinary/EPR coverage, full F3,
weights and W remain unqualified.

**For lane D:** timestamp-bounded application captures remain on `32a59b2a`.
This is raw-progress Node evidence with a reused off baseline, not a paired
latency comparison, complete F3, Bun qualification, calibrated W or GATE GREEN.
The scheduler supplied no CPU label for this placement; no host or timing
qualification is claimed.

Original MLDR Node pilot `20261110-202238-v6auwd` retained **identical raw vectors
and verdicts** with observation off/on. Both were `unknown`, reason
`work budget (completion)`, at the same legacy `15,000,000` work allowance.
The run reported ~300ms quiet windows with sampled stacks through
`canon`/`canonFlip` -> `decide` -> `sameKey` -> `leafRows`. These are coverage
candidates, not a final F3 finding: the first observer did not recheck the
heartbeat after the profiler's asynchronous acknowledgement.

A discarded-increment-only canonicalization follow-up now counts lookup and
key serialization/inspection work. Its checks and a stricter heartbeat-before/after
Node pilot passed; see `research/lane-i/work-meter/coverage/STATUS.md`.
Independent audit `20261110-203450-h8vitu` confirms exact raw-vector/verdict
equality and nonnegative exclusive-phase reconciliation for every counter.
The canonicalization follow-up now passes 158 selected tests, erasure,
roster, decoder and type/lint; each zero/double/random control passes 267
acceptance tests. Its strict Node pilot preserves the exact raw vector and
verdict and reports zero stable windows, nine changed-during-capture windows.
Independent audits passed in `20261110-204538-t42ntt`; source is frozen as
**`41d39043`** on `claude/lane-i-complete-canonical`, parent `84ffacf2`.
No failed staging/control receipt was overwritten. This is not full F3/F4 or
a calibrated-W result.


`20261110-201744-s9kwtn`: Node v20.20.2's worker inspector captured 25 samples
including the named synchronous main-thread loop **before it returned**.
Bun 1.4.3 fails the stronger same-thread check. No ordinary-timer or wrong-thread
result is being promoted to F3. The Node solver attachment is exercised above;
the Bun same-thread capability remains blocked.


Lane I resumed from `dbfe4c56`; no cancelled run was repeated. **Not GATE GREEN.**

- Already-collected constructor artifact verified on boat in
  `20261110-201003-umjycw`, `resume-artifact-verify`, exit 0:
  29 chunks / 982,162 bytes / SHA-256
  `52571387a7f165ec76af1e34ea9fe06192abd43d555cd6aa78b2cef93c1734ba`,
  1,626 sites in 78 files. Every candidate blob matches the retained identity;
  original models remain `0541fa9436e307a6fb716aa5064637b30b893b79`.
- Original `/private/tmp` runner/frozen packs are absent both here and on the
  reachable Reflex home. Recovered exact Git roots and both submodules once
  into `~/.cache/gdp-archives/b11e1f65-a8bbe098` (hard-linked as ignored data in
  `research/lane-i/work-meter/recovery/`); no constructor regeneration, no new
  worktree, no source-tree copy. Total pack sizes: 133 MiB + 7.2 MiB + 235 KiB.
- First constructor validation is **running**, not passed. Task
  `c2b0e7fa-4b9a-4c25-9ff9-2fe876123cbf`, waiter PID `399849`, results
  `runs/lane-i/resume-complete-validation/`. Four parallel gate jobs:
  exact-count/erasure/inference/roster/type checks and zero/double/random
  acceptance-mutation checks. No local scheduler is running;
  `SUPERCOMPUTER_CONTROLLER=1` is explicit on every launch.
- First validation `20261110-201047-bdfcqp` is retained: raw exact-count /
  inference tests **132 pass**, erasure/roster/decoder pass; zero/double/random
  acceptance suites **267 pass each**. The plain job fails only
  `research/lane-i/generator/prepare.ts:4` (TS2307, relative recovery import in
  staged tooling). Fixed with a cwd-resolved dynamic import; source artifact
  unchanged. Type-only recheck task `7a4e3ae4-9930-4718-96d1-13529b087b02`.
  Compressed receipt hashes independently checked in `20261110-201404-7rf4tk`.
- Commitlint first failed because the runner had no configured rules
  (`20261110-201247-2e0vl7`). The pinned existing conventional configuration
  passes in `20261110-201357-iphs06`; neither first failure is discarded.
- Ledger/boundary/bitmap source composition is running independently at
  `runs/lane-i/resume-compose/`, task `f8c02604-563e-4901-8b37-7ccb7e70fb86`.
  Native bitmap scans are a confirmed uncounted operation in the retained
  artifact; draft exact visited-word ticks/tests are in
  `research/lane-i/work-meter/coverage/` and not promoted.
- Continue independently with coverage review and ledger composition. No
  calibrated extra weights or W, complete-source pass, F3 or 29-protocol
  determinism claim yet. Zero subagents, no pushes.

## Historical pause record (retained)


## Pause checkpoint — 2026-11-10

**Branch:** `claude/mldr-integ`.
**Committed source/evidence checkpoint:** `3169e4aa7fefbdf80dcec6ff08f37b254d396aec`.
This pause record is the following documentation commit; obtain its exact
checkpoint SHA with `git rev-parse HEAD`. **Start no work until explicitly resumed.**

### Stopped / collected

All owned background tasks have exited. The last waiter, PID `4214`, is
confirmed gone; the task inventory has no active owned task. Nothing from
this lane remains queued or running on boat. No cancellation was needed:
the final batch finished within the five-minute collection window.

Last collected batch: **`20261110-123659-26mbwo`**, job
`complete-ast-artifact`, task `97b9bf2d-e8d6-4401-a7e6-3d57de8c6861`,
job exit 0. Receipt is committed at
`runs/lane-i/complete-artifact/complete-ast-artifact.log`.

### What landed and what passed

- Research source/artifact checkpoints only. **No new production source,
  helper integration, old-weight change, private-cap change or W change landed.**
- The isolated pre-constructor ledger passed **39 selected tests**, roster,
  decoder and type/lint in `20261110-123003-1cvbpa`.
- Its independent source/receipt audit and commitlint passed in
  `20261110-123336-6maehh`. Original model blob remains
  `0541fa9436e307a6fb716aa5064637b30b893b79`.
- Constructor generation now passes its syntax/literal-preserving erasure
  audit for **1,626 allocation sites**. The complete source artifact was
  collected as **29 gzip/base64 chunks**, declaring 982,162 raw bytes and
  SHA-256 `52571387a7f165ec76af1e34ea9fe06192abd43d555cd6aa78b2cef93c1734ba`.
  This is a generation/audit result, **not** a complete-source test pass.

### Unvalidated / not done

The collected constructor patch has not been materialized or independently
hash-verified. Its exact-count, kernel-mutation, inference, roster/type and
coverage checks have not run. Bitmap/native-loop and cloned/reified AST
coverage still needs review. The separate table/instance/check
`ledger/boundaries.patch` is unvalidated. There is no F3 blocking-loop
sampler, calibrated extra-weight vector or W, quiet generator intake, or
29-protocol determinism census. Lane A's original full-suite failure is
preserved below; nothing here adjudicates it.

### Next item, only after explicit resume

1. Reuse the **already collected** compressed source artifact. Materialize it
   and verify its declared SHA on boat; do not regenerate completed work.
2. Freeze its source blobs and launch
   `research/lane-i/work-meter/validation/checks.jobs.json` (never launched).
3. Commit the verified raw-counter piece, combine the independently tested
   ledger, then apply/revalidate `ledger/boundaries.patch`.
4. Continue complete coverage and the original-model 29-protocol repeated
   cross-CPU census, one job per VM. Do not wait for Lane D's parallel audit,
   but do not invent calibrated weights or promote an unqualified gate.

### Rerun first

**None: no batch was cancelled.** The first future execution is the
not-yet-started artifact verification / combined-validation work above.
Do not rerun the successful ledger or constructor preparation merely to
recover context. Earlier failed setup/ASI/erasure attempts remain recorded
in the per-piece state histories and original run directories.

### Recovery files

- `research/lane-i/work-meter/{complete,ledger}/state.json` and `STATUS.md`.
- `research/lane-i/work-meter/validation/` contains unlaunched validation tools.
- Private indexes: `/private/tmp/lane-i-complete.index`,
  `/private/tmp/lane-i-ledger.index`,
  `/private/tmp/lane-i-ledger-boundaries.index`.
- Temporary source edits: `/tmp/lane-i-complete-*.ts`,
  `/tmp/lane-i-ledger-{prove,counts,shards}.ts`,
  `/tmp/lane-i-ledger-boundaries-{prove,counts}.ts`.
- Reuse existing frozen packs and runner; do not make another local tree copy.
  All execution/receipt analysis has stayed on boat; zero subagents used.

## Current directive — finish accounting and ledger without waiting on D1

Coordinator is auditing `c9eb0f9c` in parallel. Continue all remaining I2
accounting, then the phase ledger and all-29 repeat/cross-CPU determinism
census, one job per VM. Commit each verified piece; do not pause at the
kernel-audit boundary. No calibrated weights or W have been selected here.

## For lane A

Original failing source: `8901715e39a384583b22a5ea2856d93f795807fd`, gate base
`b11e1f65`, boat batch `20261110-105202-wd6w0o`, job `clock-shard-5`.

1. `core/cli.test.ts:480` — **flows, leases and effects: at most one call
   between, keys that expire, a charge made once** (test starts at line 453).
   The no-expiry acquire/release check returned `unknown`, expected `proven`.
   Call: `check([lockPath], {ms: 8000, propose: false, env: 'acquire then release'})`.
2. `core/cli.test.ts:1122` — **the CLI on supercomputer's shapes: aliases,
   shadowing, guarded products, floor division, integer sums, scoping, Houdini**
   (test starts at line 991). The reachable `Pending` integer-map sum returned
   `unknown`, expected `['proven']`.
   Call: `check([sPath], {ms: 8000, propose: false, from: 'reachable', entry: 'Pending'})`.

**Seed provenance:** neither original check call sets a seed, and the saved
job manifest supplies no seed or `FUZZ_SEED` override. A numeric run seed / the
inherited seed environment is **not recorded in the original receipt**; do
not invent one or label this a seeded protocol-census run. Preserve that gap
when handing it over. Manifest:
`../gdp-wired-trackK/runs/t20-clock-suite-jobs.json`.

**Exact retained log:**
`../gdp-wired-trackK/runs/t20-clock-suite/clock-shard-5.log`.
Its shard stream is 143,078 bytes, SHA-256
`525a80c716b5830715073925b49452b4a5dd56395bd8e14e8f0e8b2e2939503a`.
Receipt: `../gdp-wired-trackK/research/track-gen/t20-suite-first-result.json`.
Full-context command was `bun scripts/test-shards.ts --shard 5/8`; original
job timeout 900 s, 4 CPUs / 14,336 MiB. Do not replace it with an isolated retry
or increase either 8,000 ms search allowance.

Original result remains **273 passes / 2 failures** in that shard, with
1,632 passes across the first full-suite attempt. Later isolated controls
and full shard-5 context checks passed according to lane A's
`t20-validation-progress.json` (recheck `20261110-111313-7tv8x3`, audit
`20261110-111906-5w41pe`): 1,708 combined passes, **not a single clean original
suite run**. Those later receipts do not erase the failures or establish a
numeric seed for the original run.

## Historical checkpoints below

## Current priority — generator intake, then the revised counted finish line

User-approved `MLDR-29.md` → `FINISH LINE, REVISED` now requires 29/29
original-model proofs within one complete deterministic work budget W,
calibrated once by Lane D, plus one quiet wall confirmation. Lane I owns
complete pure-instrumentation accounting and repeated exact counts/verdicts
across at least three CPU models, **after a8 adjudication and Lane A intake**.
Section 18's definition was not yet present when inspected; do not invent
counter weights or treat the partial legacy meter as the complete counter.

Qualification-only candidate `ee6a78c3` lives on
`claude/lane-i-generator-e1614061`; the active branch remains `feca37b4`.
Eight production/test/roster paths integrate Lane A's committed finite pass
and loaded-row changes. The sole finite-pass conflict retains both the
new tick and the existing failure/revival tracking. Original models and
kernel source are unchanged; new tests are registered. Source checks are
running on boat under `7519f0ee-1d07-4dec-a31e-a98d62e12cfb`.

Quiet admission unit checks passed, but the first scout/calibration batch
found no eligible model floor. Alternate-size scouting is running under
`0d4fb142-6148-4c38-88f6-f6681e475aa5`. No noisy run is promoted or averaged.
See `research/lane-i/generator/README.md`. All receipt work stays on boat,
zero subagents, existing archives/packs reused, no new local tree copy.


## Latest priority — a8bbe098 RED entries ready for Lane D adjudication

Lane D's `final-a8bbe098-results.md` is RED: same-VM `two_phase_commit`
loss on EPYC 4585PX plus the accounts inference assertion and sums timeout.
User requires five strict protocol pairs on that CPU and five on another,
plus five same-VM pairs each for `infer.test.ts:47` and `sums.test.ts`.
Three or more candidate-only losses in a five-pair cohort trigger generic
repair; otherwise report all numbers under the coordinator's adjudication
rule. No budget, test or canonical-model change has been made.

- **All required cohorts completed with zero candidate-only losses.**
  `two_phase_commit`: 5/5 proven per source on EPYC 4585PX and 5/5 per
  source on the primary Ryzen 9 9950X. All seven retained protocol cohorts
  total 35 pairs / 70 proven processes. Accounts inference: 5/5 per side.
  Sums: 35/35 native cases per side across five full-file runs.
- Original 60-second protocol, 15-second inference and 5-second sums
  limits are unchanged. Actual EPYC coverage is verified; five Ryzen-only
  eligibility skips are not counted as protocol runs. Native inference
  phase traces, source hashes and all extra cohorts are retained.
- Independent receipt audit passed; final seven-file tooling overlay
  passes the 1,646-file type/lint check, zero warnings/errors and zero OOM
  delta, in `20261110-095250-95qs99`. Commitlint passed separately in
  `20261110-095211-rt8xfl`. Earlier tooling failures remain recorded.
- **Request Lane D adjudication**, not automatic promotion of the full
  gate: `research/lane-i/follow-up/lane-d-adjudication.md`. No speculative
  generic repair is justified by a zero-loss cohort.
- Lane A integration is queued in `research/lane-i/follow-up/lane-a-intake.json`:
  Section 17.7's generic Q2 row-load family and guarded Inv1758 family, as soon
  as the original-model generator change is gated. Preserve original model
  blob `0541fa9436e307a6fb716aa5064637b30b893b79`; all P* results stay research-only.

Verified earlier follow-up: p1 is 1152.3382236 on both sources in all five
pairs; a8's three canonical Paxos runs retain 6,915,544 / 1,037,946 work.
The old 97463c56 cost control itself returns unknown in its three whole-
Paxos runs; it is not the whole-Paxos work baseline. Effect passes 5/5 per
source on one EPYC 4585PX. This does not erase the RED gate or prove a flake
cause. Details: `research/lane-i/follow-up/results.md`.


## Completed measurement follow-up — a8bbe098 remains frozen

Boat batch `20261110-080834-7ilqre` is submitted under task
`8012abb4-b186-406c-816f-2cb2c9fa8448`: five new p1 pairs against Lane B's
validated `97463c56`, three whole-Paxos repetitions per source, and five
fresh-process pairs of the exact effect-pool CLI test on one exclusive VM.
Measurements, source verification, independent native replay/receipt
audits, type/lint and commitlint completed. No production source, gate
candidate or timeout was changed.

**Helper quarantine:** Lane B now identifies frozen family `5dbdbf...` as
P*, not the original IC3Syn encoding. Earlier conditional helper results
remain valid only for their recorded machines; they do not count toward
original-model Inv* or 29/29. The requested historical p1 cost comparison
uses that exact legacy family explicitly. At inspection, Lane B's canonical
models blob matches `8214a543`; Lane F and E still have the earlier routing
blob. None of their new helpers is enabled or merged. Original-model
recapture, original-goal INIT/STEP, unchanged allowance, census and paired
gates are required by `research/lane-i/follow-up/helper-integration.json`.
Details: `research/lane-i/follow-up/README.md`. No subagents are running;
local work stays limited to file/git coordination and one waiter per boat
batch. All new receipt parsing, collection logic, audits and checks run
on boat, with zero subagents and no new local whole-tree copies.

### Historical checkpoints below (not superseded by pending follow-ups)

Lane I resumed from `cca59f0c` on `claude/mldr-integ`; clean worktree verified, handoff including PAUSED, COMMON, and Section 14 read. **NOT GATE GREEN.** Historical baselines remain `b788e195` for the consensus diagnosis and `b09da82d` for the Paxos diagnosis; the coordinator now requires **`8214a543bc44e88d979f9e4457d7370e7e3c122b` for every next final gate**.

## Retained first preflight — 1fc444ca

Frozen candidate **`1fc444ca`**, baseline **`8214a543`**. The generic symbolic-binder repair is `bed9ecb3`: original symbolic terms survive alongside distinct arithmetic constants; existing proposal limits are unchanged. It fixes the replacement introduced by `1be4ffc1` and carries Lane D's symbolic/constant controls in `kernel/model-values.test.ts`.

Roster repair `985890c1` adds all 21 new omissions and inherited `core/extract-sol.test.ts`, plus a recursively enforced core/kernel filesystem check against the explicit quick and long suites. Canonical model repair `94be6cdb` chooses the revert option: `research/protocols/ic3syn/models.ts` is byte-identical to `8214a543`, undoing the canonical routing to Lane B / Track M's `0e2790f3` version-stamped P* setup. No finite-state equivalence or 29/29 proof is asserted.

Fourteen boat jobs ran under **`c3a54b95-73ff-4431-89d7-d8205fd9734f`**: exact-source type/lint with child-PID RSS/cgroup/kernel-OOM telemetry; all added tests; seven complete quick shards; unchanged Lane D symbolic controls; independent p1/timeout evidence re-audits; three fresh combined-candidate p1/Paxos confirmations; three alternating same-worker TIP `tip2015/relaxedprefix_correct.smt2` pairs; and commitlint. Original benchmark caps remain unchanged. Frozen manifest and receipts: `runs/lane-i/next-candidate/`.

**The first preflight is not accepted. Gate remains RED.** Twelve workers completed successfully; the staging helper has one TS2345 error (lint not reached), and shard 2 fails the unchanged effect-pool CLI case. The targeted run covered only 12 of 25 requested files because 13 paths were wrong; no all-added-tests claim is made. Repair `547badb3` corrects those paths, refuses nonexistent test inputs, fixes the type error, and adds unchanged same-worker effect comparisons against `8214a543`. Corrected qualification completed under `61bd3c87-e7a6-43da-8592-04d4186511f7`; the independent archive audit passed with zero integrity issues under `c4e99d55-ad36-4939-b25e-98feaa77f55e`, after its original launcher failed before admission on a relative jobs path. Detailed retained outcomes: `research/lane-i/regressions/next-candidate-results.md`. The current Lane D re-gate request below retains these failures.

## For Lane D — independent re-gate requested

Corrected `547badb3` targeted coverage passes **163 tests / 11,974 assertions across all 25 requested files**, including every omitted core/kernel test. TypeScript passed; its first lint run rejected only the qualification worker's unsafe `finally` control flow. That helper-only defect is corrected in frozen follow-up **`a8bbe098`**, whose full type/lint check passes. Neither run reproduced the historical SIGKILL, and no OOM was observed.

The unchanged effect CLI test passes on `8214a543` in all three isolated pairs, but on the candidate in two; the third reproduces its unknown results. Both sides pass the full six-test file. This candidate-only loss remains a blocker, not a flaky test to discard. Three controlled source traces plus the clean check completed under **`42ba776a-d33f-4210-a31d-fe52fb42476d`**. Only the diagnostic controls roll back the binder fix or disable shared rows; neither is a gate candidate. Original budgets and expectations are unchanged. Native receipts: `runs/lane-i/next-candidate-v2/`; full status: `research/lane-i/regressions/next-candidate-results.md`. **Lane D: please re-gate `a8bbe098` against `8214a543`. Gate remains RED pending that independent result.** Type/lint now passes with zero warnings/errors and no observed OOM. All 15 source traces completed; the historical `d3adf3c9` parent also produced unknowns in one trace, while the repaired candidate passed all three traced first calls. This does not erase the earlier candidate-only native test failure. Full request and retained caveats: `research/lane-i/regressions/lane-d-regate-request.md`. Final independent packet verification and all commit-message checks passed in `20261110-075757-rwfa48`; this verifies the evidence, not a green gate.

## For lane B — five exact-commit pairs confirm both cost requirements

Repair **`f7c5b4ba`** now passes five alternating exact-source pairs against `d3adf3c9` on one exclusive EPYC 9455. Every p1 attempt is independently native-replayed: **2046.9378360 → 1152.3382236 units**, equal to Lane B's original validated control. All **ten** whole-Paxos runs prove at exactly **6,915,544 solver / 1,037,946 full work**, with zero increase. Source, family, archive, cardinality, native-proof and cost audit: **zero issues**. No source patch or budget change was used for this confirmation. Raw proof packet and audit: `runs/lane-i/p1/confirmation/`.

The independent final evidence job (`610d77df-a291-411a-92f6-5f882f7806b2`, batch `20261110-065954-17ddio`) failed at type checking: four TS2532 indexed-access diagnostics in `timeout-pairs-audit.ts`; later checks were not reached. Its separate commitlint job passed. The indexed accesses are now corrected for the next qualification, without changing audit semantics; no replacement pass is claimed. The original full-suite timeouts remain retained; **this is not a clean full suite or a final-gate pass**, and Lane D's already-frozen gate is untouched.

## New-main timeout diagnostics — six pairs pass in isolation

The corrected paired reruns pass on both exact `8214a543` and `d3adf3c9` sources: **six pairs / 12 processes**, **66 test executions / 348 assertions**, zero source/trace/command/deadline audit issues. The unchanged search target takes **2.406–3.211 seconds**, under its 5-second limit. The unchanged Python-fold target takes **31.109–36.150 seconds**, under its 60-second limit. Each case has three alternating pairs on a single exclusive CPU model (search: EPYC 4585PX; fold: Ryzen 9 9950X). Test hashes match independently read git objects on both revisions. These failures **did not reproduce in isolation**; their full-suite timeout failures remain preserved and unattributed. This is not a clean full suite or final-gate pass. Evidence: `runs/lane-i/paxos/post-main/timeout-pairs-v2/audit.json`.

## For lane B — repair committed as `f7c5b4ba`; five-pair confirmation active

The targeted-qualified mixed-clause schedule is committed at **`f7c5b4bad58578d95684ca279e882f48fabd8525`**. Exact-commit confirmation is now task **`3e5a6fbc-4dd0-4900-8efb-800f7170d555`**, five alternating pairs of `d3adf3c9` / `f7c5b4ba` on one exclusive worker, with native p1 replay and strict 60-second whole-Paxos runs. It requires p1 cost 2046.9378360 → 1152.3382236 and identical 6,915,544 solver / 1,037,946 full whole-Paxos work. No repeat result is claimed before collection. Lane D's already-frozen gate is not replaced.

The first timeout-rerun submission failed before any tests: a replacement-string `$` expansion corrupted the generated filter. Both jobs contribute **zero test coverage**. The corrected script uses a literal replacement callback and fresh job identities, task **`2358e804-76ae-4b31-b063-9736970f7ac2`**; original test code and 5-second / 60-second deadlines remain unchanged. Both original full-suite failures are retained.

## For lane B — mixed-clause repair passes targeted qualification

The corrected policy takes early bounded completion only for a **single quantified key**, **unary count maps**, a **mixed ordinary-map/count clause**, and a **separate relevant count premise**. Aggregate-only, concrete, isolated and multi-key targets remain sparse-first. No proof rule, completion cap or deadline changed. Exact-source qualification restores `d3adf3c9` and passes **25 tests / 108 assertions**, clean TypeScript/lint, roster validation and commitlint. Native p1 replay is checked at **1152.3382236 units**; whole `paxos_epr` proves at exactly **6,915,544 solver / 1,037,946 full work**, equal to `d3adf3c9`. The qualified `core/counts.ts` SHA-256 is `7a4c830848afa2d05393bdd00c546393092cf1f94d5ce9cdee8a2aad9189abd4`.

This is targeted qualification on one exclusive Ryzen 9 9950X, not a final gate or clean full suite. A five-pair exact-commit cost confirmation follows; Lane D's frozen `8214a543` → `d3adf3c9` gate remains unchanged. Receipt: `runs/lane-i/p1/draft-v2/qualification.json`. The prior wrong-source draft and +530-work prototypes remain failed evidence, not passing coverage.

## New-main full suite collected — two unchanged test timeouts, not qualified

All seven `d3adf3c9` shards are collected and source/placement checked. Five exit zero; two fail, with **1,147 recorded passes, two failures, five skips and 577,791 assertions** before the failed shards stop. `core/search.test.ts`'s invariant-discovery test takes 8,385.09 ms against its unchanged 5,000-ms timeout. `core/extract-py.test.ts`'s request-list fold test takes 61,074.58 ms against its unchanged 60,000-ms timeout. This is **not a clean full suite** and neither failure is attributed yet. Exact summary: `runs/lane-i/paxos/post-main/suite/suite-audit.json`.

Three alternating pairs per case are admitted against **`8214a543` / `d3adf3c9`**, task `c6728778-f9a9-4c3b-8041-9ceb0419a1dc`. The search file is unchanged; the fold case uses an explicit name filter without editing its code or deadline. These isolated diagnostics cannot erase the original full-suite failures. The separate p1 mixed-field/count draft qualification remains active (`48d3771f-2b25-4743-afae-a123ba811f0b`); Lane D's existing gate is untouched.

## For lane B — residual work isolated; corrected draft qualification running

The paired per-law probe identifies the entire residual solver increase at the aggregate-only `members$Qs keeps members's bound 2` obligation: **20,007 → 21,411 solver work**, **27,916.6078 → 28,446.5038 full work**, explaining the whole-run +530 rounded full-work increase. Requiring another count premise alone does not remove it. Both three-repeat frozen-family probes preserve p1's exact original cost but fail the strict whole-Paxos neutrality criterion. The independent receipt audit passes with **zero issues**; six refusal tests execute in each of the two staged paths (**12 executions / 26 assertions**), explicitly rejecting the +530-work prototype.

The conservative draft check is retained as a **failure**, not qualification: its new test reused the count binder name, and a staging copy overwrote its restore config with historical `8de9dadb`, also reintroducing that old revision's unused import. The original post-main full-suite packet still correctly names `d3adf3c9` and is unaffected. The corrected draft now explicitly restores and verifies `d3adf3c9`, uses a fresh test binder, and prioritizes only mixed ordinary-map/count clauses; aggregate-only bounds stay sparse. New controller **`48d3771f-2b25-4743-afae-a123ba811f0b`** checks exact-source type/lint, all scope/refusal cases, old p1 cost, exact whole-Paxos work, and commitlint. No check result or repaired-candidate claim yet. Lane D's existing gate remains untouched.

## For lane B — p1 regression reproduced; first prototype rejected on whole work

The exact three-repeat boat comparison reproduces **1152.3382236 → 2046.9378360 p1 units** for validated control `97463c56` versus `d3adf3c9`; all nine p1 certificates independently replay. A disposable unary-priority policy recovers **1152.3382236** and preserves the frozen Paxos proof at **38,917 solver / 26,285.6192 full work**, with six successful frozen Paxos certificates independently replayed. But its whole-Paxos screening pair costs **530 extra full-work units** (1,037,946 → 1,038,476), so it is **not accepted** as the joint work-neutral fix. This completed on one exclusive EPYC 9455 worker; no timing claim. Raw receipts: `runs/lane-i/p1/probe/`.

Two follow-ups are admitted: a separate-count-premise scheduling experiment and receipt-auditor refusal tests (`3431abef-abdf-4e94-8afa-126c50780bdc`, batch `20261110-063516-cuuvdp`), and qualification of a conservative uncommitted draft that also requires an actual single quantified key, leaving concrete goals sparse (`bff38ac0-d682-4852-8bf7-572f364ef00c`, batch `20261110-063659-6z5xy4`). The latter checks type/lint, scope and false-INIT regressions, p1's exact old cost, and exact whole-Paxos baseline work. **Results remain pending; no new repair or final-gate pass is claimed. Lane D's frozen `8214a543` → `d3adf3c9` gate is untouched.** Details: `research/lane-i/regressions/p1-scheduling-notes.md`.

## For lane B — initial p1 scheduling admission (historical)

Lane B's exact before/repair count-source hashes match `97463c56` / `d3adf3c9`. The original p1 and 45-law Paxos families are frozen unchanged. A new exclusive boat job tests three rotated repetitions of the validated control, exact current repair and a **disposable** single-key/unary-count early-completion policy, with independent native certificate replay. It also screens whole `paxos_epr` on the current and experimental policies at the unchanged strict 60-second limit. Task `c54164de-9246-44c1-b493-60d3529dbabd`, batch `20261110-062712-4vl6nq`, snapshot `f980b21aa51a`; input manifest SHA-256 `d503b71edbe57c418e9bd60012884c44606b077a6946a9d32c87e713871c9627`. **No new measurement or production fix is claimed yet.** This is an arity-based hypothesis, not a guarantee of linear helper expansion. Details: `research/lane-i/regressions/p1-scheduling-notes.md`, `runs/lane-i/p1/`.

Lane D's `8214a543` → `d3adf3c9` final gate is untouched. The existing new-main full-suite controller remains active; it has reported a failed shard, but its raw receipts are not collected yet and no cause or clean-suite result is claimed.

## Current checkpoint — repair qualified; final re-gate requested

- **For lane B:** first failing Paxos merge is `1550512d` (eager count completion before sparse proof search). Generic repair `dd036dd7` retains bounded completion in the existing stuck-model recovery paths. The measured repair `8de9dadb` proves **10/10 strict Ryzen trials** at baseline-exact **1,037,946 full / 6,915,544 solver units**; the culprit loses 10/10. No repair losses; one noisy baseline trial is retained as unknown.
- **Merged candidate `d3adf3c9589ec014a158b6f42ecfb091c999bb43`** includes main's optional-choice P1 fix and the lint correction. Exact-source qualification passes **54 tests / 740 assertions**, TypeScript and lint, with zero audit issues.
- **Lane D (`t6p`) has been asked to re-gate `8214a543` → `d3adf3c9`.** No new-main paired gate result is claimed. Gate remains **RED / pending re-gate**.
- Historical consensus diagnostic: all **3/3 measured pairs prove**, with two explicit CPU skips, so the planned five-pair qualification remains incomplete. Historical suite: six of seven shards completed; **1,405 recorded passes, one default-timeout failure, 17 skips**. The failed shard stops early, so these are not full-suite coverage totals.
- Full `d3adf3c9` suite `969e8315-cd78-46a9-8397-e911c8cddf48` remains active. The unchanged `core/search.test.ts` passed **all three paired runs / six processes / 60 test executions** on `8214a543` and `d3adf3c9`, at the unchanged five-second timeout. The affected test took 2.16–3.75 seconds. No isolated reproduction; full-suite confirmation is still required.



- First cancelled work rerun **completed all 140 frozen upper-bound shards** at `15eff72f`, task `cf1d3fc9-6a88-4e12-8403-974717b1ed42`. Initial aggregation: **64 fresh-process-verified conditional STEP closures, 42 unknown, 34 censored**; no full helper/family/safety proof. Detailed source/budget/provenance audit and censoring breakdown are below. The newer integration was not substituted.
- Repair: core-replay reconstruction now spreads the previous obligation before replacing its goal/decls/encoded goal, retaining `all`, certificate and pool. Added a focused range-demand test for a read omitted by the selected certificate. No budget, law, or kernel change.
- Prior V11 production source candidate: `e48a109efc5ee029d658702ac45a7e7a8ff4c9b6`. The newer combined V12 production source, returned validation failure and qualified test-only repair are recorded below. V11 validation completed with **one failed check** (new runtime-key test used `Function`); its four test shards, original MLDR pairs and replay negative control returned zero process exits. The V11 generation census has returned: all 84 unrelated comparisons have identical canonical hashes, with the three expected MLDR expansions retained. The frozen upper-bound and test-only VM repair have returned and are qualified below. Lane D's `b09da82d` gate is **RED**, not pending or green; the exact-source paired diagnosis below is active.

## Prior bf011901 gate and diagnostic chronology (historical)

Lane D's exact **bf011901 vs 4497c4b0** final gate is terminal **RED / incomplete**. Its independent report is `/Users/monotykamary/VCS/working-remote/open-source/gdp-wired-verifyP/research/verify-all/final-bf011901-results.md`. Consensus is now 3/3 proved and faster. **Paxos EPR loses all three pairs:** baseline proven in 18–23 seconds and 1,135,224 full units; candidate completed-unknown in 55–59 seconds and 9.5–15.0M full units. These are not crash diagnoses. Strict totals are candidate 81/87 versus baseline 84/87. The inherited optional-choice source-law translation defect also blocks the gate; CI owns its fix and main must be merged once that lands.

New task: bisect every substantive production boundary after passing `b09da82d`, with same-CPU 5+ strict repeats and generation/finite/per-law full-work traces. Working hypothesis, not a finding: a recovery/completion ordering or candidate-family expansion after b09 spends the additional work; A/B and later E/F/Fable changes will be tested, not blamed by chronology. **No new final-gate request until the regression and CI blocker are fixed and independently requalified.** The Paxos packet pins **21 endpoints** (every substantive boundary plus passing/failing controls) to source-specific protected hashes and the unchanged 60-second strict budget. It targets one CPU model, **EPYC 9455**, independently of the still-running Ryzen historical census. Input/import/unit-test/all-source-restore qualification is active as task `d0034a06-f161-4690-863a-8b9038d6c05d`, output `runs/lane-i/paxos/bootstrap`; the preflight passed with 21 clean source restores, 85 checked file hashes, and 12 test executions / 38 assertions (six distinct tests, duplicated mount paths). It contributes zero measured pairs. Five-repeat endpoint cohorts are now active as task `df20e57f-d555-476b-b3a6-b9c1b8b6b6d7`, using the same frozen packet and EPYC 9455 CPU filter; wide interval submission remains held until endpoint trace transport is verified. Unknown outcomes retain their work and per-law deltas rather than being filtered out of summaries. **The endpoint now reproduces the loss in 5/5 audited EPYC 9455 pairs**: b09 median 21.771 seconds / 1,037,946 full units; bf 59.004 seconds / 11,464,485 full units. Generation improves by about three seconds; the paired post-generation increase is about 40 seconds. Finite pass is zero on both sides. The endpoint envelope is only 89,456 encoded bytes and retains all raw traces. Details: `runs/lane-i/paxos/probe/endpoint-summary.json` and `cohort-audit.json`.

Only one of sixteen endpoint slots matched EPYC 9455. The full 21-point census is therefore being qualified as a **separate fixed Ryzen 9 9950X dataset**, with three seven-point groups to bound trace size. The earlier historical wave demonstrated eight eligible Ryzen workers. No cross-CPU repeat counts or timing medians will be pooled. The fresh CPU-selection unit test and all-source preflight are active as `efbaec73-4b44-4629-aef1-193a9c12720c`, output `runs/lane-i/paxos/ryzen/bootstrap`; its interval waves remain unsubmitted. That Ryzen preflight subsequently passed (seven tests / 22 assertions, all 21 source restores), but the coordinator superseded the timing census with a one-run-per-boundary work screen. **Exact final work determinism is already false for the wall-censored candidate**: the five EPYC full totals are 11,365,077; 12,268,637; 11,464,485; 12,220,881; and 11,355,285. Baseline is exactly 1,037,946 every time. The original records remain intact; no common median is substituted for equality.

The new any-CPU packet preserves each job's real CPU and exact source identity. Two three-repeat endpoint jobs will confirm the cross-model behavior before the 21-job screen; completed-attempt prefixes are also compared rather than treating wall-censored totals as deterministic. Fast packet preflight `7ed3b969-762e-44d0-a689-0f4b476531a1` is active at `runs/lane-i/paxos/work/bootstrap`. It rechecks endpoint restores and the changed audit/CPU handling; all source pack and manifest hashes match the prior full 21-restore qualification. The fast work-packet preflight passed: seven tests / 23 assertions and two endpoint restores; all 21 source-pack identities are unchanged from the earlier full restore check. Two three-repeat cross-model endpoint jobs are active as `e4a4bdd4-367e-4632-9ac2-1ebfc28cf907`, output `runs/lane-i/paxos/work/determinism`. The 21-job work screen and the old three timing waves are not yet submitted. Five-repeat same-model timing is now reserved for the culprit and repaired candidate. **Cross-model endpoint confirmation is complete**: three runs each on EPYC 9455 and Ryzen 9 9950X, zero audit issues. Baseline final counters are identical; candidate censored totals are not. The completed-attempt prefix is stable across both models: the first divergence is `Decision keeps members's bound through members$Decision` (pass 1, family 45), baseline proven with 38,917 solver / 26,245.7672 full units versus candidate unknown with 4,720,424 solver / 224,058.0405 full units. The latter inserts 30 eager count-completion instances. This is a provisional causal lead, not yet a named culprit. Full check: `runs/lane-i/paxos/work/determinism/cross-model-audit.json`.

**All 21 source boundaries are now in one parallel any-CPU wave**, task `239509c1-c5e0-430c-b23a-e30101026896`, output `runs/lane-i/paxos/work/boundaries`. Each job retains its CPU, raw strict outcome, complete per-law work and censored totals; no cross-model wall-time median is claimed. The fast screen does not pretend wall-censored total work is deterministic and is not a substitute for the final five-repeat culprit/fix confirmation. The complete 21-point screen now has **zero audit issues**: all seven earlier points prove at exactly 1,037,946 full / 6,915,544 solver units; all fourteen points at or after `1550512d` return unknown. See `runs/lane-i/paxos/work/boundaries/screen-summary.json`.

### For lane B — eager completion is the first failing change

The first bad merge is **`1550512d`**, whose production delta moves count-law completion before the first model query. The first affected bound obligation goes from 38,917 solver / 26,245.7672 full units and proven to 4,894,670 solver / 225,271.9765 full units and unknown, with 46 eager instances. Later requested-map narrowing reduces that to 30 instances but does not restore the proof.

Generic repair **`dd036dd7`** removes only the eager call: sparse proof search runs first, and both existing bounded, requested-map-only stuck-model completion paths remain. It changes no kernel rule, strict budget, candidate set or protocol. Ordering tests now forbid pre-query completion; false-INIT rejection and independently checked positive certificates remain, with an additional easy count certificate that must not trigger unnecessary completion. Focused proof/type/lint validation is running on boat as `faf8af80-c961-4eba-a68f-2ec7a0ef0e31`. The first qualification did not pass: 22 focused tests passed, but the newly added exact-zero fixture did not prove. TypeScript passed; lint found an unrelated `String(build.logs)` diagnostic in `bootstrap-check.ts`, now repaired. The existing three certificate/false-INIT tests all passed. Original failed receipts remain at `runs/lane-i/paxos/fix/validation`; they are not relabelled as passing. The bounded source-paired probe (`e46707c9-384b-4243-925c-706a4ab1600e`) reproduced the exact-zero non-proof on both original and repaired sources, so that fixture was not a repair regression. The initialized conditional three-element claim proved on both, with both certificates checked and no completion event. Corrected-fixture candidate `8de9dadb` leaves production byte-identical to `dd036dd7`; separate focused and type/lint controllers are active as `2460c129-5838-44c1-8863-599bf46196d7` and `ab895207-670a-45b2-bff3-94eeaabad575`. Focused requalification now passed on exact candidate `8de9dadb`: **23 tests, 106 assertions, zero failures and zero source-audit issues**. The second full check passed TypeScript but failed lint on the new restore helper’s unused `join` import. That import is now removed; the failed check remains preserved. Five-repeat Ryzen culprit/fix confirmation (`8d5c2bc7-07b4-4c3c-bb74-543503609952`), seven full-suite shards (`e3ce5019-86f7-4982-ae4f-a97bbded5cec`) and strict consensus rechecks (`286e798e-11ee-4764-b6c7-6bbed1166400`) are now active, using the same qualified frozen packet. No result is claimed for those pending runs. Main has advanced to `8214a543` (optional-choice comparison context and optional-calendar operand rejection), and that P1 fix is merged into the integration branch. **Every next gate uses `8214a543` as its baseline.** The active frozen-source runs stay untouched and count only as historical repair diagnostics, not a new-main gate. The lint-corrected, merged candidate is `d3adf3c9`. New-main qualification (`17e9227a-a575-4e49-a177-d69592a10186`) now passes with **54 tests / 740 assertions, TypeScript clean, zero lint warnings/errors and zero source-audit issues**. Ten historical Ryzen repair trials all prove at exactly baseline work; the culprit loses all ten. One noisy baseline trial remains explicitly unknown, not discarded. Lane D (`t6p`) has been asked to run the full final gate for **baseline `8214a543` versus candidate `d3adf3c9`**, including the known CHC and ITS/resource cases. The historical consensus run returned three measured Ryzen pairs, all proven on both sides, at 3,256,350 → 3,251,424 full work; two other jobs are CPU skips. Five-pair coverage is therefore incomplete and is not called qualified. The historical unit run completed six of seven shards with 1,405 recorded passes, one failure and 17 skips; the failed shard stopped after `core/search.test.ts` exceeded Bun’s unchanged 5,000ms timeout at 6,434.45ms. This is not yet attributed to environment or code. A full merged-source suite is now running (`969e8315-cd78-46a9-8397-e911c8cddf48`), alongside three paired runs of the unchanged search test on `8214a543` / `d3adf3c9` (`90371148-31aa-474c-8a87-3fad952373c5`), with no timeout increase. The paired search rerun is now source/trace-qualified with zero issues: all six processes pass, 60 test executions / 270 assertions, target duration 2.16–3.75 seconds, unchanged five-second timeout. Its initial audit caught an incorrect expected `8214a543` protocol-model hash; independent `git show` hashing confirmed the correct per-revision value, the initial failure is retained, and no raw receipt was changed. Lane D has been informed; full-suite confirmation and the final gate remain pending/RED.

The five requested new bar identities are running three alternating pairs each: CHC hsortprime and up3, ITS-SCC bio, ITS bio and cover. Controller `bbe68e82-5c9e-4205-a149-3dfba2b57344`; outputs `runs/lane-i/paxos/bar`. The existing qualified resource helper retains per-process-tree sampled peak RSS, per-PID peaks, free memory, OOM counter deltas and PID-correlated kernel logs. A SIGKILL alone will not be labeled OOM. Budgets, source SHAs and the canonical roster are unchanged; a separate diagnostic roster is passed explicitly. The paired reruns are now collected: **30 children / 15 pairs**, source/RSS audit zero issues. Independent reporter qualification passed on boat: **eight tests / 24 assertions**, and its full generated audit exactly matches the retained local summary. Batch `20261110-050728-57rvdx`, snapshot `0e8dce22cdc6`, task `37a8c6a2-6880-4678-9ae3-440c3edaf98b`. They contain **10 PID-confirmed kernel OOMs**, split five baseline and five candidate, with sampled aggregate process-tree RSS about **13.31–13.54 GiB**. ITS bio OOMs 3/3 on both sides; SCC bio OOMs baseline 1/3 and candidate 2/3. Cover OOMs baseline once; candidate times out 3/3, so the original candidate cover SIGKILL remains unattributed. Hsort returns checked-IMC sat 3/3 on both sides with six deliberate raw parent SIGKILLs; up3 returns completed sat 3/3 both sides. Only those three up3 pairs have both processes exit zero. Eight strict timeouts remain. This does not establish a complete no-loss bar and does not retroactively assign a cause to original -9 rows. Full data: `runs/lane-i/paxos/bar/resource-summary.json`. Sampled RSS is not an exact OS high-water mark; all reported maxima match retained samples and terminal markers.

## Earlier handoff — prerequisites passed; superseded by the RED final gate

The final current-source qualification of **`bf011901`** passed on boat: **173 tests / 3,410 assertions**, zero failures, and **zero TypeScript/lint warnings or errors**. The emitted count-runtime hash is independently unchanged. Batch `20261110-035600-xl5s32`, snapshot `31b4c9d28b5a`; both jobs ran on exclusive Ryzen 9 9950X workers. Audit: `runs/lane-i/final-prereq/lint-final/validation/validation-audit.json`.

The separate strict confirmation has **10 paired repeats / 20 proven sides**, zero losses and zero audit issues against **`4497c4b0`**. The requested candidate is `bf01190119f9409077a36e11a4a5b763fb6c1cad`; its production/protocol/kernel/gate paths are byte-identical to strict source `8d35b7f1`. Only the bounded research formatter/test and recorded evidence differ. Re-gate scope and the seven bar identities are written in `runs/lane-i/final-prereq/lane-d-request.md`. The exact-source request was delivered to existing Lane D terminal `t6p` (receipt `started=true`, turn 20), and the coordinator was notified. Delivery is not gate admission or completion; **no final-gate success is claimed**. Every earlier failed check remains retained.

## New main `4497c4b0` — pre-lane mechanical qualification passed

The coordinator moved main from `b788e195` to **`4497c4b05c3111959a2b8d808c426a0e3cab3f01`**. This merge retains the CI-only plain-file/decision-law work, exhaustive comparison (tests, never proofs), source-free helper runtime/default interpretation, opt-in user-helper compilation, extractor absence/choice fixes and bar class propagation. `core/dsl.ts`, `core/machine.ts` and the other production paths merged automatically. The sole textual conflict was **`scripts/test-shards.ts`**: I retained every existing MLDR/count/recovery/kernel test and added main's `extract-absence.test.ts` and `extract-choice-joins.test.ts`; main's new compare/mutate/runtime tests were already included by the automatic merge. No `kernel/` or `lean-kernel/` change is introduced by this merge. All three boat jobs have returned and passed the receipt audit: **202 tests / 89,632 assertions, zero failures**, plus **zero TypeScript/lint warnings or errors**. All three workers were exclusive large VMs with no co-tenants. This qualifies only the pre-lane source `91f2d2d9`, not the later five-lane integration and not a final gate; raw receipts and a reproducible auditor are at `runs/lane-i/main-4497/`. Source `91f2d2d9` is captured by snapshot `60b56e8cdad1`, batch `20261110-033045-5mxrqt`, task `b9fad643-2044-44cd-8cf0-cc78790b67a6`: full type/lint and roster validation plus runtime/DSL and extractor/bar test groups. The historical replacement wave is independently frozen at its earlier snapshot.

**For lane D:** the next final-gate base is `4497c4b0`, never the old base. The earlier exact-source request below is now historical only. Already running jobs need not be cancelled, but no result transfers across the new baseline. A fresh candidate SHA will follow qualification and the newly published lane-tip integrations. The consensus_forall bisection, its immutable source pack and all running historical jobs remain pinned to `b788e195` as explicitly requested.

## Final-gate prerequisite — qualified; re-gate request delivered

Coordinator instruction was to hold Lane D's final gate until both fixes and the independent five-plus-repeat comparison passed. **Those prerequisites are now met; the final gate itself is not yet run or green.** Candidate `5829b23d` still carries both isolated causes: default focused recovery (`55b5846a`) and eager count-law completion (`60b8c37a`). Integrate both Lane A and Lane B fixes as they commit. Before any new final-gate request, Lane I must run and audit **at least five strict repeats per side on Ryzen 9 9950X against `4497c4b0`**, showing no `consensus_forall` loss. Historical b788-based bisection results cannot satisfy this new-baseline check. Existing cheaper validations continue and are not cancelled or relabelled.

## Consensus fix integration — qualification pending

- **A `47dfc340`, production fix `1564709f`:** ordinary counted reasoning gets its opportunity before finite-input recovery, within the existing attempt deadline. Resolved `core/counts.ts` by retaining integrated member-witness freshness handling plus the new readiness/scheduling logic; no proof verifier was changed. Resolved the quick-roster conflict as a union without duplicate seed entries, and added the previously unlisted `finite-tiny.test.ts` / `finite-tiny-houdini.test.ts` to both the roster and its coverage assertion. New recovery tests include certified-CTI refusal and a checked ordinary counted proof. The incoming report is archived at `runs/lane-i/incoming/20261110/A-47dfc340.md`. No performance or gate claim yet.

- **B `e7bc9adb`, production fix `337294ea`:** complete only assumptions about maps read by the requested count target; unrelated count assumptions retain ordinary demand-driven instantiation, and field targets do not trigger speculative completion. Production and fixture changes merged automatically alongside A's scheduling fix. Preserved all positive conditional-certificate and field-proof tests plus the stronger false-INIT/unrelated-map control. The only new conflicts were the report and quick roster; the integration roster already contained every incoming entry, so it was retained. Report archived at `runs/lane-i/incoming/20261110/B-e7bc9adb.md`. Both fixes are now integrated at `6ca0a5fc` but remain unqualified as a combination. Three cheap check/test jobs and twelve CPU-guarded consensus cohorts are prepared. Every eligible Ryzen 9 9950X cohort runs five fresh-process original strict pairs against `4497c4b0`, with alternating arm order, unchanged 60-second limits and no forced recovery/completion opt-outs. Nonmatching CPUs produce explicit skips and zero coverage. Whole-cohort Brotli capture plus durable raw files protect collector integrity; source/harness hashes, semantic verdicts and all five repeat identities are audited before this prerequisite can pass. The first post-fix qualification at `44ad3947` returned **167 tests / 3,386 assertions, zero failures**, but its check exposed a contextual generic inference error in A's new local `result` variable (`Tried<unknown>`). Supplying the existing `Proof` type argument fixes the inference without a cast, suppression, deadline or runtime change. The original failed check and still-running strict source are retained; a clean current-source check remains required. The own-pair batch is `20261110-034240-kp8mpv`, snapshot `2a77bdce4309`, task `e88b75c0-1ad7-43aa-bcbd-b26df6ca5461`, at exact source `44ad3947`; the completed audit reports **eleven CPU skips, five accepted pairs, zero losses and zero issues**. All ten strict sides prove on one exclusive Ryzen 9 9950X. Baseline times are 50,536 / 27,124 / 26,564 / 29,757 / 30,028 ms; candidate times are 22,249 / 17,401 / 19,785 / 19,183 / 24,056 ms. Every baseline has work 14,498,189 / full 2,665,853; every candidate has work 11,093,727 / full 3,256,350. The candidate is faster in each measured pair but full work remains higher; neither metric is hidden. This is a passed prerequisite for measured source `44ad3947`, not a final gate. The subsequent `Proof` annotation emits byte-identical count runtime, verified separately. A final exact-source confirmation will include the new qualification-only follow-ups. The targeted qualification is `20261110-034241-psw272`, task `2d96103e-fdc4-4028-a574-cd0e32808295`; the **167 passing tests / 3,386 assertions** and failed check are retained separately. Type-corrected source `a197ab4f` returned an exact **emitted-runtime identity** result, SHA-256 `2da24a9a74a03b527c1ba111cbcc510ea0bc8627e5dcb7b5dd81a2d15d136efa`, in batch `20261110-034514-vod9cn`, snapshot `3e9d01824275`, task `402a7171-6b71-4cae-a79c-820e738cc2db`. Its check still failed: the old-source comparison copy was placed under `integ-input/` with a `.ts` suffix, so the normal compiler scanned that misplaced old source and its invalid relative imports. This is a validation-fixture failure, not a clean check. Preserve it in `runs/lane-i/consensus-fixes/type-recheck/validation`. The corrected recipe performs the same byte comparison, renames only that disposable reference to `.source`, and runs the full unchanged check; it is now task `7f92354e-07f5-437b-b964-dbc0f5a815da`, output `runs/lane-i/consensus-fixes/type-recheck-v2/validation`. No compiler exclusion or production edit was added. That corrected run passed TypeScript but exposed one lint error in the incoming research-only `s17-trace.ts`: an unknown object was passed to `String`. The new bounded formatter preserves real Error names/messages and primitive text, never traverses arbitrary objects, and has explicit regression tests. Its first ternary-based implementation still triggered the typed `no-base-to-string` rule, despite **173 tests / 3,407 assertions passing**. Replaced the ambiguous narrowing with explicit primitive branches; no production/protected-harness file changed. This original lint failure is also retained, and a fresh check is required. The original lint failure remains retained. The final prerequisite jobs now bind exact source **`8d35b7f17506fcd1f8c1d9a05ec2624c924c855d`** to baseline **`4497c4b0`**, shared snapshot **`329ef3cbe804`**. Check/tests: batch `20261110-035016-m45qys`, task `cf6991fe-c44e-4899-beb7-3b28dc6c0f00`, output `runs/lane-i/final-prereq/validation`. Strict confirmation: batch `20261110-035023-3p9acg`, task `d1deb71c-dc90-419c-b819-e7573a13be81`, new cohort IDs 13–24, output `runs/lane-i/final-prereq/strict`. The old comparison source now has a `.source` extension and cannot enter TypeScript's glob; no real source is excluded. This is a distinct exact-source confirmation after type/test/reporting follow-ups, not a duplicate of the earlier source-bound five pairs. The strict confirmation has now passed its full audit: **10 paired repeats / 20 proven strict sides**, zero losses, zero source/phase/receipt issues, and ten explicit CPU skips. The two accepted cohorts ran on separate exclusive Ryzen 9 9950X workers (`bx_5f32uf5a`, `bx_7m649ges`). Every candidate was faster than its paired baseline; full work remains 3,256,350 versus 2,665,853 and is not hidden. Exact rows are in `strict/paired-summary.tsv`; full per-law traces remain losslessly retained. This satisfies the requested own five-plus-repeat no-loss prerequisite for `8d35b7f1` against `4497c4b0`. Current repair candidate `bf011901` has byte-identical production/protocol/kernel/gate paths; only research error-formatting/test/reporting changed. **Lane D remains held only for the fresh clean type/lint qualification.** The immutable input cache is `/private/tmp/lane-i-final-prereq.aqoHxz`. The targeted suite returned **173 passing tests / 3,407 assertions**; the check still failed on the research formatter's ternary narrowing. That failed check is retained. The formatter now uses explicit primitive branches, with added bigint/boolean/symbol coverage. The switch-based repair passed all 173 tests / 3,410 assertions but triggered the repository's exhaustive-switch rule; it is now an equivalent if-chain with no implicit cases or suppressions. Repair source **`b150220e`** is byte-identical to `8d35b7f1` in production, protocols, kernel and gate paths; only the research formatter/test and reporting changed. Its fresh check/test controller is `59b380bd-166d-4692-afc2-6729509fa827`, output `runs/lane-i/final-prereq/lint-repair/validation`, input cache `/private/tmp/lane-i-lint-fix.brmWBB`. The strict batch remains untouched. That repair returned **173 passing tests / 3,410 assertions**, but the exhaustive-switch lint rule rejected its fallback-only object/function case. The equivalent explicit if-chain at **`bf011901`** avoids both lint ambiguities without casts, suppressions, object traversal or production changes. Fresh full check/tests are task `18442b80-e0ea-4723-ac52-14f7df76e6e8`, output `runs/lane-i/final-prereq/lint-final/validation`, using immutable `/private/tmp/lane-i-final-lint.CqS19p`. A direct Git comparison confirms that production, kernel, gate, protocol, dependency and canonical-roster paths remain identical to strict source `8d35b7f1`. All admitted inputs stay immutable; the new check uses `/private/tmp/lane-i-consensus-current.VxJsac`. **This still does not request or replace Lane D's final gate.** Raw receipt bytes are preserved rather than normalized for whitespace style.

- **A follow-up `d0c2c113`:** its explicit `Proof` type argument matches the integration repair exactly and merged automatically. Adopted the stronger end-to-end recovery fixture with production's bounded-widening mode enabled; its checked-proof assertion is unchanged. This follow-up changes tests/measurement tooling, not the emitted production runtime. Only the report conflicted, archived at `runs/lane-i/incoming/20261110/A-d0c2c113.md`.

- **B follow-up `722701c2`:** production is unchanged. Integrated its stricter completion receipt auditor and negative controls, adding that test module to the canonical roster/coverage assertion. The two incomplete learning-switch census jobs remain explicitly rejected in B's own report; their follow-up results are not substituted for Lane I's independent runs. Only the report conflicted, archived at `runs/lane-i/incoming/20261110/B-722701c2.md`.

## New lane-tip integration after `4497c4b0` — active

- **A `0bab28e2`:** production finite-search files merged automatically, preserving the existing whole-family/source-interpreter certification boundary. New interval/seed paths remain opt-in; front-loading replaces rather than doubles the 256-attempt allowance. The sole conflict is the lane report, preserved verbatim at `runs/lane-i/incoming/20261110/A-0bab28e2.md`, while this continuous integration report is retained. Added the two new seed test modules and the qualified diagnostic tests to the canonical quick roster and its coverage assertion. A's pilot is still pending and does not satisfy its five-of-seven criterion by assertion.

- **B `4ce50c00`:** preserved the scalar-premise documentation and new coverage. Resolved `core/counts-completion-order.test.ts` by retaining **all three intents**: the existing scheduling/positive field probe, Lane I's independently checked concrete-key count certificate, and B's explicit false-INIT regression (`Total=2`, claimed `<=1`). No completion behavior was changed. The incoming report is at `runs/lane-i/incoming/20261110/B-4ce50c00.md`; B's unary-only scheduling prototype remains rejected/research-only, not silently promoted as a performance fix.

- **E `e1b8d3b7`:** production merged automatically. Preserve source-bound strictness when constructing sufficient member-inclusion guards; retain the four strict/inclusive combinations and boundary proof/refusal tests. Only the report conflicted; incoming report is at `runs/lane-i/incoming/20261110/E-e1b8d3b7.md`.

- **F `c1521262`:** production merged automatically. Preserve compensated single-set count transports as untrusted proposals and their copying/conjuring negative controls; the kernel still checks every retained frame. Only the report conflicted, archived at `runs/lane-i/incoming/20261110/F-c1521262.md`.

- **Fable `f6b383f0`:** `core/machine.ts` merged automatically with new main. Retain both CI's source-free helper/runtime defaults and the interpreter's per-write environment reuse / tuple-write memoization. Lane A's newer finite-search implementation remains intact. Only the report conflicted, archived at `runs/lane-i/incoming/20261110/Fable-f6b383f0.md`. Two incoming raw receipt tables contain pre-existing trailing spaces; their bytes are preserved rather than normalized. The source diff passes whitespace checking; those two historical receipt files are the explicit exception.

All five reviewed lane tips and main `4497c4b0` are now integrated at `399c328a`. The combined check and seven canonical test shards are running as task `a40988c4-85d4-450d-bac1-e443dd7d097e`, batch `20261110-033350-zdkdwh`, snapshot `d0c41b3366da`. That batch returned all seven test shards with **1,294 passing test executions / 335,448 assertions**, zero failing test summaries and valid isolated placements, but **the check failed** on two research-only TypeScript inference errors: unknown `Object.entries` values in `fast-step-census.ts`, and a literal-boolean `Map` inference in `frame-cut.ts`. Original failed receipts remain preserved. The repairs add only explicit `Machine` / path-entry types; they do not alter production or diagnostic runtime behavior. Fresh type/lint and targeted qualification remain required; no passing check or historical gate result is transferred to this source.

The rebased paired input is prepared from an exact **26.88 MiB** Git archive of `4497c4b0`; its SHA-256 is `9508c2e454b4b6eefa4093bbf6efba569d09bea4bc89646b6e8df7bc0a3a6dc6`. Vendor archives are hard links to the unchanged, checksum-bound inputs, not copied trees. Three original strict-60-second MLDR pairs and the unchanged 87-pair generation census are now admitted against this new base, with exact candidate **`5829b23d7e7d64136625154c9b161402a89aff19`** and shared snapshot **`93f69f174116`**. MLDR: batch `20261110-033552-8cp8b1`, task `ec4eb3bf-439a-46c3-bce8-ec765d181b26`, output `runs/lane-i/rebased-4497/mldr`. Census: batch `20261110-033548-0tv266`, task `80f7ab06-7b96-49d5-b898-5d2c21b6a218`, output `runs/lane-i/rebased-4497/census`. Source `5829b23d` differs from the combined-test source `399c328a` only in reports and validation manifests, not production, kernel, protocol models or gate code. These are pending iteration results, not a final gate. Input metadata is retained in `runs/lane-i/rebased-4497/input/identity.json`; the local data cache is `/private/tmp/lane-i-base-4497c4b0.TW93Bm`. Strict trace capture is lossless gzip plus a durable on-VM raw file; it wraps but does not change the existing harness or its deadlines. **Both pre-fix batches have now returned and are audited.** All six original MLDR sides remain **unknown**; the three candidates stop near 59 s with work 30,645,470 / 39,868,106 / 42,355,941. Baseline work is 2,657,026 in every pair. The generation census has **87 complete pairs, zero receipt issues**: all **84 unrelated pairs have identical canonical hashes**, while MLDR remains 27 baseline / 34 candidate with stable hashes. These results bind `5829b23d` versus `4497c4b0`; none is promoted to evidence for the later A/B fixes. Raw envelopes, decompressed traces and audits are retained under `runs/lane-i/rebased-4497/`.

## Historical replacement cohort returned — ten-point coverage gap closed

**Wave 6 is complete and audited:** 64 CPU skips, 80 accepted pair receipts, and **eight repeats at each of the ten formerly missing points** on exclusive Ryzen 9 9950X workers. Every point has at least five complete pairs (70 complete total), satisfying this historical coverage gap. All source, transport, placement and trace checks passed. Three historical losses and ten incomplete pairs remain explicit; this is not a no-loss result. Full traces and per-law/phase data are in `runs/lane-i/merge-bisect/wave-6/cohort-audit.json`; the bounded view is `coverage-summary.json`. Baseline here remains historical `b788e195`, not the new Paxos baseline or final-gate baseline.

Wave 4 returned all 36 scheduler rows. Its repaired lossless transport passes the strict audit: **34 CPU skips and 20 accepted pair receipts across ten revisions**, with no source/transport/semantic-audit issues. At that earlier point each revision had only two attempted pairs, so none met the required five-repeat historical qualification; wave 6 above has now filled that gap. A further lower-priority 72-slot coverage wave intended to use fresh cohort IDs 401–472 with the same immutable b788-based source pack and qualified lossless runner; it does not touch or replace the new-main final-gate candidate. CPU skips will still count as zero coverage. Admitted batch `20261110-040105-61i84t`, snapshot `b9bf84188d31`, controller task `b9e88b69-007f-497f-ada0-eb503b961f07`, writes `runs/lane-i/merge-bisect/wave-5`; it runs in the lower-priority `submission` class so it does not replace Lane D's gate work. **Wave 5 returned with 72 pre-execution failures and zero measured pairs:** every log says `Module not found "regression-driver/merge-bisect-cohort.ts"`. I omitted the required driver/source-pack bootstrap while reusing a bare runner and mounted only the driver directory under the wrong alias. This is a submission error, not a new prover failure or worker OOM. Original failed logs and `wave-5/bootstrap-audit.json` are retained. A replacement will not be widened until a single-job checksum/import/restore preflight passes. That preflight **passed**, with zero audit issues: 70 file hashes, a successful complete import build, 11 manifest revision identities, and clean baseline/V12 source-plus-dependency restores. Batch `20261110-043701-j7vdc7`, snapshot `f59d2d7a4055`, task `386c1fa8-eb2b-46bc-afdf-c8b366a48b8f`; audit is `runs/lane-i/merge-bisect/bootstrap-v6/validation/bootstrap-audit.json`. This EPYC bootstrap check contributes zero measured pairs. It uses a private runner (`/private/tmp/lane-i-history-runner.Df4NKx`) and a complete read-only staged bundle (`/private/tmp/lane-i-history-data.33ppZf`) with explicit driver, incremental pack, original delta, and shared pack directories. Original incremental manifest/pack hashes are unchanged. After that qualification, fresh IDs **501–572** were submitted in the lower-priority `submission` class, controller `2dcdf22e-7899-4361-af50-29467f18da6c`, output `runs/lane-i/merge-bisect/wave-6`. It uses the exact same private runner and immutable bundle. Measurement results remain pending; CPU skips and prior missing-driver failures still count as zero coverage. Nineteen pairs have both semantic results; seventeen prove on both sides. The b09 and Fable `7eb16797` checkpoints each retain one observed strict loss; one earlier checkpoint pair is incomplete. Raw failures and censored results remain separate. The first-A/default-focus and first-B/completion attributions are not replaced by aggregate wall figures from this still-small cohort. Full per-law data and bounded summaries are at `runs/lane-i/merge-bisect/wave-4/`.

## Coordinator follow-up: merge bisection and bar resource attribution — active

The requested wide boat follow-up is admitted, with no production edit and no new passing gate claim. The source pack covers **all 62 first-parent merge boundaries** between `b788e195` and V12, plus the endpoints. It is a deduplicated **8,965,134-byte** incremental Git pack, not another whole-tree archive. Every pinned revision has the same vendor submodule identities. The first coarse wave includes the five explicitly requested lane merges and V12; matching Ryzen 9 9950X workers run **five strict 60,000 ms paired repeats per revision**, with generation/finite-pass wall time and full-name per-law solver/full/counted work. Nonmatching CPUs are explicit skips and cannot satisfy the repeat count. The fresh public-attempt trace wrapper is observation-only; source trees, original protected harness hashes, and before/after trace-patch hashes are retained.

- Bisection: **42 jobs**, batch `20261110-025306-zdy134`, snapshot `a5fb3aa8dae9`, task `9ab5c34d-b73a-45a8-bd22-dbc25a55ba82`, output `runs/lane-i/merge-bisect/wave-1`. The initial manifest omitted the non-merge historical b09 checkpoint; its original three jobs cannot execute that revision and are not counted. A separate corrected manifest adds that existing packed commit without modifying admitted inputs: **three jobs**, task `9783eb78-ec90-4568-8a85-21d3d9b9bcb8`, output `runs/lane-i/merge-bisect/b09-fix`. This is not a duplicate completed experiment.
- Bar: **exactly the seven affected task identities**, three rotated pairs each, original baseline/b09 source and original solver arguments/deadlines. Batch `20261110-025352-1lx5c9`, snapshot `7ecd05d31698`, task `591eb54b-99e3-41e6-8609-6889079465b3`, output `runs/lane-i/regressions/bar-resource`. Child PIDs, VM OOM counts, cgroup events and PID-specific kernel messages distinguish actual process losses from scheduler preemption; a final zero controller exit alone is not success.
- Instrumentation qualification passed on boat: batch `20261110-025454-ex3k2j`, snapshot `e1dcd65b2416`, **one test/two assertions**, full TypeScript/lint **zero warnings/errors**. The admitted bar v1's space-only parser cannot read tab-separated VmRSS: **its zero RSS peaks are unavailable data, not zero memory**. PID/OOM/exit evidence is unaffected. The checked v2 parser fixes whitespace for subsequent runs; existing inputs were not overwritten.

### Original bar-worker evidence

Read-only collection found five original workers stopped; the two available workers' old job directories have been removed. No VM was resumed or stopped and no scheduler state was changed. A broader retained kernel query did recover **six explicit global OOM deaths of Bun** on the original `its-bio_t2_ari` worker `bx_7vs7decr`, 19:29:04–19:31:48 UTC, at roughly **14.4 million KiB anonymous RSS each**. Their successive spacings agree within 1.3 seconds with the six original child durations, across both baseline and candidate. Original totals by side are baseline **18 SIGKILL / 3 timeout / 15 zero exits**, candidate **15 SIGKILL / 4 timeout / 17 zero exits**; there is no completed candidate-only verdict loss in these records, but the censored comparisons are not a no-loss proof. This is strong sequence correlation, not an invented direct PID mapping: the old child PIDs were not retained. The original TIP list task has all six children exiting **124 at 60.26–60.58 seconds**, with no OOM in the queried kernel window: bilateral strict timeouts, not six completed candidate losses. Exact raw API/kernel receipts and conservative attribution are in `runs/lane-i/regressions/bar-forensics/`.

### For lane A — `55b5846a` default focused recovery accounts for the large full-work increase

The follow-up ablation returned in batch `20261110-031531-23aey6`, snapshot `aed15294f79d`, task `350fbf12-9c2c-4299-a3ad-5a38ff85081f`. All **12 children prove consensus_forall**, with zero source/trace/semantic-audit issues and identical generated-name lists in every triplet. This isolates the existing `GDP_COUNTS_FOCUS=0` opt-out; in focus-only runs the source-file before/after hashes are identical. Commit `55b5846a` introduced the default finite-input focused-recovery gate in the first-A ancestry.

| First-B configuration | Successful solver work | Successful full work | Screening pairs |
| --- | ---: | ---: | ---: |
| unchanged | 18,135,054 | 4,898,768 | controls below |
| completion off only | 14,681,480 | 4,556,168 | 4 |
| focus off only | 13,768,302 | 2,743,349 | 2, Ryzen 9 9950X |
| both off | 10,131,635 | 2,374,867 | 2, EPYC 4585PX |

Focused recovery alone contributes **2,155,419 full-work units** in this counterfactual; B completion contributes **342,600** with focus on. Together these explain the main expensive proof policies more accurately than blaming generation or inclusion. Two Ryzen screening pairs are not a five-repeat qualification, and variable wall times do not support a universal +15-second claim. The effects are independently reproducible policies, not an identified merge-conflict resolution error. **Do not ship the blanket opt-outs:** they are causal probes, not a generic fix preserving the new recovery capability. No production, kernel, budget or law change has been made. Full raw profiles, generation timing and source hashes are in `runs/lane-i/merge-bisect/first-b-focus/`.

### For lane B — `60b8c37a` count-law completion is a causal contributor at `1fc01c10`

The first wave and corrected-b09 wave returned with **39 CPU skips and six accepted Ryzen jobs**. The source/placement/raw-trace audit has **zero issues**, covering **30 complete strict pairs**. Four historical revisions now meet the five-repeat requirement; the ten other selected points do not yet and are not inferred from skips.

| Source | Complete pairs | Successful solver work | Successful full work | Median paired post-generation delta |
| --- | ---: | ---: | ---: | ---: |
| first A `08c45710` | 15 | 13,236,043 | 4,557,617 | +3.543 s |
| first B `1fc01c10` | 5 | 18,135,054 | 4,898,768 | +7.893 s |
| middle `a3930f44` | 5 | 18,135,054 | 4,898,768 | +6.851 s |
| latest A `aa9bffe6` | 5 | 18,135,054 | 4,898,768 | +1.327 s |

Baseline successful work is always **14,498,189 / 2,665,853**. The first-A cohort also contains **one baseline-proven/candidate-unknown pair** (replica 3, repeat 5), retained in the audit. Full work rises already at A; the later solver-work step is localized to B. No measured run entered `finiteHoudini` (finite-pass time zero). Faster generation and variable whole-run wall times can mask proof overhead; this does **not** support a universal +15-second wall claim.

At `1fc01c10`, the full-name law `every x, y, z with x < size ∧ y < size ∧ ¬(x = y) ∧ z < 64: never Voted[x] is 0 and 1 <= Decided[64·y + z]` incurs the largest extra work. Its trace contains **seven count-completion additions**. The merge adds `60b8c37a` (complete count-law tuples before SAT drops) alongside `bd82e993` / `3837bb36` (prefer/admit member inclusion instances). **Four isolated screening jobs** compare unchanged first-B, baseline, and either completion-off or inclusions-off under the original strict budgets: batch `20261110-030728-obhsap`, task `4c570661-3f6b-49cb-87e2-2fde41f540e7`, output `runs/lane-i/merge-bisect/first-b-ablation`. These are proposal-only experiments, not production fixes, and their non-9950X timings will not count toward merge qualification.

The isolated ablations returned **24/24 proven child runs**, with zero source/trace/semantic-audit issues. In all four completion-off triplets, solver work falls from **18,135,054 to 14,681,480** (−3,453,574), and full work from **4,898,768 to 4,556,168** (−342,600). Disabling member inclusion leaves both counters **exactly unchanged** in all four triplets. Thus `60b8c37a` is a demonstrated contributor, not merely a temporal correlation; the member-inclusion hypothesis is falsified for this workload. This is not the whole regression: first A already increases full work substantially. The further two-job focused-recovery batch has also returned and is detailed under For lane A above. No production feature has been disabled.

The original equality check on entire protected files was too strict for historical comparison: A extracts only MLDR from `ic3syn/models.ts`, leaving consensus unchanged. It was replaced with independently Git-derived **source-specific hashes**, covering all 65 pinned revisions and six unique protected blobs. Actual source mismatch is still rejected. Full raw traces and recomputed phase/per-law values are required.

New collective cohorts let every eligible Ryzen worker run one pair at **all ten missing points**, rather than consume it for one point while other CPUs skip: batch `20261110-030544-1ku5gk`, task `4df5b469-b402-48f4-803e-e1dd1281f809`, output `runs/lane-i/merge-bisect/wave-2`. This wave returned with 34 CPU skips and **two collector failures** (`mb-cohort-101`, `mb-cohort-109`). Both ran all ten children, then rejected the oversized combined encoded payload **before printing or persisting it**. The raw child traces were not retained, so these contribute **zero accepted receipts**, not twenty inferred pairs. The audit rejects both failures explicitly. This was a diagnostic transport bug, not a new solver verdict. After six bar jobs released their workers, an additional distinct-ID cohort wave was submitted: task `e7e57155-4799-4807-8b1b-962b1406fc1f`, output `runs/lane-i/merge-bisect/wave-3`. The additional old-format wave is now complete: **32 CPU skips and four collector failures**, with **zero accepted receipts**. All four fail after the same too-large payload guard; the original logs and rejected audit are preserved. No missing result is credited. The first lossless transport probe preserved the raw traces but did **not** fit: ten archived paired records measured **492,140 bytes** with the old encoding and **481,792 bytes** after decoded gzip, exceeding the unchanged 350,000-byte limit. Its six unit tests / 21 assertions passed, but the real-data load check correctly rejected it before type/lint or new benchmark submissions. The long-window Brotli envelope and per-child/final on-VM archive are now qualified: task `ccf9dc0a-a8ef-4e4e-9c04-a3dfb41001c0`, batch `20261110-032635-tvccjv`, snapshot `90aa2fd78b60`, output `runs/lane-i/regressions/cohort-pack-check-br`. Ten archived paired records occupy **148,564 bytes**, losslessly, below the unchanged 350,000-byte limit. **Six tests / 21 assertions passed, with zero TypeScript/lint warnings or errors**. Every original raw measurement trace remains intact and the existing proof audit still rejects fabricated work. Compression and persistence happen outside measured child runs. The distinct-ID v2 manifest is now admitted for the still-missing coverage: task `9dd29c0a-e262-4489-83aa-65ed960c7eb9`, batch `20261110-032818-a6uet3`, snapshot `3e7feb870f81`, output `runs/lane-i/merge-bisect/wave-4`, IDs 301–336. Source pack, strict limits, CPU filter, original protected hashes and per-law instrumentation are unchanged. Original failed and active jobs are not relabelled, overwritten or counted as complete. No replacement cohort is submitted until qualification and actual failed-job status are known. The ordinary five-repeat rule still cannot be bypassed by a single cohort. The ordinary five-repeat rule cannot be bypassed by a single cohort result; only the aggregate of independently audited receipts can qualify a revision.

Reporter qualification passed on boat in `20261110-030817-n89d22`, snapshot `8431b9597f07`: **four tests / ten assertions, zero failures, zero type/lint warnings or errors**. The separate initial audit qualification `20261110-025955-h709pp` passed three tests/eight assertions. Production remains unchanged. The further reporter qualification passed on boat in batch `20261110-031536-h0o0dr`, snapshot `6bf52a420921`, task `5a69b13e-ff05-4bbb-97b2-909664273a6a`: **five tests / 15 assertions, zero failures, zero TypeScript/lint warnings or errors**.

### Bar attribution complete for the exact rerun roster

All **seven tasks / 21 rotated pairs / 42 child receipts** returned. The resource/source/placement/raw-trace audit has **zero issues**. Outcomes are **10 deliberate checked-IMC portfolio parent handoffs, 9 normal completions, 21 strict timeouts, and 2 PID-confirmed kernel OOMs**. The two new OOMs are specifically **candidate TIP `tip2015/list_weird_concat_map_bind.smt2`, repeats 2 and 3**; their paired baselines time out, so this is a real resource asymmetry, not a completed semantic verdict loss and not a green result. No scheduler-preemption evidence was found.

The apparent unexplained CHC SIGKILLs have a code-level explanation: `compare/chc/kind.ts` deliberately calls `stop()` on the parent when the IMC worker obtains a checked proof, before emitting the final `answer by=imc, answer=sat`. All **16 original CHC kills** have that exact preceding `imc/proven=true/checked=true` and terminal answer sequence. The CHC driver is byte-identical in baseline and candidate (Git blob `31155cc35136b8534f33b7e38acb3dcb73cd84ab`), so this lifecycle behavior is not a new integration regression. All **10 repeated CHC kills** additionally have zero OOM-counter increments and no PID-specific OOM, excluding the observed OOM alternative for these new runs. The attribution helper requires matching task identity, checked proof, ordered timestamps and zero OOM evidence; it **does not change the raw exit, process-completion flag or gate acceptance**. Raw `SIGKILL` is preserved. The old remaining **17 non-CHC kills** comprise the six strongly kernel-correlated ITS bio OOMs described above and **11 original kills whose precise PID cause cannot be recovered**; the exact paired reruns do not justify inventing an original cause. Current ITS/SCC reruns primarily time out without OOM. The original SCC-bio and cover workers subsequently resumed independently under the shared pool. Read-only historical-kernel queries on both found no retained entries for the original window; their current boot times are later than the original failures. These receipts are saved as `bar-forensics/*kernel-recovery.json`. I did not resume, stop, repair or alter either worker, and the eleven original causes remain unknown. Only **three rerun pairs have both processes exit zero**; their answers agree. There is still no complete no-loss bar comparison.

Auditable artifacts: `runs/lane-i/regressions/bar-resource/resource-summary.json`, each task's raw log, `runs/lane-i/regressions/bar-forensics/`, and `runs/lane-i/merge-bisect/first-b-ablation/ablation-summary.json`. The original process failures have not been relabelled as successful proofs.

### For lane D — historical request, superseded by main `4497c4b0`

Previous request, now historical only: **`b4f9018f72010fc1bac07fd47d70348448ad5379` vs `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`**, the already mechanically qualified fixed-fixture integration. Do not start this as the next final gate; the coordinator has moved the required baseline to `4497c4b0`. A direct Git diff confirms its `core/`, `kernel/`, `compare/`, protocol models, scripts and dependency inputs are identical to current committed integration `20cd2615`; later work is diagnostic only. Its production is still V12 `8769061b`. This supersedes older current-candidate requests, not historical receipts. Please include the exact seven bar task identities above and audit the CHC winner/parent lifecycle explicitly: a self-killed parent is not scheduler preemption, but a `checked=true` log alone must not become a fresh accepted proof. Preserve strict deadlines, independent proof validation, CPU labels and both SHAs. The two candidate TIP OOMs, 21 timeouts, frozen strict regression and incomplete five-repeat historical cohorts remain blockers; **this request is not GATE GREEN**. The installed `hc` channel is now available despite the old handoff note: this exact request was also sent to existing Lane D terminal `t6p` (delivery returned `started=true`, prior turn 14). This is delivery evidence, not a claim that D has run or passed the gate. I continue the coverage collection without waiting for another lane.

## Latest lane-tip integration — mechanical qualification passed; no-loss blocked

The latest committed lane tips are now integrated without substitution into any frozen experiment: A `d7d6a9e6` (merge `aa9bffe6`, evidence only), B `72e9da1a` (merge `1550512d`), E `34206459` (merge `d6189c1e`), F `60704669` (merge `f70716da`, research/test only), and Fable `546be441` (merge `7eb16797`). All source merges were automatic; each report conflict preserves Lane I’s continuous report plus the exact incoming report in `runs/lane-i/incoming/20261110/`.

Production deltas: early count-law completion, flags-first member seeding, and sharing runtime breakpoint lists only among writes with identical breakpoint descriptions. No kernel, law set, deadline or counted budget was changed. The guard prototype remains unapplied. An integration test covers shared equal-breakpoint writes alongside a nonshared unequal-breakpoint write, including cell-by-cell interpreter agreement. The new completion-order test is explicitly included in both canonical rosters.

V12 is now admitted at clean source **`8769061bea541a33396819be86f7a5bba0a7bf73`**, unchanged baseline **`b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`**. Both controllers captured tree **`5c02ba03212e`**, image `sc-f0d8daeee6c3`, before this documentation update:

- **9 validation jobs** (check, four changed-test shards, three original-MLDR pairs, negative replay control): batch `20261110-022934-e437u3`, task `b49ff1d1-b416-40ca-a6b6-63ecb7368461`, output `runs/lane-i/v12/validation`.
- **87 generation pairs:** batch `20261110-022931-9ald5l`, task `59a82dbf-fe94-47e8-a6f9-86a5fd21b0a0`, output `runs/lane-i/v12/census`.
- Baseline-to-candidate roster check: **127 changed test modules, zero missing** from the V12 commands. This is a coverage check, not a passing test result.

The existing baseline/vendor archives are reused by directory mount; only small identity/coverage metadata is new. These gate-class jobs validate a **new combined production source**, not duplicates of the still-pending V11 or b09 experiments, whose submissions and inputs remain untouched. **V12 validation returned with one failed test.** Check/lint, shards 2–4 and the negative replay control passed their process checks; the new completion-order fixture failed because its count parameter `row` collides with the law’s bound variable. The first naming-only repair (`682c38e9`, batch `20261110-023348-alajrq`) passed check but still failed its universal-count proof expectation. A boat diagnostic showed the scheduling event is correct, while that universal fixture returns unknown; its field path returns a checked proof. The scheduling test now preserves all ordering/boundedness assertions and mandatory field proof, and adds a distinct concrete-key conditional count certificate that the probe checked independently. This changes no production code or application budget. The intermediate `b504dcca` qualification contained an invalid hand-written conditional AST, caught and fixed with the exact `ite`/`same` constructors used by the successful probe (`359603d7`). That intermediate run is not accepted. The final failed-shard/check qualification is submitted separately in `runs/lane-i/v12/final-fixture`, including the new bar/census reporting code: source `3281b7fff8f0d20a2b0b03116a735c6e37565a48`, snapshot `4947df6babfc`, batch `20261110-024135-jbbe6p`, task `fb52c2f1-fb60-4ae2-a5d8-ad9916d8a76b`. An exact Git diff excluding test modules confirms production `core/` and `kernel/` are unchanged from `8769061b`. **Final qualification passed:** repaired shard 1 has **234 passing tests, zero failures, 8,320 assertions**, including the scheduling-order and independent conditional-certificate checks; full TypeScript/lint has **zero warnings and errors**. Together with the unchanged original shards 2–4, the retained evidence comprises **705 passing test executions / 22,168 assertions** across the 127-module coverage roster. This is explicitly **composite unchanged-production evidence**, not a rewrite of the original failing batch; see `runs/lane-i/v12/qualified-tests.json`.

At the close of that qualification, all Lane I controllers had returned; the newly requested follow-ups are listed above. **The no-loss gate remains RED:** frozen b09 has a reproduced lost strict verdict; new-source MLDR remains unknown; the bar has 33 SIGKILLs and seven timeouts. The frozen upper-bound results remain conditional. None of these are promoted to successful proofs by the passing mechanical checks. All six original-MLDR sides returned **unknown**, not proven: baseline work `2,657,026` each; candidate work `71,968,651`, `24,945,016`, `44,773,626`. Candidate times were `57,730`, `59,006`, `59,001` ms. This is not a no-loss result or an MLDR proof. The V12 generation census also returned all **87 pairs** with zero receipt issues: 84 unrelated pairs have identical canonical hashes; MLDR is 27 baseline/34 candidate in all three, with the same stable hashes as V11. These remain generation-only results. Lane D’s production source remains `8769061b`; test-only repair qualification is separate, and b09 remains a historical RED checkpoint.

## Frozen 140-shard upper-bound census returned — conditional evidence only

Controller `cf1d3fc9-6a88-4e12-8403-974717b1ed42` returned all **140 / 140** scheduler rows with exit 0, all on exclusive large boat workers. This was the frozen original production **`15eff72f04f74351b622b02d08e47bfb9dfdb131`**, original 34-law family, no supplied laws, no shared source-subset probes, 1e12 counted allowance and 1,800,000 ms per operation. It is not the current integration. Output: `runs/lane-i/upper-bound/resumed/full/`.

The existing tested summarizer reports **64 closed, 42 unknown, 34 censored, 0 certified SAT, 0 pending**, with no issues. Every closed shard has a successful **fresh-process ordinary kernel verifier receipt** for its conditional STEP proof. Certificates were checked on the workers; the logged certificate hashes do not constitute a new local replay or a whole-helper proof.

A separate provenance audit checks all 140 names/statuses/placements, all frozen `core/` and `kernel/` manifest-success lines, original-family/source/budget/operation metadata, reproducible disposable patch hashes, unmodified kernel patch scope and verifier linkage: **zero issues** in the initial local receipt pass. Audit qualification completed on boat as task `6f093de6-9b70-40f6-9991-0d13ee9d87e9`, batch `20261110-021230-byouia`, source `8fa5ac41` / snapshot `80054a195e34`: all **11 tests / 25 assertions passed**, all 140 provenance checks returned zero issues, and the full TypeScript/lint check had zero warnings/errors. The remote audit SHA-256 `45b12b3eb969a125b3e8e96ed5916e1d288222afca2b5c054012a58c268e8fc9` matches the retained local audit exactly. Only returned receipts plus tests/check were replayed; no proof shard was rerun. Both new audit test modules are also added to the canonical future validation and quick-suite rosters; the already completed V11 recipe remains unchanged.

| Target / counted pass | Closed operations per ceiling mode | Remaining per mode |
|---|---:|---|
| Inv* (`star`), pass 0 | 0 / 7 | 7 unknown |
| Inv*, pass 1 | 0 / 7 | 7 censored |
| Inv2973-half (`half`), pass 0 | 0 / 7 | 7 unknown |
| Inv2973-half, pass 1 | 0 / 7 | 7 censored |
| Inv1758 (`rows`), pass 0 | 7 / 7 | none |
| Inv1758, pass 1 | 5 / 7 | ops 1 and 4 censored |
| Generated p1, pass 0 | 0 / 7 | 7 unknown |
| Generated p1, pass 1 | 7 / 7 | none |
| Safety, pass 0 | 7 / 7 | none |
| Safety, pass 1 | 6 / 7 | op 4 censored |

**All 70 on/off pairs have the same terminal classification.** Removing local ceilings did not add a closed shard in this run. This is not a timing comparison across unlike CPUs, nor proof that any finite completion bound exists.

The 34 censored cases are **12 cooperative wall returns, 2 outer-watchdog stops, and 20 early SIGKILLs**. The early kills report about **13.5–14.2 GiB peak RSS**, consistent with resource exhaustion near the allocation; no kernel OOM log was collected, so they are not conclusively relabelled OOM. Their last observed work is only a lower bound. The 42 unknowns are unvalidated symbolic SAT hints, not certified counterexamples. No original safety proof, complete helper proof, or whole-family upper bound is claimed.

All 140 raw logs remain untouched; compressed copies, source-bound summaries, verifier hashes, CPU labels and raw/compressed checksums are retained in commit `8fa5ac41`. No large source copy was made. The finished census's `frozen.tar` KEEP-LOCAL pin is released for coordinator-managed, verified offload; no input was deleted. The pending audit consumes only small hard-linked identity/family/manifest inputs, not that source tar. The main/b09 source-pack pins remain active for the pending regression experiments. Future-roster validation completed as task `0607c587-4075-4e23-a017-aaf92f308db9`, batch `20261110-021325-wwijf7`, source `5813044f` / snapshot `e30c827a55b6`: all **3 propagation/coverage tests / 23 assertions passed**. It did not repeat any proof run.

## Diagnostic evidence audit / scheduler observation

The lint repair is verified below; its compressed logs, source identity, placement and raw/compressed SHA-256 receipts are retained in `runs/lane-i/v11-lint-repair/`. The original failing V11 check is preserved.

The bounded scheduler observation after that completion found the already registered strict batch with **16 left / 0 running** and targeted bar batch with **12 left / 0 running**. The pool was ready but reported a churn health breach. These are queued batches, not completed experiments or fresh failures. No submission was duplicated, cancelled or promoted through private scheduler state; shared settings remain untouched.

`research/lane-i/regressions/receipt-audit.ts` will reject wrong-source/CPU/budget records, missing/duplicate repeats, nonexclusive or non-boat placement, changed raw traces, and summaries/per-law work not supported by the compressed trace. CPU skips cannot count toward the ten-pair requirement. Auditor qualification completed in batch `20261110-020621-1wircq`, task `9fef5785-d2e2-4b27-9013-3f5ecaf2e89a`, source `2030894d` / snapshot `1549bf8553a1`: **six tests / 15 assertions passed**, and the full TypeScript/lint check reported **zero warnings or errors**. Fault injections cover changed source/CPU/budget, corrupted traces, fabricated semantic results and per-law work, missing/duplicate repeats, mixed skip/result records, and mismatched bar answers. This validates the auditor code, not any pending experiment or proof. Its compressed receipt and placement are retained under `runs/lane-i/regressions/audit-check/`.

## Original strict and bar reproductions returned — frozen b09 remains RED

Strict batch `20261110-015728-zs64hl` returned 15 same-9950X pairs plus 11 nonmatching-CPU skips. **14 pairs have complete semantic results**: 13 prove on both sides, while group 2/repeat 2 proves on baseline and returns unknown on b09. The fifteenth pair has a censored baseline and unknown candidate; it is retained, not silently discarded. Baseline totals are 14 proven/1 incomplete; candidate totals are 13 proven/2 unknown. The strict receipt audit correctly remains nonzero on that incomplete baseline.

On the 13 both-proven pairs, b09 uses exactly **18,135,054 solver work versus 14,498,189 (+25.1%)**, and **4,898,768 full work versus 2,665,853 (+83.8%)**. On all 14 complete pairs its generation is faster (median paired generation ratio 0.709), but median paired total time for both-proven cases is 0.992. Faster generation does not remove the proof-work regression or the observed lost verdict. Metrics: `runs/lane-i/regressions/strict-initial/`.

Bar batch `20261110-015931-92u7qg` also returned. One worker’s **1,537,375-byte stdout was cut to a 400,000-byte tail** by collection, hiding its three records. The complete gzip was recovered read-only from the original VM `bx_af3p9nak` and matches its remote SHA-256 (`b3408baa1a5d01deff999516f44ed88950f0e204ebeaf551901ae5023ac62fa8`), with no benchmark replay. All **36 paired records now pass source/trace/roster integrity checks**. Only **15 pairs completed both children**; those have no differing parsed answers. Across all 72 children there are **33 SIGKILLs, 7 timeouts and 32 zero exits**; 16 parsed answers came from incomplete children and are not accepted as completed benchmark results. No OS kill evidence was collected, so SIGKILL is not asserted to mean OOM. The bar is **not clean** and does not demonstrate no loss.

V11’s older-source generation census (`e48a109e`) returned all **87 pairs**: **84 unrelated pairs have identical canonical hashes**, and the three MLDR pairs consistently report 27 baseline versus 34 candidate laws with stable per-side hashes. Census receipt checks report zero issues. These are worker-generated digest comparisons, not an independent reconstruction of canonical arrays, proof success, or results for V12.

## Row-cache screening and guard hypothesis — completed

Batch `20261110-020658-ztqyee` completed all four workers / eight rotated triplets. The source/CPU/variant/trace-hash/raw-summary audit reports zero issues; all **24 child traces** were integrity checked, and all eight triplets retained identical generated-name lists. Detailed metrics are in `runs/lane-i/regressions/cache-probe/cache-summary.json`; the reproducible reader is `research/lane-i/regressions/cache-summary.ts`. Baseline: **6 proven, 2 incomplete SIGKILL processes**; standard b09: **7 proven, 1 unknown**; b09 with row sharing off: **2 proven, 6 unknown**. Six triplets were on Ryzen 9950X and two on EPYC 4585PX. These are screening data, not the ordinary ten-pair cohort or a no-loss gate. Disabling the row cache is **not** supported as a fix; it increased work/memory and degraded completion here.

The successful default-b09 runs consistently used 18,135,054 solver work / 4,898,768 full work versus baseline 14,498,189 / 2,665,853. A sampled complete pair attributed about 7.95 s to focused recovery, with three pass-0 SAT outcomes and seven count-completion proposals in another attempt. Its finite admission filter took about 370 ms, so generation/filter cost alone does not explain that added proof work. Labels in `counts: try` are truncated; they are not treated as unique full law IDs.

**Guard screening returned negative.** Batch `20261110-021813-xj8zgv` completed two exclusive EPYC workers / four triplets. All 12 runs returned proven, but there were **zero genuine-counterexample events**, and both default b09 and the prototype used exactly **18,135,054 solver work / 4,898,768 full work** in every completed trial. The guard did not fire or remove the focused cost. A raw-trace/patch/CPU/source audit reports zero issues; `runs/lane-i/regressions/refuted-guard/guard-summary.json` retains the results. **No guard was applied to production and no speedup is claimed.**

The latest scheduler observation still has 16 original strict workers and 12 original bar workers queued, none running. Its class totals were 662 queued gate jobs on 50 VMs versus 136 submission jobs on one VM. This is submission-class starvation, not a failed launch. No public per-batch priority command is exposed; shared scheduler policy and original submissions remain unchanged.

A **disposable, two-worker guard probe** (task `6ee4f30b-2f39-4213-9581-82c37a22de0f`, output `runs/lane-i/regressions/refuted-guard`) tests a specific smaller hypothesis: `withDeferredCountRecovery` currently runs recovery even after `ordinary.refuted === true`, an already validated genuine finite counterexample. The prototype adds only that short-circuit, returns the exact ordinary result, and changes no budget, law or kernel rule. Baseline, unmodified b09 and the labelled prototype are rotated twice on each worker under the original strict limit. Full-name finite-model events will show whether the guard actually fires. This is not a production edit and is not counted as ordinary strict coverage. If it does not help, it will not be claimed as a regression fix.

## Independent row-cache screening ablation — completed

While ordinary strict/bar batches remain queued, four small **gate-class screening workers** are being submitted for the specific generic-overhead hypothesis. Batch `20261110-020658-ztqyee`, task `c25cffca-2214-45f2-99f0-8b5fccfbf4a8`, snapshot `36997d7ff34a`, output `runs/lane-i/regressions/cache-probe`. On each machine they run baseline, unchanged b09, and b09 with the existing `GDP_ROWS_SHARED=0` cache switch, in rotated order, twice. They preserve the original 60 s wrapper / 60,000 ms proof limit and generated-law policy, and record cache hit/retention counters plus process memory. No production code or kernel rule is patched.

This is a distinct, labelled ablation, **not a resubmission or replacement of either queued batch, not a source fix, and not part of the required ordinary ten-pair 9950X cohort**. Other CPU models are allowed for screening and must remain labelled. Both the standard b09 and cache-off variants share the same CPU and reconstructed source. The earlier remote-reconstruction size notice applies; no new whole-tree archive is written on the laptop. A result can falsify the row-cache-overhead hypothesis; no performance conclusion is claimed before it returns.

## Coordinator red-gate diagnosis — active

Lane D reports `b09da82d` RED: `consensus_forall` repeat 3 was baseline proven at 44.711 s versus candidate unknown at 59.218 s on Ryzen 9950X, with identical generated lists; four CHC losses, two ITS-SCC losses and ITS/SCC/TIP error rows also need paired diagnosis. Both requested tracks are being prepared in parallel; existing V11 and frozen work stays active.

**Size notice before remote reconstruction:** each diagnosis worker will reconstruct both exact main/b09 Git-object snapshots on boat. Their source, Git objects and installed dependencies may exceed **500 MB combined per remote worker**. The laptop only reuses existing Lane D packs through `--data` and writes small drivers/receipts; no whole-tree archive or source pair is copied locally. Newly created remote temporary checkouts are removed by their owner after compressed traces/hashes are emitted.

Strict diagnosis: batch `20261110-015728-zs64hl`, task `438bba34-4a8c-430f-8ba6-d4fac07a8b7d`, source-tree receipt `05e9ea017ccc`; output `runs/lane-i/regressions/strict-initial`. Targeted bar diagnosis: batch `20261110-015931-92u7qg`, task `3d6b6d41-e453-4d8b-ac94-4afabcf6628b`, tree receipt `38de353d4f4c`; output `runs/lane-i/regressions/bar-initial`. Both registered once on boat, class submission, timing/exclusive mode. The twelve bar entries receive three paired repeats each; the original 60 s wrapper and solver margins are preserved, including pinned TIP Bun 1.4.4. Sources are always the exact main/b09 objects, not the newer lane tip. Full roster and drivers are under `research/lane-i/regressions/`. Results pending.

The strict batch rejects non-9950X CPUs before restoring sources, rather than counting them as matching repeats. Sixteen independent workers each attempt three alternating-order strict pairs on a matching CPU; CPU skips do not count toward the required minimum ten valid pairs. Instrumentation records generation wall, finite-pass profile, per-law attempt units/wall and compressed raw evidence without changing time/work budgets or proof policy. More qualifying workers will be submitted if fewer than ten pairs return.

Original bar error rows inspected: the ITS failures show SIGKILL (`code: -9`), and baseline `tree_Flatten3` explicitly reports `proveData threw: Out of memory`; the other TIP errors end after import/agreement. Hypothesis: some error rows are resource exhaustion rather than a new semantic exception. These remain genuine incomplete/error receipts, not excused successes. The targeted batch uses exclusive large workers with a 14,336 MB request; that changes resource headroom versus the original bar and must be reported, not mistaken for a source fix if an error disappears. Time/work limits and solver arguments remain original.

A separate falsifiable strict-regression hypothesis is generic prover overhead or changed model instantiation: between main and b09, `kernel/prove.ts`, `kernel/prover-rows.ts`, and arithmetic model-value proposals changed even when generated law lists did not. Phase/per-law evidence must distinguish that from generation time before any fix or ablation is credited.

## V11 returned: 690 tests pass, check failed, no MLDR proof

Batch `20261110-015357-ekhlb4` / controller `702a89c9-25de-445c-821b-4a1e2d20550c` finished in 130 s. All **124 changed modules** ran: **221 + 165 + 142 + 162 = 690 passing tests, zero failures, 22,002 assertions**. The original strict receipt auditor returns exit 1 with exactly `validation roster mismatch` (the extra negative-control worker) and `check: exit/backend/CPU placement` (the real check exit 1). No audit rule was relaxed. That rejected audit, source identity, original placement/status and nine integrity-checked compressed worker logs are retained under `runs/lane-i/v11/`; `validation-receipts.sha256` binds raw and compressed forms. The real replay negative control failed specifically with `readCount: 2`, `readsRetained: false` after the old reconstruction was restored, then emitted `CORE_REPLAY_NEGATIVE_CONTROL_OK`. Its expected failure is not counted as a test-suite failure or a new proof.

`check` failed on `typescript(no-implied-eval)` at the newly merged runtime-key test's `new Function`. Commit `ab131920` uses the existing `runInNewContext` helper instead; no production semantics changed. A fresh full check and runtime-key test pair are running on boat as task `1f713e51-f7ca-4bd2-b755-6742d0d208d4`, output `runs/lane-i/v11-lint-repair/results`, source-bound to `ab131920d8e5d67b9f6172ca5182bae8552da0ee`. That repair is now **validated**: batch `20261110-020048-e1u4gi` / source snapshot `cba531fadc55` returned zero TypeScript/lint warnings or errors, and all **five runtime-key tests passed**. Both workers were exclusively placed on boat. This closes the observed test-fixture check failure only; it does not repair or admit any failed strict/bar proof.

All three original MLDR pairs remain unknown on both sides. Candidate internal search times: **58,523 / 59,779 / 59,025 ms**; first says `not proven: one primary per term`, the other two `time (rule result)`. No MLDR proof or strict proof margin is claimed. The V11 generation census and frozen upper-bound run remain active and untouched.

## V11 submitted on the new integrated source

Source **`e48a109efc5ee029d658702ac45a7e7a8ff4c9b6`**:

- Nine validation jobs: `702a89c9-25de-445c-821b-4a1e2d20550c`, output `runs/lane-i/v11/validation`. Full check, four changed-test shards, three original MLDR pairs and the replay-metadata negative control.
- 87 generation pairs: `79f61a91-d29e-4ef4-b3c6-85c12e548666`, output `runs/lane-i/v11/census`.
- A baseline-to-candidate test-file roster comparison lists **124 changed modules, zero missing**. This is a coverage-list check, not a test verdict.
- Inputs reuse `/private/tmp/gdp-archives/.mounts/b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c/` by `--data`; per-run input contains only small identity metadata. No tree archive was created/copied, no existing submitted workload was duplicated/cancelled, and no file was deleted.

**Lane D: superseding source request is `e48a109e`.** The earlier `b09da82d` is a validated historical mechanics checkpoint, not admission for this integrated source. The pending V11 reports will preserve inner verdicts, CPU labels, canonical hashes and the intentional-failure control separately.

## New lane integration / V11 preparation

Pinned merges: A `5632e5e9` then `8dfb319e` (bounded native-clause splitting and default-off post-target pruning); B `e17ed54f` (bounded member/row-premise probes and stricter receipt tooling); E `5c3686f0` (member/range preservation and ranked-source experiments); Fable `b74b2f00` (compiled derived cells and shared dense-write breakpoints); F `0775159a` (guarded frame tests/source reconstruction probes).

Conflict decisions: kept the verified full-record core replay and its read/pool/certificate diagnostic rather than an explicit-field reconstruction; retained both range test sets; deduplicated the range import; retained both `runInNewContext` and `times` runtime-test imports; used the stricter frame-falsifier result union; kept the checked scalar/audit input guards; kept both partial-predicate cases. Lane reports remain at their pinned branch tips. Offload keep lists were combined, making F's external context path absolute.

The four newly added test modules (finite target pruning, row premises, range-input preparation, ranked-source installation) are added to both the validation and quick-suite roster assertions. The original replay negative control remains in the next validation. New behavior has **not yet been validated in this integrated source**; prior green mechanics and V9/V10 census results retain their original source bindings.

## V10 generation census completed; newer production tips require integration

Batch `20261110-004022-hzxjo7` (controller `1d5b236b-821e-47f1-8dba-db994bd90c31`; exact scheduler ID remains available in its controller receipt), candidate **`b37c4e2ce8172d0e3e1546b6c099ceff33b2d7ae`**, completed all 87 pairs. The same roster/source/phase/CPU/hash/repeat audit reports **zero issues**, **84 canonical-identical pairs across 28 non-MLDR protocols**, MLDR consistently **27 → 34**, and no count decreases. **Every baseline and candidate canonical hash matches V9**, including MLDR, despite the intervening finite-generator change. This is repeatable generation evidence, not an MLDR proof or a final gate.

MLDR paired generation wall ms: r1 EPYC 4585PX **51,560.946 → 13,137.081**; r2 Ryzen 9950X **38,678.107 → 13,736.742**; r3 Ryzen 9950X **48,685.612 → 17,318.256**. Full CPU-labelled metrics, 87 compressed logs, and 174 raw/compressed hashes are retained under `runs/lane-i/v10`.

A fresh lane-ref check found newer **production** changes (A finite-predicate batching, E member/range preservation, and Fable compiled runtime/count changes), not just report updates. These require source review/integration and fresh validation; the clean `b09da82d` mechanics/negative control must not be transferred silently. No redundant final census has been launched before that integration.

## V9 generation census completed: 28 unchanged protocols, MLDR 27 → 34

Batch `20261110-001623-9q08uz`, source **`edd284913024a6566591d7ad1cba8059b8047a14`**, completed all **87** generation pairs (29 protocols × 3 repeats), with zero worker failures. Audited every job for exact roster, a single comparison record, both side boundaries, source identity, exclusive CPU-labelled placement, valid canonical hashes/counts, and stable hashes across the three repeats: **zero issues**.

- **84/87 pairs are canonically identical** between baseline and candidate: all three repeats of each of the 28 non-MLDR protocols.
- MLDR alone changes, consistently **27 → 34** generated laws. Baseline canonical SHA-256: `182e714c9c0384d3113f03bbbafba40ec5f19f7c19b2d00377c1d4ef4b567329`; candidate: `dd495ab653ff4376b1c7b8c462c7dfafbcf9b3f5fc27949b8d61543ad5c69563`.
- **No candidate count decreases.** Count growth by itself is not proof of set inclusion or proof success; the changed MLDR family is not labelled identical.
- MLDR measured generation wall (baseline → candidate ms): r1 **26,365.565 → 15,211.453**, r2 **43,215.176 → 18,587.650**, r3 **32,818.075 → 14,585.282**. CPU strata and all per-protocol paired timings are in `census-summary.json`; no full-run proof-speedup claim follows.

Evidence: `runs/lane-i/v9/census-summary.json`, original 87-row status/placement, and 87 integrity-checked compressed logs. `census-receipts.sha256` binds both the raw and compressed forms (174 hashes). Guest comparisons require zero proof queries; full raw canonical payloads are not in the returned logs, so their hash comparison remains guest-produced evidence, not a new local reconstruction.

**Scope caveat:** this is the completed **v9** census, not automatic admission for current `b09da82d`. Production `core/finite-tiny.ts` changed after v9; the already-submitted v10 census remains pending, as does the frozen upper-bound run and Lane D's independent gate. No census was duplicated or cancelled.

## Final-candidate validation completed / Lane D evidence

Batch `20261110-005805-lfrigx`, task `7988c131-e6e5-4fb3-8a6e-9143d69bd124`, source `b09da82d`, completed all nine jobs with zero worker failures. `check`: **0 warnings, 0 errors**. Changed-test shards: **216 + 148 + 136 + 160 = 660 passing tests, 19,846 assertions, no failures**, across 120 changed test modules. The new real core-replay regression passed and independently checked each returned certificate.

The negative-control worker restored the old metadata-dropping reconstruction in its disposable checkout. The selected regression then failed specifically with `readCount: 2`, `readsRetained: false`; the control verified that expected failure and returned `CORE_REPLAY_NEGATIVE_CONTROL_OK`, then restored its source. This demonstrates sensitivity to the original lost-read defect, rather than merely exercising a passing branch. The hook also compares pool/certificate identity; this fixture does not claim exhaustive nonempty-pool coverage.

The strict standard auditor first **correctly rejected the nine-job roster** (`validation roster mismatch`): it expects exactly the usual eight jobs, not the extra intentional-failure control. Its failed audit remains intact at `validation-audit.json`. No auditor rule was weakened. `standard/projection.json` records original summary/placement/control-log hashes, the eight retained jobs, and the separately validated ninth job; its log views are hard links, not copies. The standard eight-job projection then audited with **zero issues / exit 0**. That means valid receipts, not an MLDR proof or gate approval.

| Pair / CPU | Baseline pre-attempt wall ms | Candidate pre-attempt wall ms | Candidate search ms | Candidate result |
|---|---:|---:|---:|---|
| r1 Ryzen 9 9950X | 24,379.598 | 14,181.221 | 59,115 | unknown / time (rule result) |
| r2 Ryzen 9 9950X | 19,053.609 | 12,259.359 | 59,001 | unknown / time (rule result) |
| r3 EPYC 4585PX | 22,446.553 | 13,132.418 | 59,005 | unknown / time (rule result) |

All three baselines were also unknown (`not proven: one primary per term`). Candidate trace-kept count was 16 each; safety was never reached. No MLDR proof, family success, or full-run speedup is claimed.

**Lane D:** the exact source identity is `runs/lane-i/final-candidate/input/identity.json`; full nine-job receipts and compressed logs are in `validation/`, and the source/hash-bound standard audit is in `standard/`. This supersedes the pending-validation portion of the request below, not its review requirement. Frozen upper-bound and generation-census work remains outstanding. No blanket/final gate green is declared.

## Repair3 clean; final candidate / Lane D gate request

Batch `20261110-005456-jpu4hp`, source `50b3dc68`, completed all five jobs successfully on Ryzen 9 9950X. `bun run check` reports zero warnings/errors; all **659 tests and 19,840 assertions passed**, across all 120 changed test modules. This closes the observed TypeScript, fixture-scope, lint, and test-roster failures for that source. Compressed logs and status/CPU/hash receipts are under `runs/lane-i/repair3`.

The guarded replay probe then found a real ordinary count attempt that reaches core refutation and returns independently checked certificates. `b09da82d` turns that fixture into an end-to-end regression in `core/count-ranges.test.ts`. A diagnostic emitted only on the existing `countsDump` hook checks reference preservation of the full read set, pool and selected certificate across the actual core-rebuild branch; the test also independently checks every returned certificate. The disposable-worker negative control restores the old metadata-dropping record shape and must fail this exact regression for the lost-read diagnostic. No kernel rule, supplied law, work share, deadline or proof acceptance policy changed.

**Lane D final gate request: inspect `b09da82d` / exact full SHA in `runs/lane-i/final-candidate/input/identity.json`.** Nine jobs are submitted as task `7988c131-e6e5-4fb3-8a6e-9143d69bd124`: full check, all four changed-test shards, three original MLDR repeats, and the old-shape negative control. Output: `runs/lane-i/final-candidate/validation`. Fresh results and the negative-control sensitivity remain pending, so the new replay coverage is not yet declared validated. Existing frozen upper-bound and generation census batches are untouched and still require their own results. No MLDR proof or no-loss gate is claimed.

## Repair2 completed: all changed tests pass; final fixture lint remains

Batch `20261110-005238-i4t0hb`, source `90f6676aa0697a91bdc1a845d9edd9b0d645b597`, completed. All four changed-test workers passed: **215 + 148 + 136 + 160 = 659 tests, 19,840 assertions, zero failures**, covering all 120 changed test modules. This includes the previously failing finite-polarity test and both newly rostered audit/archive modules.

`check` still exited 1: TypeScript passed and lint reached four diagnostics at one new fixture line, where `request.left/right` were interpolated without narrowing their possible map/undefined type. `50b3dc68` now explicitly rejects non-number fields and only formats narrowed scalars; no production engine change. A full five-worker check/test rerun is task `3b811587-1fef-4d5a-8caa-ced0da232f71`, `runs/lane-i/repair3/results`, using the same canonical archive cache and existing `research/lane-i/repair2.jobs.json` recipe. Result pending. Repair2 compressed receipts and hashes are retained; passing tests do not override the failed check.

## V10 completed: new check/test defects, no MLDR proof

Batch `20261110-004025-7qwhgq`, candidate `b37c4e2ce8172d0e3e1546b6c099ceff33b2d7ae`, completed: check exit **2**, changed-tests-2 exit **1**, all other workers exit 0. The audit correctly returns nonzero. Check stopped at a TypeScript narrowing error in `research/track-m/link-lane-b-focus-audits.ts`; the finite-polarity test inherited an unused count binder `a` that collided with its scalar `a` when the independent interpreter checked scope. Neither is a production proof-engine change.

V10 tests: shard 1 **210 pass**, shard 2 **143 pass / 1 fail**, shard 3 **136 pass**, shard 4 **160 pass** (649 passed / 1 failed overall, 19,790 assertions). Do not label the failing shard or whole suite green.

All three original MLDR candidate runs again returned **unknown / time (rule result)**: 59,017 / 59,076 / 59,254 ms, 16 trace-kept candidates each, safety never reached. Baseline returned unknown (`not proven: one primary per term`) in all three. All three pair guests report Ryzen 9 9950X; candidate pre-attempt wall was 12,444.703 / 17,626.867 / 19,377.932 ms, baseline 22,698.158 / 28,124.501 / 27,471.780 ms. No proof win is claimed. Source-bound audit, CPU placement, statuses, compressed logs and hashes are retained under `runs/lane-i/v10`.

The first lint-repair batch `20261110-004916-komoui` likewise completed with the v10 TypeScript and finite-fixture failures; its new unsupported-bound regression passed in shard 1 (211 passing there). It did not establish a clean check. Receipts are retained under `runs/lane-i/lint-repair/results`.

### Repair2 and coverage

`90f6676a` gives the unused test count a non-colliding binder and makes the existing input-name assertion narrow correctly. A source-roster comparison found two omitted changed test files (`research/mldr-incl/pack-production.test.ts` and `research/track-m/link-lane-b-focus-audits.test.ts`); both are now in validation and the quick-suite roster regression. **All 120 test modules changed since baseline are listed; this is a roster fact, not a test result.**

Five new check/changed-test jobs for that source are task `d7d2f018-6b20-4ddc-ba8f-b4fe7ccd470a`, `runs/lane-i/repair2/results`; existing jobs were not resubmitted. They reuse the same hard-linked archive cache view and a metadata-only input directory. Pending, not passed. No new MLDR performance claim is attached to these mechanics-only repairs.

## V9 completed: tests green, check red, no MLDR proof

Batch `20261110-001619-awzeif` completed all eight jobs. The controller exited zero but `check` exited **1**; the conservative receipt audit also correctly exits **1**. TypeScript reached the subsequent lint phase; lint found four redundant quote escapes in `research/mldr-incl/install-targeted-completion.ts` and an exhaustive-switch requirement in `core/count-ranges.ts`.

Four changed-test shards passed: **203 + 142 + 136 + 160 = 641 tests, 19,762 assertions, no failures**. These counts include the then-rostered focused source tests, not the unsupported-bound regression added afterward.

All three MLDR pairs were normal returned results, **unknown on both sides**, with no independently checked MLDR proof. Candidate used 34 generated laws versus 27 baseline. Candidate trace-kept counts were 18/16/16, not successful final families. Candidate returned `time (rule result)` at 59,033 / 59,066 / 59,016 ms.

| Repeat / CPU | Baseline pre-attempt wall ms | Candidate pre-attempt wall ms | Candidate trace-kept | Candidate safety attempted |
|---|---:|---:|---:|---|
| r1 Ryzen 9 9950X | 18,421.151 | 11,900.413 | 18 | yes; unknown |
| r2 EPYC 9455 | 21,078.238 | 13,631.399 | 16 | no |
| r3 Ryzen 9 9950X | 41,471.579 | 24,473.019 | 16 | no |

The helper obligations remain unresolved: `canVote/3` pass 1 consumed 3078 units each; `disabled/0` consumed 3054/3054/2058; CV/CfgT row agreement consumed 2997/1219 in r1/r2 pass 1 and was not reached in r3. R1 safety consumed only 48 pass-0 units then 0 pass-1 units, both unknown. Thus faster candidate generation is **not** a proof win or a whole-run performance claim; scheduling/CPU variability is explicit in receipts.

`runs/lane-i/v9/validation-audit.json` preserves the source-bound parsed evidence. Compressed logs, `summary.tsv`, CPU `placement.json`, and `compressed-receipts.sha256` are retained. Raw logs remain until the coordinator approves cleanup/offload.

### Confirmed lint repair and focused rerun

`5abc2ddf` removes only redundant quote escapes and replaces the default unsupported-bound branch with the explicit identical-return expression cases. The new test checks that map/conditional bounds remain unknown rather than gaining unsupported evaluation. Five fresh check/changed-test jobs are submitted as task `c2647ee8-0869-43f6-b868-848c3c92677b`, output `runs/lane-i/lint-repair/results`. No archive was recreated/copied: `--data` uses a hard-linked baseline cache view, with only a small source identity in the run's input directory. Pending, not passed. Existing v10/census/upper-bound workloads remain untouched.

The separate receipt-audit batch completed too: **12 tests, 28 assertions passed**, then the same five lint errors caused its check job to fail. Its historical-v8 audit correctly rejected v8's failed check (expected nonzero audit verdict); the wrapper's exit zero does not make v8 green.

## Disk

Coordinator disk rules are active: no new per-run whole-tree archives; one reusable `/private/tmp/gdp-archives/<sha>.tar`; no deletion without the coordinator's decision; record any planned write over 500 MB before doing it. Retrieve compact summaries/receipts/hashes; retrieve raw traces only for a concrete question and compressed. Existing submitted controllers and their input paths are left intact.

Created **hard links, not archive copies**, from retained archives into the shared cache (no new archive data blocks):

| Source SHA / canonical path under `/private/tmp/gdp-archives/` | Bytes | SHA-256 |
|---|---:|---|
| `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c.tar` | 30,167,040 | `c593e659eb2d22592f82ab291a63a057679eaf11e8086ed0eed5a972c57745fe` |
| `d47141cce2caf5b86b0c2c0c372a5174f424bc15.tar` (handwired) | 32,501,760 | `73d44548dbe109a40ac933406324e17d7dee39e7dff1a6f1270ed030c31c1da4` |
| `0b6ebeeec827b05210f3acfa4149a70dda9a0de5.tar` (gdp-ts) | 665,600 | `75d367da15decb1fefce2ae72ae50e7f3f737989094a760fde643c5b1f5c1496` |
| `15eff72f04f74351b622b02d08e47bfb9dfdb131.tar` (frozen census source) | 234,588,160 | `7d697a87edba36cc65a6ca33e4998fe67e677c6a5fe02617a759fc9df25252b5` |

**Deletion candidates for coordinator approval only; nothing deleted:**

- `runs/lane-i/v1/input/{main,handwired,gdp-ts}.tar` through `runs/lane-i/v8/input/{main,handwired,gdp-ts}.tar`: eight historical sets, **506,675,200 bytes total (~483.2 MiB)**. Each set is 63,334,400 bytes; current Lane I controllers use v9/v10 or resumed-upper input, not these archives. Baseline/vendor identities are preserved in the shared cache and committed manifests. Retain the small identities, manifests and receipts.
- `runs/lane-i/upper-bound/input/{main,handwired,gdp-ts}.tar`: **63,334,400 bytes (~60.4 MiB)**, old smoke/capture packaging; resumed full census uses `upper-bound/resumed/input`. Same retained baseline/vendor archive hashes. Keep its `family.json` and `source.sha256`.
- **Do not remove active inputs** `runs/lane-i/v9/input`, `runs/lane-i/v10/input`, or `runs/lane-i/upper-bound/resumed/input` while their registered controllers may still read them. Their hard-linked cache names are not additional copies and removing only one alias would not reclaim its blocks.

### Coordinator offload plan

The coordinator may archive eligible old files to boat snapshot `gdp-wired-offload-20261110`, verify them there, then free their local copies with `.offloaded.json` hash/pull receipts. No local removal was performed by Lane I. Historical duplicate tar candidates above may follow that process; compact manifests, audits, compressed receipts and hashes remain local.

Added the canonical baseline/vendor/frozen archive names and their hard-linked mount aliases to `/private/tmp/gdp-archives/KEEP-LOCAL.txt`, preserving the other lane's existing entries. `runs/KEEP-LOCAL.txt` protects the exact live frozen-source input. The cache view exists because current `--data` accepts **directories only** and ignores symlinks: `/private/tmp/gdp-archives/.mounts/b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c/` contains hard links to canonical tar inodes, not copied data. No archive sits in the new run's input/output directories.

Additional optional cleanup candidates after approval: uncompressed v9 validation logs (147,729 bytes total; all eight have retained `.gz` versions and hashes), and `runs/lane-i/v9/validation-audit-output.json` (116,897 bytes; duplicate of the retained audit JSON). Nothing over 500 MB was written.

### Real replay regression discovery

Lane D correctly notes that the small `all`-versus-selected regression does not itself run the production core-cut path. Started one focused ordinary-attempt diagnostic (`research/lane-i/core-replay-probe.ts`, task `d8f871e2-a9db-4599-a57d-381205795954`, `runs/lane-i/core-replay-probe/results`) to find a deterministic core-refutation fixture and independently check its actual certificate. This does not modify the engine or use supplied protocol laws. Completed on Ryzen 9950X in 2.3 guest seconds. None of the three fixtures returned a proof; `upper` reached `decision:refuted`, while `frame`/`equal` stopped at finite-model handling. This is a **discovery miss**, not a passing regression or independently checked proof. The end-to-end replay coverage gap remains open. A second ordinary probe (`research/lane-i/core-replay-guarded-probe.ts`, task `f9b71da7-c418-4a24-8f66-32e515e08af1`, output `runs/lane-i/core-replay-guarded-probe/results`) gives the initial obligation a trivial disjunct, testing the hypothesis that the first fixture stopped at initial-goal proof growth rather than step replay. It completed on Ryzen 9950X in 1.42 guest seconds: guarded `upper` reached `decision:refuted`, returned a proof, and independently checked every certificate; guarded `frame` remained unproved. This is a successful tiny synthetic fixture, **not an MLDR proof**. Its actual replay regression and metadata-dropping negative control are now in the final-candidate validation above.

## Admission recovered; one-subagent cap remains

Coordinator reports the shared blob-cache lock freed at 00:35 and normal wide boat submissions are open again. Verified **all four original Lane I batch IDs are now persisted in the scheduler queue**: `20261110-001227-5qxos1` (140 shards), `20261110-001619-awzeif` (validation), `20261110-001623-9q08uz` (generation census), `20261110-001947-ek072a` (receipt audits). Their existing controllers remain owners. Nothing was killed or resubmitted, and no duplicate run was created.

Integrated A `19ad4ab4`: the atom-readiness shortcut and two finite-domain equivalence tests remain confined to the experimental tiny backend; original generation still does not invoke it. New witness-replay diagnostics distinguish newly found from historical drops. Only the report conflicted; Lane I keeps pointers to A's report. V9 remains bound to its older source SHA; new mechanics are required for this source update.

### Subsequent resumed lane merges

Refreshed E to `84a7a672`, B to `432bbc37`, and Fable to `c40acb07`; F remains `27ca886f`. Their report conflicts retain Lane I text with these pointers. E's duplicate-import removal auto-merged, but post-merge inspection found the integration had separate `rangeInstances` and `rangeViolations` imports rather than E's duplicate combined imports. Fixed the resulting missing constructor by consolidating both symbols into one canonical import; neither range construction nor violation detection is removed. A new current-source check will verify the fix. V9's shipped source is unchanged.

### Report-only admission refresh

Merged A `81f19fdb`, E `ab869755`, and Fable `72c6acc3`: report/admission/disk evidence only, no production or test changes. Kept Lane I report and pointers to each branch's `runs/REPORT.md`; E's `research/mldr-incl/WORKING.md` update is retained. B remains `432bbc37`, F `27ca886f`. V10's source binding remains valid; no duplicate validation was submitted for these documentation-only merges.

The five-minute observation of the already-registered receipt-audit controller expired without a worker result. That is **only an observation timeout**: the controller remains active and its two-job batch is not failed or resubmitted. All awaited evidence remains pending.

### V10 source-bound submission / for lane D

Candidate **`b37c4e2ce8172d0e3e1546b6c099ceff33b2d7ae`**, unchanged baseline **`b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`**. This includes A's inactive tiny-atom optimization, the canonical range import repair `2e8e3bbb`, and explicit inclusion of the new receipt-audit regressions in the quick/changed-test rosters. Fresh identity and archive checksums are under `runs/lane-i/v10/input`.

- Validation task `aec69c1d-36a6-4209-bcbc-98cf8b755111`, output `runs/lane-i/v10/validation`.
- Generation task `1d5b236b-821e-47f1-8dba-db994bd90c31`, output `runs/lane-i/v10/census`.

These are new-source runs, not retries or replacements of registered v9 batches. All run strict `--timing --vm-type large` through the scheduler. The upper-bound experiment stays frozen on `15eff72f` and is not rebound. All outcomes pending.

**For lane D:** this supersedes the current-candidate request for `edd28491`; bind the next final gate to **`b37c4e2c` vs `b788e195`**. Historical gates and v9 receipts stay with their own SHAs. No result or green claim is transferred across the source change.

## Coordinator memory-pressure guidance (historical; submission hold lifted, memory cap retained)

The coordinator confirmed that laptop memory pressure (7.5/8 GB swap and heavy paging) is stalling shared blob-cache admission while a client's per-file `utime` crawls. This supersedes the unconfirmed contention hypothesis below; it is not a proof-engine failure. All four existing Lane I controllers remain untouched: no resubmission, no cancellation, no scheduler/cache changes.

Until the coordinator lifts this instruction: at most one subagent, close idle/finished subagents, and no new parallel local work. Lane I has started no subagents and has none to close. Continue only lightweight sequential file review/edits and observation of the already-submitted jobs. Their receipts remain pending.

## Resumed integration ledger

All current committed heads integrated: A `bef4020f`, B `30537f70`, E `b3f8377e`, F `27ca886f`, Fable `a6ae4be9`. Lane-local evidence stays at each branch's `runs/REPORT.md`.

- A's optional finite-value domains, bounded compiled clauses, and round limits remain confined to the experimental tiny backend; production still uses the original finite path. Its source merge was clean.
- B/E/F have no new core/kernel/script deltas beyond already-integrated work. Their checkpoint/research receipts were retained.
- Fable's `a19a0713` import repair agrees with the integration's existing canonical `kernel/model-sequence.ts` import. Retained the unused-import repair and new narrowed-range test. Its only source conflict was a blank line between the existing recursive `lawReads` helper and A's tiny wrapper; preserved both implementations and the blank line. No side's behavior was dropped.
- All `runs/REPORT.md` conflicts keep this Lane I report with the branch pointers above; their text is not copied here.
- `e594a8f8` preserves core-replay `all`, certificates and pool metadata. The new v9 run, not old v7/v8 receipts, will validate the combined tree.

### Resumed validation submission and convergent B range merge

V9 is submitted on **`edd284913024a6566591d7ad1cba8059b8047a14`** versus baseline **`b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`**. Eight validation jobs: task `35d1dcd8-5feb-4788-b662-795cd19d2016`, output `runs/lane-i/v9/validation`. All 87 generation pairs: task `0f17f2ed-023e-46db-aaa5-01bde628c16d`, output `runs/lane-i/v9/census`. Both use fresh `runs/lane-i/v9/input` identities and retained baseline/vendor archives. All remain pending until audited.

B then advanced to `b056c3b4`. Reviewed every production hunk: its demand-driven range function, three full-read return sites, both model-loop rebuild triggers, and replay read preservation are already present here. Conflicts resolved to the existing equivalent implementation, retaining E's member premise/independence checks, I's replay spread, and I's additional narrowed-read regression. B's repeated range-demand assertions already exist here; no assertion was dropped. New B research comparison scripts are retained. This merge changes no core/kernel/test bytes relative to v9's candidate.

### For lane B

Your `b056c3b4` range port converges with v9's `edd28491`. I kept the integration's equivalent implementation plus E's member handling and the replay spread repair `e594a8f8`. Fresh combined v9 runs are in progress; no old gate result has been transferred.

### For lane D — superseding the historical candidate request

The current production/test candidate is **`edd284913024a6566591d7ad1cba8059b8047a14`** against **`b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`**. Please bind a fresh exact-roster, both-SHA-bound, CPU-labelled final gate to these SHAs when your cancelled first gate completes. It includes the core-replay metadata repair and all checkpoint lane tips. The later B merge is production/test-byte-identical. V9 local iteration checks are submitted, not yet green; only your complete receipt can authorize a gate claim.

### Receipt audit and admission observation

Added `research/lane-i/validation-audit.ts` and regressions: process exit zero without exactly one semantic result is not a pass; duplicate/malformed phases fail; original-harness unknown stays unknown; test-load errors cannot be called clean; measured pre-attempt wall is reconstructed from timestamps, never from the counted `candidates at` clock. Upper aggregation now refuses duplicate terminal records, unknown status labels and a `closed` label without both worker and independent checks.

Boat audit/check batch task `479c40a4-0c9e-4cea-af27-6dc356346d61` uses `research/lane-i/resume-audit.jobs.json`, output `runs/lane-i/resume-audit/results`. It also semantically audits the retained v8 logs, expecting the recorded failed check; a missing audit artifact cannot satisfy that expectation. New auditor tests/check are pending, not reported as passed.

Admission observation at 2026-11-09 17:22 UTC: all four owned controllers remain alive, but their output directories are empty and no corresponding persisted scheduler queue JSON exists yet. They have descriptors open on the shared `scheduler/blob-cache.lock`; scheduler PID `44811` also has three descriptors there. This is evidence of a shared admission stall, not evidence that the 140 searches or validation jobs ran. No other client's process, scheduler, cache, VM or lock was stopped, removed or changed. Keep the existing owners; do not duplicate-submit or silently transfer a result. The hypothesis is cache-lock contention before admission, not a measured code failure.

## Archived paused checkpoint (superseded by the explicit resume above)

**Branch:** `claude/mldr-integ`. **Last source/test SHA:** `a3930f448d4a7e447cb4d9470a4ec34a5d09e5b3`. **WIP/evidence checkpoint SHA:** `b5ed324525e8e88ad7386fa746f1ed41dad95536` (this RESUME is the subsequent documentation-only commit; obtain its final SHA with `git rev-parse HEAD`). Baseline remains `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`. No push. The pending merge of Fable `f8206bfc` was **aborted**, not completed. No merge is in progress.

## Proven/measured so far

- **NOT GATE GREEN.** No full MLDR proof and no Lane D final receipt. V7 is the last fully audited integration cycle: clean type/lint check; **621 tests / 19,688 assertions**; all **87 generation pairs** successful, with **84 non-MLDR pairs byte-identical**. Three strict MLDR runs are **unknown**, at **59.012 / 59.018 / 59.147 s**. These are generation comparisons, not a replacement for the full proof-verdict roster.
- V8's four changed-test shards completed with exit 0 before cancellation. The actual `core/count-ranges.test.ts` loaded and all four tests passed. All three new test-load propagation tests passed: a real missing-export error cannot be masked by a passing file, and the quick-suite driver propagates failure and stops. Their receipts are committed under `runs/lane-i/v8/validation/`.
- V8's check **failed**: `core/counts.ts(931,11) TS2322`, a rebuilt replay object lacks required `all: MapRead[]`. Three paired strict-MLDR commands produced logs and exit 0, but their verdicts have **not yet been semantically aggregated/audited**; process success is not proof.
- Upper-bound implementation/smoke receipts exist, but the requested **140-shard full census has no usable collected results**. Do not infer a closure or a counted-work bound from a cancelled job without a receipt.

## Cancelled / stopped owned work

All three active tasks were stopped by exact task ID and joined as `killed`. Final task inventory: **zero active owned tasks**. Shared scheduler/other clients were not stopped.

| Task ID | Batch; output directory | Purpose; partial usability / rerun |
|---|---|---|
| `c87cb42c-4236-4aec-af04-02ebf100a772` | `20261109-153811-6qofjx`; `runs/lane-i/upper-bound/full` | 140 original-34 upper-bound shards, frozen production `15eff72f`. Output directory empty. No usable partial result; rerun all 140 after explicit resume and source binding. |
| `381ed372-6c96-4727-9a1b-2a4ac8336fcf` | `20261109-155412-uekwu6`; `runs/lane-i/v8/validation` | Eight validation jobs. All individual logs/summary collected: four test passes, one check failure, three unaudited MLDR command results. Usable only as those individual receipts; rerun full validation after repairing the source. |
| `6a287b13-8a11-4483-87ac-88d5e5279fd8` | `20261109-155416-jnnc4s`; `runs/lane-i/v8/census` | 87 generation comparisons. Output directory empty; no usable partial results; rerun all 87. |
| `2092fac9-ec85-42a5-8f13-ffc3567c8625` | no boat batch | Lane-tip watcher already exited 0 before checkpoint. No active watcher remains. |

Cancellation metadata: `runs/lane-i/checkpoint/cancelled-tasks.json`. Small collected receipts are committed; large outputs, archives and tar snapshots stay out of git and remain local. Their paths/sizes are in `runs/lane-i/checkpoint/local-artifacts.txt`; preserve the workspace's `runs/lane-i/` (about 549 MiB before checkpoint). More detail: `runs/lane-i/checkpoint/README.md`.

## Open audit blockers and exact next steps — only after explicit resume

1. Read this RESUME and checkpoint README; verify branch/HEAD and a clean worktree. Re-read `supercomputer --skill`. Do not resurrect cancelled tasks or overwrite old output directories.
2. Repair `core/counts.ts` around line 931: preserve the required complete-read list (`all`) when the model-replay branch rebuilds certificate objects. Preserve the E member-witness independence checks, B completion retries, F compensated-frame cap, and Fable demand-driven range rebuilding. Add/check a focused regression; commit normally, never amend or reset history.
3. Reconcile Fable `f8206bfc` / canonical import fix `a19a0713` after resume permission. The integrated import is already correct (`../kernel/model-sequence.ts`, since `704efc27`); do not reintroduce the old import from `kernel/prove.ts`. The quick roster must continue explicitly including range/member tests. Fable's own 29/29 matching verdict report is not proof about the newer combined tree.
4. Create **new** `runs/lane-i/v9/input/` with the retained v8 baseline/vendor tarballs and checksums; repin `identity.json` to the newly committed candidate SHA, unchanged baseline and exact lane heads. Then run:
   - `supercomputer run --jobs research/lane-i/validate.jobs.json --out runs/lane-i/v9/validation --class gate --timing --vm-type large --data runs/lane-i/v9/input:integ-input`
   - `supercomputer run --jobs research/lane-i/census.jobs.json --out runs/lane-i/v9/census --class submission --timing --vm-type large --data runs/lane-i/v9/input:integ-input`
   Keep one owner/waiter per batch. Collect and audit every result, including test-load errors, MLDR verdicts and actual pre-attempt wall; do not accept only process exit status.
5. Resume the upper-bound request through `research/lane-i/upper-bound/README.md`. The retained jobs/input manifest is bound to frozen source `15eff72f`, **not** the current source. Reproduce that source in a disposable tree with retained tooling, or explicitly recapture/rebind the repaired source and label a new experiment. Never relabel old inputs. Submit all 140 helper/op/pass/ceiling-on/off shards in parallel with a fresh output directory. Require the original 34-law family, no supplied laws, independent verification, and conservative unknown/censored reporting.
6. Restart lane monitoring only when resumed. Refresh force-added `runs/REPORT.md` as lanes move. Request Lane D's exact-roster, both-SHA-bound, CPU-labelled final gate on the final candidate; no green claim or merge to main without it.

---

# Lane I — continuous MLDR integration

NOT GATE GREEN. Baseline `main` = `b788e195`; branch `claude/mldr-integ`.

Read COMMON.md, MLDR-DESIGN.md Sections 14–16 (including the answered 16.3 audit), and all MLDR-29.md rules, Speed, Gate evidence and Merging. Only Lane D's SHA-bound final receipt can authorize GATE GREEN. No push or merge into main is authorized here.

## Current status

V7 completed with clean check, 621 tests / 19,688 assertions, and all 87 generation pairs successful (84 non-MLDR pairs byte-identical); strict MLDR remains unknown 3/3. New E declaration-backed member premises and Fable demand-driven ranges are integrated and require v8 validation. Separately, the coordinator's 140-shard upper-bound research census is submitted on frozen production `15eff72f`, original 34-law family, no supplied laws; results are pending and will not be transferred to newer production. No Lane D final green receipt exists. The baseline is unchanged; no history was rewritten.

## Plan and falsifiable hypothesis

Combine every committed lane tip without dropping either side of conflicts. Hypothesis: preserving A's finite-model certification and attempt deadlines, B's completion/leaf budgets, E's lazy inclusions, Fable's generation-wall reductions, and F's demanded row splits produces a type-correct integrated engine without changing the other 28 generation lists. Falsifiers: failed checks/tests, changed unrelated candidate lists, missing helper attempts, uncapped attempts, or same-VM regressions. All substantive runs use `supercomputer`; strict verdicts use `--timing --vm-type large`, one job per repeat. No supplied laws count toward the finish line.

## Input ledger

- A: `claude/mldr-gen` at `00a0cbc1`.
- B: `claude/track-mldr` at `715ffd78` (advanced during initial inspection).
- E: `claude/mldr-incl` at `79d094f5`.
- Fable wall: `claude/mldr-wall` at `800b824f`.
- F: `claude/mldr-leaves` at `78eedf50`.

Lane-local reports remain in each lane's `runs/REPORT.md`; this report keeps pointers, not copies. Source histories and both sides of each conflict are reviewed before resolution. Raw logs and archives stay ignored.

## Execution ledger

- Initial worktree clean at baseline. Scheduler skill read; no local tests or builds.
- A `00a0cbc1`: source merged cleanly. Only `runs/REPORT.md` conflicted (add/add); retained Lane I report with the pointer above. No checked integrated result yet.

- B `715ffd78`: retained A's finite certification and shared `attemptEnd` deadlines, added B's count-law completion import and pre-SAT completion retry (both conflicting hunks were additions on B). Shard roster includes `count-completion.test.ts` and B's field-demand tests. Retained A's newer T16 audit repair evidence and T13 generation/census fixes (existential caller handling, exact 29-roster validation, optional repeat-2 receipt); B carried older copies without those fixes. Lane-local report remains a pointer.

- E `79d094f5`: production inclusion changes merged without a source conflict; B already contains its cherry-picked inclusion/upper-bound implementation. Retained Lane I report, pointing to E's original report and replay evidence.

- Fable wall advanced to `1dd0f1bb` during inspection (includes `800b824f`). Three `core/finite-houdini.ts` conflicts combined explicitly: retain A's 2 s local wall, targeting, cancellation and `onFinish` options; add Fable's recursive count dependencies and unchanged-read skip; sort the full family INCLUDING A's parameter precondition and declared facts; seed boundary/base/random states in round zero and record rejected boundary states for Fable's later-round revival. A's unsupported-sums guard survives. Faster runtime keys, own-property audit fix, lazy step-count calculation and hashed BFS merged cleanly. Report kept as pointer.

- F `78eedf50`: model-demanded rows and write-free activation changes were already inherited through B (`3779c750`, `4cf52e8d`, `1ecbfb15`). The remaining three frozen-probe portability fixes merged cleanly.

- Refreshed B to `5bf5b8da` and E to `70356696` (research/receipt changes; production unchanged). Added `research/lane-i/validate.sh` and exact single-protocol census receipt validation; 109 changed tests in four disjoint groups, one check job, three same-VM strict MLDR pairs, and 87 same-VM generation pairs. No lane-local analyzer is final gate evidence.
- Local submodule setup initially failed because the configured URLs are local paths; reran Git with command-scoped `protocol.file.allow=always`. Both pinned submodules are now present; no global config or other worktree changed.

## Live validation and interactions

Frozen candidate `5440a7b87ead19fcc02b9b8be86df382088d9cdf`, baseline `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`. Commands:

```
supercomputer run --jobs research/lane-i/validate.jobs.json --out runs/lane-i/v1/validation --class gate --timing --vm-type large --data runs/lane-i/v1/input:integ-input
supercomputer run --jobs research/lane-i/census.jobs.json --out runs/lane-i/v1/census --class gate --timing --vm-type large --data runs/lane-i/v1/input:integ-input
```

Both batches are running. Do not read scheduler launch success as validation success. Source archive/submodule hashes are recorded in `runs/lane-i/v1/input/identity.json`. Per-job CPU labels and placement accompany paired traces. A read-only filesystem watcher reports new committed lane tips; it never edits or merges on its own.

### For lane B / F

Your reported safety loss belongs to the disposable full 15.4+15.5 policy ablation, not automatically to current production: neither side of Lane F's ordinary-pipeline calibration lost safety. Lane I retains all production tips for measurement and does not install the rejected disposable policy. Lane F's current direct frontier increases work (about 667 to 885–1,075, no closure); keep that negative evidence visible. The integrated strict harness and census are running, not yet a promotion recommendation.

### For lane A / Fable wall

The integration retains A's parameter/fact checks and 2 s finite cap with Fable's sorted-family/unchanged-read optimization. Targeted boundary states must be recorded as rejected states so they can revive after a premise drops; the resolution does so. The integrated tests include declaration, cancellation, fixpoint, runtime-key ownership, and small-state tests.

## First frozen integration results

`5440a7b8`: all four changed-test groups passed; **check failed** in Lane B's `research/track-m/summarize-lane-b-pairs.ts` because `.sort()` lacked the required comparator. Fixed with explicit ordinal ordering in `0d9e1d3c`; no production change. Scheduler controller returned exit 0 despite the failed check job; the failure is retained and is not called green.

All three original MLDR candidate runs returned unknown under the strict wrapper. Initial trace: 34 generated/retained laws, Inv* and Inv2973-half are tried at about 3,050 units and return unknown; Inv1758 is tried at about 2,997 and remains unknown. Full per-repeat extraction follows when both batches are collected. `counts: candidates at 0 ms` is counted-clock output, **not generation wall**; no wall claim is inferred from that field.

Refreshed A to `26c04703` after the event-driven watcher notified its push: new strict audit/generation evidence only, no production delta. E/F report-only conflicts resolved by keeping this report and pointers. The newer source check remains pending; source-equivalent experiment receipts continue to bind the original `5440a7b8` engine.

## For lane B

The integrated `bun run check` caught `require-array-sort-compare` at `research/track-m/summarize-lane-b-pairs.ts:9`. `0d9e1d3c` supplies an explicit lexical comparator on both arrays without changing the roster assertion. Pull this fix or its equivalent; do not classify the failed check as infrastructure.

## Continued lane refresh

B advanced to `120b0787`: all changes are research/receipts, no core or kernel delta. Its new ablation links identify the safety loss with **reconstruction allocation caps**, not helper-only caps; keep that narrowed candidate research-only as the lane does. One source conflict in `summarize-lane-b-pairs.ts`: accepted B's extended explicit-comparator/optional-job-roster assertion in place of I's equivalent fixed-roster comparator, preserving both the lint repair and B's multi-arm/byte-verification audit. Report conflict resolved with this pointer.

I's first current-check rerun also caught one new research-only type error: optional `placement` access in `research/lane-i/summarize.ts`. Fixed conservatively with optional access (missing placements remain validation issues), committed separately. Both failures and all raw logs are retained. No production code has changed since the frozen `5440a7b8` experiment.

## Runtime audit refresh and census failures

Fable advanced to `671dc506`. The only new production change is the audited Uint32 `$unique` stamp rollover reset: zero the buffer and restart at one before a stale stamp can match. Kept A's independent runtime cancellation hook; source merge clean, report conflict kept as a pointer. Added rollover/growth test retained. This requires a fresh integrated run, not a silent transfer of the old SHA's results.

The first census completed 81/87 pairs successfully. Six generation-only `learning_switch{,_i4}` jobs exhausted the driver's 120 s process limit (one reached the scheduler's 210 s inner limit); neither a complete census nor a byte-identity claim for all 28 is supported. Those generation-only jobs now get the existing lane census allowance of 900 s per side with a 2,100 s job wrapper. **The original proof harness stays at strict 60 s; no proof budget changes.** All first-attempt failed receipts remain in `v1/census/`.

The first four changed-file groups total **584 tests, 19,569 assertions, zero failures** across 109 files. The own-summary type/lint failures were repaired separately; no clean full check is claimed until the new job returns.

## Measured pre-attempt wall (observation-only preload, v2)

Same-VM strict pairs against main, no supplied laws. `research/lane-i/timing.ts` timestamps candidate generation and the first completed attempt; pre-attempt wall subtracts that attempt's measured duration from its return timestamp, using the official result's elapsed time to establish proof start (millisecond rounding applies).

| repeat | CPU | main pre-attempt | integrated pre-attempt | integrated verdict / wall | safety tried |
|---|---|---:|---:|---|---|
| 1 | Ryzen 9 9950X | 24.819 s | 13.426 s | unknown / 59.009 s | no |
| 2 | EPYC 4585PX | 24.893 s | 11.778 s | unknown / 59.247 s | no |
| 3 | Ryzen 9 9950X | 37.985 s | 23.042 s | unknown / 59.020 s | no |

Receipts: `runs/lane-i/v2/validation/{mldr-r1,mldr-r2,mldr-r3}.log` and `placement.json`, candidate `e884f3af`. This confirms generation wall improved on the paired runs but does **not** solve the proof wall. Earlier uninstrumented v1: safety reached only repeat 1 (unknown); Inv1758 reached repeats 1/3 (unknown); Inv* and Inv2973-half were tried in all repeats (unknown, pass 1). No full family was kept. v1/v2 core bytes are identical; runtime rollover audit landed afterward and is being rerun as v3.

### For lane A / B / E / Fable

The integrated family is 34 laws (finite pass dropped 6 in the recorded v1 trace, including `CV at most 2`). The remaining unweakened overlap and disabled variants still consume attempts. Pass-1 Inv* about 3,071 units, overlap-half about 3,055 when it finishes its allowance, Inv1758 about 2,997: all unknown. Deadline overruns are now only atomic-query-scale in these traces; the finish line is not reached. This is combined-system evidence, not a request to adopt the rejected disposable leaf/class policy.

v3 now binds the current runtime-audit tip and repeats checks, all changed tests, MLDR ×3 and generation census. Prior type/lint failures in I's report script (optional placement; unused omitted-log binding) are recorded at `current-check/`, `fixed-check/`, and `after-b-check/` and fixed in separate commits. These do not change the engine.

## Runtime test repairs and final mechanics

Fable's `4b57a3b2` fixes its new rollover test: a sparse `[300,2]` call correctly takes the Set path and does not reset the stamp; an added dense call checks growth/reset instead. This test-only tip and F's complete stopping report `d5d14cc9` are merged. F's original full triple is also unknown and its 14 direct operation pairs showed no row-split gain; no promotion claimed.

The fresh v3 check exposed another inherited test issue: `new Function` violates `typescript(no-implied-eval)` in `core/runtime-keys.test.ts:55`. Replaced only the fixture execution with `node:vm.runInNewContext`; the generated source and all rollover assertions are unchanged. Both the original test assertion failure and lint failure remain in `v3/validation/`; corrected tests passed in `final-mechanics/` but its check still caught the lint issue. `final-mechanics-v2/` reruns all 109 changed test files and full check after this repair. No production behavior changed.

## Current lane ledger and commit policy blocker

All current committed tips are merged: A `f7894c43`, B `a778692e`, E `80f277d7`, Fable wall `4b57a3b2`, F `d5d14cc9`; main remains `b788e195`. The last A/B updates only strengthen their research checks/records; no production changes. Their report conflicts keep pointers, not copied prose. B's helper-only cap candidate remains research-only as intended.

**Commitlint is not green.** `runs/lane-i/commitlint/results/commitlint.log` checks 24 Lane I first-parent messages through `6dc0c8b0`; 14 earlier integration merges used `merge(research): ...`, which conventional commitlint rejects (`type-enum`). This is my integration-message error. They are not hidden, reclassified, or rewritten: history rewriting was not authorized. Subsequent merges use `chore(merge): ...` and subsequent ordinary commits use allowed conventional types. This remains an explicit acceptance blocker alongside MLDR; adding a new commit cannot change an old header.

The current production source remains byte-identical to v3 `1d7a276d` (excluding only the repaired runtime test). Later changes are tests, research evidence, and this report. All work is local; no branch push or merge into main occurred.

## Completed integration evidence, and next pushed runtime change

For production snapshot `1d7a276d` (v3): the **entire census is complete, 87/87 successful pairs, zero proof queries, all 84 non-MLDR lists byte-identical**. MLDR is 27 → 34 laws in all repeats; candidate canonical hash `dd495ab653ff4376b1c7b8c462c7dfafbcf9b3f5fc27949b8d61543ad5c69563`. Candidate generation walls: 12.260 / 14.834 / 11.886 s versus main 27.179 / 26.817 / 21.794 s. Six previous 120 s census timeouts are retained; the correctly allowed slow jobs returned successfully (261–482 s paired).

Post-repair mechanics: `final-mechanics-v2/` passes **585 tests, 19,580 assertions**, and full `bun run check` (zero errors/warnings). `current-tip-check/` independently passes full check after the latest research-only merges. No changes to `kernel/kernel.ts` or `lean-kernel/` relative to main. Neither result is a Lane D final gate.

V3 original MLDR remains **unknown in all three repeats**: 59.026 / 59.001 / 59.002 s. First-attempt walls 23.284 / 14.235 / 19.491 s; 34 laws each. Inv* pass 1: 3,071 units, unknown all three; Inv2973-half: 1,807 / 3,055 / 3,055, unknown. Inv1758 is not reached in r1, unknown at 2,997 in r2, then wall-cut immediately in r3. Safety not tried in any v3 repeat. This is the measured stop: helper/candidate cost still blocks the original harness.

New tips then arrived and were merged: E `e3adcdb3` (conditional lemma reduced to five checked premises, NOT a safety proof), F `3af7e73a` (diagonal source diagnostics), B `568fc570` (original-family audit capture), and wall `eb9aad68` (production per-step key-array cache). The cache's `$c` is allocated inside each compiled `step`; all writes remain after computed read expressions. Existing 2,400-step interpreter/compiled comparisons cover repeated steps; no assertion or budget was removed. Conflicts were only reports; the runtime patch merged cleanly with cancellation and overflow fixes. The wall patch is a real production delta, so v3 results are NOT promoted to this new SHA.

Fresh snapshot `d99480e80c1466cd97e8fe588646003f60c9dda6` is running the complete Lane I validation and 87-pair census in `runs/lane-i/v4/`. Its input identity was expanded from an abbreviated to full SHA immediately after submission; guest copies will be checked rather than presumed. All recent merge commits now use `chore(merge):`.

## V4 validation: current production, 2026-11-09

V4 validates the per-step key cache on `d99480e80c1466cd97e8fe588646003f60c9dda6` (guest identity prints unique abbreviation `d99480e8`; it is expanded here, not retroactively edited in raw logs). The latest E `30c4c889` and wall `21fee653` tips are also merged; neither merge changed the production source or the tested TypeScript files. V4's `bun run check` is clean and **585/585 tests, 19,580 assertions, zero failures** pass on boat.

All three original MLDR repeats still return **unknown**, 59.021 / 59.008 / 59.002 s, on AMD EPYC 4585PX. Candidate count remains 34. Wall before first attempt: **13.895 / 17.637 / 11.975 s**. Inv* pass 1 costs 3,071 units in each repeat, unknown; Inv2973-half costs 3,055 in each, unknown; Inv1758 costs 2,997 in r1/r3, unknown, and is not reached in r2. Safety is never attempted. The full fresh census is still running; its absence is not counted as a pass. A fresh check on the report-refreshed tree is also running.

## V4 census complete; new A/B/E/F/wall tips integrated

V4 is complete: **87/87 generation pairs pass, 84/84 non-MLDR pairs are byte-identical, and the Lane I analyzer has no missing/failed-job issues**. MLDR stays 27 → 34 laws with the same canonical hash in every repeat. Paired generation wall, candidate vs main: 21.123 vs 26.168 s; 16.432 vs 24.555 s; 14.088 vs 25.867 s. This is generation-only, not 29/29 proof. Refreshed full check also passes (`v4/current-tip-check/`).

While those jobs ran, all lanes pushed again. Integrated A `c21a6e54` (paired side exit propagation + regression test), B `539bde1b` (original-family audits), E `3f3a523c` (withdrawn exact-suite interpretation), F `36210941` (independent empty-count reconstruction), and wall `c775d8c1` (explicitly reverted per-step key cache). Only report conflicts occurred. The wall revert is preserved; integer stamp overflow and the test VM repair remain. F's syntactic emptiness hint drops premises and selects reconstruction; it does **not** admit a fact, bypass the checker, or raise the enclosing budget. Fresh explicit tests for both new files are added to Lane I validation.

These are new production changes, so completed v4 results are historical rather than final evidence for them. A complete v5 repeat is required and is being submitted next.

## V5 validation and latest range integration

V5 full check is clean (zero warnings/errors), and 599 tests / 19,620 assertions pass. Original MLDR verdicts: unknown at 59.006 / 59.010 / 59.049 s; candidate count 34; pre-attempt walls 13.897 / 12.809 / 11.256 s. CPUs are EPYC 4585PX / Ryzen 9950X / EPYC 4585PX. Inv* pass 1 takes 3,071 units, unknown all three; Inv2973-half 3,055 units, unknown all three. Inv1758 is not reached in r1, wall-cut at 0 units in r2, unknown at 2,997 in r3. Sixteen helpers are kept at deterministic units `[88,301,318,316,97,198,64,148,271,70,259,180,64,225,305,240]`; r3 additionally keeps one count-cube helper at 2,170 units. Its trace name is truncated, so no exact helper identity is inferred. Safety is never tried. The v5 census continues independently.

Wall `c21f301c` arrived during validation. Its range constructor is wired into counted passes through parent `d24a4196`; inspecting only the tip's two new files would have missed this. Resolved `core/counts.ts` by keeping B's completion retry and E's preferred member-inclusion selection, adding ordinary kernel-checked range instances at all three certificate construction sites, and retaining the existing shared `attemptEnd`. Resolved `core/finite-houdini.ts` by using the updated dropped-set revisit filter, preserving preconditions, certified drops, changed-read/no-op filtering and outer cancellation; removed only the duplicate relocated `lawReads`. F's independent-empty-source reconstruction stays intact. Removed the new range test's unused `Machine` import and added it to the validation jobs. No checker or Lean source changed. V6 is a new full validation/census snapshot, not a promotion of prior receipts.

## Range follow-ups and tiny-proposer merge

Merged wall `cc7bb326` (missing `CountDecl` type import) and B `803129c4` (the same range integration). Retained one range import, the earlier unused-test-import repair, B's completion and inclusion selection, and all three range insertion sites. The actual v6 check found an additional wrong `modelSequence` import in the range regression test; fixed it to `kernel/model-sequence.ts`. V6 failures remain in `v6/validation/`; they are not recast as passes.

V6 original MLDR is unknown at 59.017 / 59.004 / 59.003 s; pre-attempt walls 14.085 / 14.813 / 12.040 s. Sixteen helpers kept in each repeat. Inv* costs 3,071 units, Inv2973-half 3,056, Inv1758 2,997, all unknown in all three. Safety is not attempted.

Merged A `fdabeba4`: the new bounded tiny-instance proposal module and independent replay wrapper are experimental, not called by production generation. Resolved the added wrapper versus relocated `lawReads` by keeping both; the optimized ordinary finite path and outer cancellation remain. Added both new test files to Lane I's changed-file jobs. A tiny screen is never itself a proof or a certified drop: the wrapper requires the full family, facts/precondition and source interpreter replay. The complete v7 validation/census is the next snapshot.

### For lane A / B / Fable

The combined range+completion+preferred-inclusion path still exhausts the original helper limits in all three v6 repeats. Range seeding does not alone get safety scheduled. The import repairs above are integration-only, not weakened tests or changed budgets.

## V5 census closed

All **87/87 paired generation receipts** are successful, zero missing/failed-job issues; all **84 non-MLDR lists are byte-identical**. MLDR is 27 → 34 laws with unchanged canonical hash. Paired generation candidate vs main: 13.198 vs 20.237 s; 13.376 vs 22.356 s; 12.647 vs 24.950 s. This closes the historical v5 cycle (clean check, 599 tests, strict MLDR unknown 3/3), not the newer range-enabled candidate.

## V7 completion and coordinator upper-bound census

V7 (`704efc27694151cd4797707ebf5b8aea5b8df318`) completes with clean check, **621 tests / 19,688 assertions**, and **87/87 successful generation pairs**; all **84 non-MLDR candidate lists are byte-identical**. MLDR generation is 27 → 34 laws, same canonical hash. Candidate/main generation wall: 15.665/29.999 s, 12.576/20.434 s, 12.723/20.218 s. These are generation results, not a proof gate. F `15dc5ebc` subsequently merged with no production delta; the repaired range imports were retained.

For the coordinator's new upper-bound request, the unchanged original admission path captured **exactly 34 laws**, no supplied laws, at production SHA `15eff72f04f74351b622b02d08e47bfb9dfdb131`; family SHA-256 `5dbdbf766e9949b051d0764920f1bcc3707690cd6852fca6d0bcf18674fbdac4`. The actual dispatch has seven values (0..6), so the full roster is **140 shards** = five requested helpers/safety × seven ops × two passes × ceilings on/off. All jobs are submitted together, each exclusive large VM, 30-minute wall, effectively unlimited counted budget (`1e12`), no shared/subset pass allowance. See `research/lane-i/upper-bound/README.md` for the exact conditional STEP scope and ceiling-off changes. Both smoke variants executed real searches, source hash checks and CPU labels; they were deliberately censored at 2 seconds, not claimed as proofs. Full results are pending in `runs/lane-i/upper-bound/full/`. Integration continues separately.

## V7 original-harness stopping point and active research

The completed v7 strict runs are unknown at **59.012 / 59.018 / 59.147 s**; pre-attempt walls **11.746 / 15.935 / 14.778 s**. Inv* consumes 3,071 units and Inv2973-half 3,056 in every repeat, unknown. Inv1758 consumes 2,997 in r1 and is wall-cut at 0 in r2/r3. R1 keeps 18 helpers and reaches safety (still not proven); r2/r3 keep 16 and never try safety. No proof-gate claim follows from the clean mechanics and generation census.

Upper-bound implementation check is clean on boat. The 140-shard research batch is active; every shard is source-hash checked before disposable instrumentation. Source remains frozen at `15eff72f` for this census even as integration resumes. Results require independent certificate verification; missing records remain pending, and forced stops report counted work only as a lower bound. Aggregation tests explicitly cover those cases.

## Integration after the upper-bound snapshot

Merged E `36a278e9` (including B `6d69e094`, F `682c8dc6` and declaration-backed member premises), then Fable `5bf4535e` (demand-driven range repair). E adds ordinary member witnesses and only instances of existing declarations, under its 64-tuple / four-per-source limits; count-witness read-key independence remains enforced. Fable now adds a 0/1 count's range only when a model violates it, rather than eagerly burdening every goal. Its lane reported that eager ranges cost a non-MLDR verdict, which a generation-only census does not detect; Lane D's proof roster remains required.

Conflicts: retained `memberSources`, the guarded witness filtering, B's completion retries and E's preferred inclusion fallback; adopted `rangeWanted` with read lists on all certificate branches and range-triggered rebuilding in both model loops. Kept one import per symbol. The relocated finite `lawReads` and newer dropped-set replay logic survive unchanged. Added new member-premise and upper-bound aggregation tests to Lane I's jobs. The new source gets a complete v8 check/test/strict-MLDR/census batch. The already-running upper-bound shards are intentionally still bound to their earlier source manifest.

## B stopping-evidence refresh

Imported B `00a7d516` and its force-added raw archives. `research/track-m/LANE-F-HANDOFF.md` now records the original-34 Inv1758 early-entry limit: 6,002.553 counted units / 6,040.223 ms with field/row cases still open, not a proof. No derivability-closure/class-order events occur for its field-only claim. Baseline is wall-limited at 2,679.971 units / 7,018.544 ms, so this is not a same-budget cost win. These diagnostic results do not change the production settings, v8 source changes above, or the final gate status.

## Coordinator test-load alert and F refresh

Integrated F `53bf1264`: compensated directed-difference frame proposals retain the old difference under the existing cap and are checked by the original kernel. The coordinator flagged F's old `modelSequence` import. Integration already imports it from `../kernel/model-sequence.ts` (not `kernel/prove.ts`), but the quick-suite manual roster did omit this new test file. Added `core/count-ranges.test.ts`, `core/count-write-frames.test.ts` and `core/count-recovery/member-premises.test.ts` explicitly to `scripts/test-shards.ts`. No suite runner swallows a nonzero child status; its `--measure` route also fails if any file fails.

Added `research/lane-i/test-load-propagation.test.ts` to both the quick roster and Lane I validation. It creates an isolated real missing-export fixture beside a passing test, requires Bun to fail, then runs the actual quick-suite driver with that failing test group and requires failure/stop before the next group. It also asserts the explicit roster entries. Thus a passing file cannot mask a module-load error. These changes and the actual range test are pending boat validation below; they are not yet claimed green.

## For lane D

Please run the independent one-command final gate on **`704efc27694151cd4797707ebf5b8aea5b8df318`**, the current best combined A/B/E/Fable/F candidate (range insertion, preserved completion/preferred inclusions, F's independently reconstructed empty sources, tiny proposer present but NOT active in generation). Baseline is `b788e1959bba1f2e8aa1f94d4cf7c0eb163a2f9c`. Lane I's full v7 checks and 87 generation pairs have been submitted on that exact SHA. This is a request, not an assertion they passed. V6 still had 3/3 original MLDR unknown and two now-fixed import failures, so a red gate remains expected until measured otherwise. Bind both SHAs, exact roster, paired identity, CPUs, DuoAI/broken/bar and full check/tests; only your complete receipt may authorize GATE GREEN. If a newer lane changes production, I will explicitly supersede this SHA, not silently transfer your result.
