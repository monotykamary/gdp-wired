# Inv* final-STEP proposal result (not final admission)

## Latest scoped cap pilot

Tree `cd8e729ea52815a008056bc8bcce78bb80a388d3` passed5/5 jobs in
batch `20261111-081443-vovpow`. The original225M run now ends at
**224999999 raw units**, versus225642713 below, while the explicit unchecked
Inv* proposal still returns. Public result remains UNKNOWN. Controls:21 full
tests/126 assertions,17 legacy tests/69 assertions, types/lint1936 files.

The gap was ordinary `brokenOf` model evaluation through the lazy judge, not
a native checker. `withEvaluationAdmission` scopes amortized credit only to
that boundary; raw eval counters remain unchanged. It admits at most256 raw
units per block, consumes no new root/local allowance, discards nested-scope
credit, and admits individually near the endpoint. No protected prover,
checker, Lean, prices or tier allocation was changed. This is one original
cap result, not a28-original W campaign or final calibration approval.

Combined F/check-once/evaluator runtime `8ec48490b0ebaa22caf7a2748fb6365d78f47bf8`
passed14/14 native/regression jobs and the strict28/28 legacy-pair audit.
There were232 passing test executions/6408 assertions, plus native19-law/
38-packet replay,4 mutation classes, source checks and clean types/lint1972.
Both original manifests returned an unchecked Inv* proposal; nine-flag final
usage224999999, F-flag final225000051 (within1024 envelope, not strictly W).
Current nine-flag return consumes125004150.7273 W-relative units, leaving
99995849.2727. See EVALUATION-ADMISSION.md for exact benchmark/endpoint data.
The actual-hook benchmark measured6.569ms batch versus12.242ms per-node for
1M evaluations, with identical1M units; baseline3.726ms. This is a microbenchmark,
not a whole-prover speed claim. The real public-pipeline mutation control passed
1 test/28 assertions with clean types/lint1973 on59f390b7. Source committed as
51ee4018; A owns the remaining closing reserve.

## Historical first proposal pilot

The corrected native pilot on F-free tree
`a370e7fcc0568c9aa0ae8a69b541d7571401d11a` passed5/5 jobs in batch
`20261111-080351-3irrvj`. Source is based on committed6f05 plus the primitive
budget policy and explicit final-STEP proposal route. No tier/root/price/checker
or Lean changes. This tree is not yet the final committed combined pin.

## Integrated original run

Original MLDR, W225000000, same T220 eight flags plus
`GDP_COUNT_FINAL_DEFER_CHECKS=1`:

- All7 Inv* operations propose.
- `count-strategy-result`: `proposed:true`, `checked:false`,
  `status:"unchecked"`. No early final STEP check executes; INIT still checks.
- Return clock490481.2614392; observed root end900000.052.
- W-relative consumption at return122620302.3598 raw units; remaining
  102379697.6402. This uses the actual root accessor, not the count plan's
  larger local endpoint929695.37528.
- Public final verdict is UNKNOWN, not a claimed proof. Final raw225642713
  exposes an unresolved642713-unit endpoint overshoot. Therefore this run is
  NOT a hard-cap/1024-slack, whole-family, wall-performance or W admission.

For comparison, the preceding primitive-only pilot reached a TRUE native
STEP check that cost81194798 raw units, but it exhausted the local strategy
allowance before INIT/return. At the actual root end this check would have
left about21.18M, not the initially estimated28.6M. The latter estimate used
an incorrect assumption about the root endpoint; A and t1 have the correction.

## Controls

- Full-mode proposal/refusal controls + primitive policy:10 tests/94 assertions.
- Legacy mode, including original scope suite:16 tests/68 assertions;5 explicit
  full-only skips.
- Full mode with final-defer disabled:4 tests/22 assertions;5 explicit skips.
- Types/lint clean on1935 files.

Total30 passing tests/184 assertions. Coverage includes checked standalone
finishing despite the environment flag, invalid deferred STEP refusal,
missing/bad INIT, changed count bound/read declaration, repeated closing calls
with mutation between them, valid deferred replay and bad replay refusal,
throwing-check refusal and unchanged primitive/legacy limits. Stronger helper
and global-freshness controls are in the next gate, not counted here.

The first pilot's failed control receipts remain in results/final-step-pilot:
an existing expiry assertion was being run in a different meter mode; an
allegedly invalid declaration drop still proved a natural-number tautology;
and a bad empty leaf was already rejected by the untrusted transporter. Tests
were corrected, not the unchanged native predicate.

## Remaining integration

- A owns closing/native reserve and root-vs-plan bounds; no allocation patch
  has been made here. D is reviewing the explicit proposal contract.
- Candidate4d4df527 added the inherited flags-off call-site gate and
  helper/freshness controls and passed5/5 jobs.51fb8efc added the genuine
  changed-required-instance refusal and passed2/2 jobs.
- Independent F gate's34 jobs passed execution, but strict parity found11/28
  order differences already present on6f05. Three production `supportOrder`
  calls now pass a machine only with STRATEGIES1; the helper API is unchanged.
  F/default re-gate treeba0c639d passed34/34 jobs and strict28/28 pairs,
  committed separately asf07e9656. No failed strict audit is relabeled.
- The disposable counter-crossing sample located the overshoot. The scoped
  evaluator pilot above repairs it without changing the production counter
  or checker. Overall wall improvement is not inferred from this cap result.

Files: count-final-step.ts, count-strategy.ts, count-case-compose.ts,
count-guard-composition.ts, count-row-composition.ts, count-strategies.ts,
count-proof-scope.ts, counts.ts; primitive policy files are documented in
FINAL-STEP-PLAN.md and the pilot manifest. Large native logs are under
runs/lane-i/rolling-final-step-v2 and copied gate receipts under results/.
