# Authoritative 51ee campaign contract for D

Source: `51ee4018ba8ad802a4b2d061a51afa59bd943aff`.
Evidence-only head: `226a7089`. Read the source from git, not this working tree.
Authorities: `CHECK-ONCE-HANDOFF.md`, `check-once-combined.jobs.json` and its
`combined-original-check-once` / `combined-original-lifted-report` entries; immutable data archive
`/tmp/lane-i-check-once-combined`.

## Provisional historical W

W = **225000000 raw provisional work units**. The original runner uses
`--ms 900000`, fullRate250. Do not substitute the old150M pilot budget.
This is a reproduction value, not the final reference-seconds calibration.

## Exact nine-entry baseline environment

```
GDP_WORK_FULL=1
GDP_WORK_STEPS=0
GDP_COUNT_FRAMES=1
GDP_COUNT_REJECTIONS=1
GDP_COUNT_STRATEGIES=1
GDP_COUNT_TIERS=1
GDP_REQUEST_QUOTIENT=1
GDP_COUNT_ROW_DEFER_CHECKS=1
GDP_COUNT_FINAL_DEFER_CHECKS=1
```

The first eight are the pre-check-once environment. The ninth is the actual
check-once/STEP-proposal flag; there is no separate CHECK_ONCE environment name.

## Separate twelve-entry F variant

Add exactly these three to the nine above:

```
GDP_COUNT_LIFTED=1
GDP_COUNT_LIFTED_PREREQUISITES=1
GDP_COUNT_LIFTED_REPLACEMENT=1
```

Do NOT add GDP_COUNT_DEFER_CHECKS, GDP_COUNT_CLOSING_RESERVE, G1, C2, R1, R2,
new generation flags, or any working-tree feature. Clear ambient GDP_* flags
rather than inheriting them. The F variant is separate, not implied by51ee.

## Coordinator-authorized deferral profile update

After the historical contract above, t1 explicitly requested adding
`GDP_COUNT_DEFER_CHECKS=1` to D's F campaign. The new **13-entry** profile is
`51ee-deferral-profile.env.json`; label it separately from the historical
12-entry receipts. Source remains51ee until another pin is explicitly admitted.

Source correction: c2242022 gates K3 with `GDP_COUNT_ROW_DEFER_CHECKS`, already
present. `count-row-agreement.ts` requires deferToComposition && deferRowChecks;
P4 K3 leaves already report unchecked-proposal. The added global DEFER flag
controls F's replacement on51ee, and all three extra constructors only after
G1 is separately integrated. Do not conflate these changes or carry a fit
between the12 and13-entry profiles.

The new global flag belongs in future integrated manifests as requested. It
does not authorize G1/C2 source advancement for D, calibrated-W transfer, or
closure/promotion while the native/Lean discrepancy is under audit.

## Full-mode STEP exclusion boundary

`deferFinalCountStep` requires BOTH completeWorkProfile.enabled and the exact
internal familyStepProposal symbol, in addition to COUNT_FINAL_DEFER_CHECKS=1.
Only the counted guard/row dispatcher supplies that capability. The individual
final guard/row STEP check is deferred; its returned metadata is explicitly
status:unchecked and checked:false. INIT remains checked. Ordinary/public
standalone strategy calls and F's standalone composition remain checked.
The final public family checker is unchanged, not skipped or cached; both
closing call sites operate on current machine/family/instance/certificate bytes.
These exclusions are about the internal proposal phase, not accepted proofs.

## Recorded outcomes, not final admission

Nine-entry original: unchecked Inv* returned after125004150.7273 units,
99995849.2727 left; final224999999. F variant: return125004812.7273,
99995187.2727 left; final225000051. Both final verdicts UNKNOWN. The latter
only meets the historical1024-unit envelope, NOT strictly<=W.

The paired feature-off28 legacy census used15M LEGACY units and explicit
GDP_WORK_FULL=0/GDP_WORK_STEPS=0. It is not evidence for a full-work W campaign.
D's6f05 pilot is distinct and does not validate51ee. Final calibration uses
the newly agreed reference-seconds method and requires the admitted new pin;
no older fit or budget transfers implicitly.
