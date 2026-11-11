# Direct mini phase-ledger contract

Lane D's `reference-mini/run-mini.sh` CHILD reads these APIs directly from its
pinned source, with no adapter and no phase-name weights:

```ts
import {rawWork, workKeys, withCompleteWorkWeights} from './core/work-meter.ts'
import {withWorkLedger, type WorkPhase} from './core/work-ledger.ts'
```

Keep `events: WorkPhase[]` in each `mini-calibration-raw/v1` gzip record.
Each fit row is `{phase: e.name, raw: e.exclusiveRaw, wallMs: e.exclusiveWallMs}`.
Never fit inclusive `e.raw` or the F3 facade's aggregated phase map. The root's
`raw` and the sum of every event's `exclusiveRaw` equal the case's raw delta.
`id`, `parentId`, `depth`, `completed`, `raw` and `exclusiveRaw` also form the
per-repetition deterministic structural signature; wall values are not in it.

The 20 exact keys are exported as `meterKeys` in `contract.ts`. They are the
12 fixed legacy dimensions followed by tableCells/checkSteps/astNodes/evals/
cubeTests/ticks/cdclNodes/epr. Numbers are counts, not divided by 250. Lane D
fits its nonnegative extra coefficients and computes W; this code chooses no
calibrated coefficients. The optional bounded **format diagnostic** uses all-one
weights for the eight extra counters solely to obtain finite fixture runs, and
records them explicitly. The twelve legacy coefficients stay fixed.

`validate-mini.ts` extracts the **exact CHILD** from a frozen copy of lane D's
kit and checks all 58 original/broken cases in three fresh-process repetitions
on the same pinned `aeef6091` tree, at a 100,000 fixture allowance. This is
174-case format, phase and repeatability preparation, NOT the once-only mini
calibration, not a weight fit, and not proof/host/F3 qualification.

The first unweighted run (`runs/lane-i/mini-phase-contract-routed/`) did **not**
pass: all three case workers returned a null child status. Its old assertion did
not retain signal/error/case identity, so no more specific cause is asserted.
Those failures are preserved. The driver now emits per-case starts, successful
receipts and partial summaries, with signal/error on child failure.

`bounded.jobs.json` supplies `bounded` to each repetition, passing explicit
all-one diagnostic weights for exactly the eight extra counters to the same CHILD. Any success there verifies
format/partition/repeatability under that fixture policy only; it does not
validate the unweighted paths, fit a weight or qualify the mini.

The current pin has the same ledger blob as `32a59b2a`, but lacks lane B's
later `37d006af` opt-in production strategy hook. The kit must not claim that
those 174 baseline cases measure a strategy path absent from its source.
The strategy composition is prepared separately; source-pin changes belong
to lane D/coordinator and require their own frozen evidence.

## Verified bounded format result

`20261111-013419-oblh9u` passed all 174 cases with eight explicit diagnostic
ones. Independent audit `20261111-013540-hq5zlp` matched the raw/phase
signatures in all three repetitions and rejected duplicate cases, mixed
weights, altered signatures and a wrong source. The signature digest is
`023da56d500346ae5e4d929b64c5c149b28218396e49c74705a8e7f79c99c3d6`.
No case had positive EPR work: this is not EPR-path coverage.
