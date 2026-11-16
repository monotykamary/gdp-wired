# 0.50.2 source-triage

Read-only classification of the ten non-Lean known-failure jobs at `70b660443`.

## Result

- **55 unique test signatures / 76 manifest job-test instances.** `runner-cli-c-jvm` is a 21-signature duplicate of the direct C and JVM jobs, retained in `classification.json` as a job identity but not counted as an independent failure.
- **Dominant cause:** fail-closed source translation finalization, not a flaky test result. `translationVerdict` in `core/source-check.ts` rejects a marked source rule when the native journal is unavailable: `source translation unchecked: native source replay is unavailable or disabled`.
- **Important correction to the starting hypothesis:** ad-hoc `r.stepLaw`/`r.law` assertions indeed have no `attachNativeLaw` binding, but the observed runs stop earlier at the unavailable-journal guard. Thus a native-law binding is necessary but not sufficient: restoring the journal is first required. CLI/source-comment laws built by `core/laws.ts` do bind native laws, yet are also refused when replay is unavailable.
- **Two genuine non-Lean core gaps are evidenced, not erased by the dominant source-finalization cause:**
  1. `trading` order-book: Book step-law cyclic translation falls back/uncovered on three named goals.
  2. `extract-c` boundary-inferred case: diagnostic reports `kernelProven:false` and meter cyclic fallback/uncovered before finalization.
- No watchdog/infrastructure receipt establishes flakiness. The loops case's 50.54s duration versus `check({ms: 30_000})` leaves a wall-budget contribution **unresolved**, not a reason to waive it.

## Evidence

Original immutable receipts were read in bounded ranges:

`/home/user/VCS/working-remote/open-source/gdp-wired-bapa-finish/runs/bapa-release-0501-final-70b660443-full/{trading,extract-rb,extract-ex,extract-c,extract-jvm,extract-swift,extract-orm,extract-rs,extract-go,runner-cli-c-jvm}.files/{stdout.log,stderr.log,COMMAND-RESULT.json}`

Two narrow diagnostic runs (temporary remote test-copy instrumentation only; assertion still throws, so exit 1 is expected evidence rather than a passing test):

- Boat batch `20261116-185100-0hhylj`, class `interactive`, `--timing`, large / AMD Ryzen 9 9950X.
- Raw exports retained at `/tmp/bapa-0502-control/runs/source-triage-diagnostics-01/`.
- `diag-ruby-native-law-gap`: 6.41s, exit 1; public verdicts include `kernelProven:true`, `translation:"unchecked"`, unavailable-native-replay reason.
- `diag-c-native-law-gap`: 38.11s, exit 1; same verdict for representative source-gap cases and one independently observed `kernelProven:false` C boundary gap.

## Honest recommendations

1. **Do not weaken assertions, mark unknown true, or call the source cases flaky.** They currently assert source-backed proof while the public mechanism deliberately refuses to certify it without native replay.
2. For source test coverage, choose deliberately:
   - make replay journals available and register native interpretations for the stated laws (stronger assertion); or
   - split expectations into symbolic `kernelProven` coverage plus an explicit assertion that source finalization is refused without replay (weaker, but honest and already modeled by CLI tests).
3. Repair cyclic translator/prover routes for Book and the C boundary independently; neither is a Lean-export fix.
4. This lane recommends **no release-scope Lean change**. Parent decides whether source replay infrastructure or expectation restructuring belongs in 0.50.2.

Exact per-test records and duplicate mapping are in `classification.json`.
