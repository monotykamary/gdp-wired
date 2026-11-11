# F conditional-route integration stage (pending gates)

Approved eleven-file source: `c87fcb75c2880d51b86820ae98d4a0f261d0ed65`.
Owner's expanded contract: trackL `research/track-m/C87-RUNTIME-HANDOFF.md`.
Prepared B prerequisite context: `ed5cf6782ac5b5e0d7268055fbb1461b5bb9d262`.
Earlier F4/F5 features: cd671ac1, a99d9210, c0482014, 189d248f,
cffa5026, b5a0ce70. These are prerequisite provenance, not new combined approval.

Base runtime: A `23f74e5c` on K3 `b232e68c` and B `f29796ee`.
Evidence-only head before this stage: `738789be` (strict Q1 repair).
First runtime test tree: `dc415081ff27de58aaa2ff450f29561ea0167e02`.
Expanded family/test-harness tree: `fa976c60c1f6aa3acf8b17d91d82987084c38bc4`.
Their core/kernel trees are byte-identical, but they are not final candidates:
a subsequent static audit found an unconditional provenance allocation leak.
Corrected tree: `fdeb51a0b99ddd5ad96c6f20caa8eb275d342e5a`.

## Explicit merges

- Twenty absent files: thirteen prerequisite helpers plus seven missing roots.
  All copied from exact c87; no new lifted-family/threshold-field/load-marker
  producer or research whitelist is included.
- Keep B's `countGuardTree.hoist` and alias logic; add only `yesFirst` ordering.
- Keep B frame query, leaf cap and deferred-check options. Normalize zero
  coefficients before canon; add F's `extraWhen` option.
- Keep K3's row deferral, optional helper interfaces and tail tracing. Add F's
  separate composition-only intermediate-deferral option and unchecked metadata.
  Final native checks stay in place. No minimizer environment policy is enabled.
- Keep row/guard registry order and pools. Add only the opt-in lifted selector,
  structural prerequisite ranking and composer dispatch from the prepared source.
- Quorum provenance is WeakMap metadata; candidate JSON, formulas and order stay
  unchanged. Changed formulas cannot reuse a stale tag. Its AST-building work
  now runs only for explicit `quorumLaws(m,true)` or GDP_COUNT_LIFTED=1. Without
  this gate, even disabled F changed raw AST counters. Explicit F tests retain
  their tags, and a new regression checks identical formulas and repeatable
  disabled-meter deltas.
- Guard facts retain B's searchEnd/deadline refusal, adding F's CDCL/minimal-view
  and explicit proposal options rather than replacing that boundary.
- Composer keeps K3's tail records and adds F's native timing records. Its F
  stage assertion projects the native records before checking their exact order;
  proof/native-check/clock assertions remain. The old D clock regression bytes
  are separately retained unchanged at SHA2563d8aca2f... and run verbatim.
- No existing count-cases, recovery, machine, solver, wall, runtime-wall, trace
  clock, kernel, Lean, counters or weights are replaced.

## Recorded acceptance gates

Final staged runtime tree `ba0c639da71d0b15670650fd41b64e75f32f081d` passed
34 execution jobs and the separate strict28-default audit. It also repairs
three inherited B call sites that requested count-first order with STRATEGIES
off; the pure helper API is unchanged. See `F-RESULT.md`. These are scoped
source/native/default gates, not an online whole-family or calibrated-W claim.

## Gate contract

Pilot: shapes, increments, transports, negative/deferred controls, B/K3/A
preservation and complete type/lint. Expanded gate: unchanged old clock test,
observed/unobserved proof plus complete raw-vector identity, original frozen
19-law/38-packet family, full native checker/freshness/mutants, original admission.
The literal feature-off28 paired census is prepared against5e52, with only
GDP_WORK_FULL=0 and GDP_WORK_STEPS=0 present. This is distinct from the historical
clock-off run, whose strategy/tier/frame knobs were explicitly on.

The later reader-cap investigation produced isolated commit `6f05aee1` on the
without-F base, not a wholesale F import. It is the explicit one-file protected
exception: seven endpoint checks plus two imports in `kernel/reader.ts`, whose
decoding bytes reconstruct the original exactly. Native TypeScript runtime
import analysis proves the checker closure excludes the reader. See
`READER-CAP-PIN.md` and `READER-RESULT.md` for its separate gates.

No combined admission, all49 closure, measured speedup or calibrated W claim.
