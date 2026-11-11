# Next combined pin — validation pending, no freeze

Branch `claude/mldr-next-combined` in `../gdp-wired-integ-next-stage` is a
fresh child of `4bec30ad095fbb75396947a37ea113f47d875cc5`. The original dirty
I worktree remains untouched. R1 is isolated on `claude/mldr-r1-native-stage`
in `../gdp-wired-integ-r1-stage`, held out pending its timing and own gates.

## Ordered composition

1. Exact production rejection `3bc30b20` delta from51ee.
2. Exact generation cancellation correction `78796c83` (SOURCE-ONLY ACCEPT),
   patchSHA304c6a6d53e18a6c2bc8fa2f426759be173a096d6db64a1a3d4d6a76fb92deb3.
3. Exact5-file closing baseline `f213770e` on3bc.
4. Exact scheduler `826d0989`, then deadline correction `3fc6dbbf`.
5. Frozen B22/R2 partial treee59827c5 (no R1). Two deliberate overlap
   resolutions retain A's `shapeFamily` and B22's `reindexFactsOnly` in
   `core/count-strategies.ts` and `core/count-row-composition.ts`.

`core/counts.ts` is byte-exact3fc; the corrected generation helper and frozen
regression are byte-exact787. Other unchanged A files are bound in
`ADOPTED-A.tree`. All181 prior protected bindings are checked, with only the
three documented B22 materializer/test exceptions. No kernel predicates,
prices, root grants or exports are changed.

## Scope and default-off flags

- D4bec acceptance is bounded to its exact delta and fixed225M observations.
- D787 carries the explicit-budget/replay-ledger source findings forward;
  parent3bc is not retroactively green. Trigger: three flags plus a
  structurally GENERATED quorum law, not a selected/admitted strategy.
- `GDP_COUNT_CLOSING_RESERVE=1` and `GDP_COUNT_PREREQUISITES=1` enable the
  closing/scheduler path only with its existing deferral prerequisites.
- B22 `GDP_COUNT_REINDEX_FACTS_ONLY=1` remains row/guard only, no lifted caller.
- R2 `GDP_COUNT_EMITTER_FRAME_POOL=1` remains research-native/Lean HOLD.
- No flag is activated by default. R1 is not included in this candidate.

## Gate before commit and D request

Run exact-source native/component controls (including both frozen deadline
regressions), type/lint, both commitlint configurations, unchanged protected
and A bindings, and strict28 normalized feature-off legacy pairs. Record a
new original225M endpoint as a bounded observation, not calibratedW or a
whole-family admission. Preserve failures, fetched file hashes and source
identities. Native replay of an existing family is not fresh combined-family
generation or Lean clearance.

All heavy work uses supercomputer with SUPERCOMPUTER_CONTROLLER=1.
Results carry paths/hashes/metadata only; fetch full artifacts as files.
No push. After the gate, make the next combined source commit and send D
an exact source/diff/receipt request; no automatic freeze follows.
