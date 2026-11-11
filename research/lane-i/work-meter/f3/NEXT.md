# Native and original-path checkpoint

All owned batches are terminal. Active handoffs: `d3171c30`, `b7986de1`,
`33c65fb5`; frozen strategy source `cd00524f`, tree
`6d1453342ca15df8bf948465c13cbf9a1aedf8a2`. No W or production admission.

## Verified results

- 174-case bounded format contract and independent negative controls passed.
- Strategy row proof checked, complete phase events and exact source exported;
  direct ordinary/EPR fixtures passed. See strategy/VERIFIED-SOURCE.md.
- Original consensus proves/checks in two fresh repetitions (212 FM, 863 plain
  rows); broken variant non-proven; raw/result/phase summaries agree.
- Original consensus_epr stops in preflight at both 15M and 50M diagnostic
  allowances. At 50M: 49,841,887 evaluations, zero EPR work. Both failures are
  retained; do not manufacture coverage with further budget bumps.
- Native 10M run preserved raw/result/phase totals but hit its observation cap.
- Native 100M run (`20261111-015254-rydo8b`) preserved all those values with
  31,172,052 spans and no overflow. Five timestamp-valid stable windows,
  eleven changed windows. One ~304 ms invocation is `canonFlip`'s WeakMap.set;
  two certFor and two tree-walker go windows remain unattributed. Invocation
  spans include reflection/callbacks/GC, not an exact native instruction.
  One invalid profile was excluded and retained only as hash/size metadata;
  its full payload exceeded the diagnostic log limit.
- Six span controls / 22 assertions and full type/lint on 1,727 files passed
  (`20261111-015523-rjj9on`). Native canonicalizer identity: 96 cases, 335
  marked calls, original/wrapped-off/wrapped-on raw and output agreement.

## Replay / next work

`audit-native.mjs` takes a native-profile log plus the saved
`runs/lane-i/resume-numeric-f3/f3-numeric-mldr-pilot.log` baseline.
`calibration/audit-original.ts` audits `runs/lane-i/original-path-coverage`, or
`runs/lane-i/original-epr-50m epr-only 50000000`. Audit logs are saved there.

Next: retain full invalid-profile payloads through bounded artifact transport;
attribute certFor/tree-walker windows; investigate EPR preflight cost without
changing original inputs; continue full F3. Lane D must deliberately freeze
any new source and opt in to the strategy hook before pricing it. Full F3,
original EPR coverage, calibrated W and the 35% strategy share remain open.
Leave `.reflex-saved/` untouched.
