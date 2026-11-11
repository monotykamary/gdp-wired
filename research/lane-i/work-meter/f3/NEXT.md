# Native and original-path continuation checkpoint

Committed: `d3171c30` (174-case format contract), `b7986de1` (strategy meter
handoff). Frozen strategy source: `cd00524f` / tree
`6d1453342ca15df8bf948465c13cbf9a1aedf8a2`. No W or production admission.

Completed original-path study (`20261111-014806-1pinis`): consensus proves and
checks with actual ordinary work in both repetitions (212 FM, 863 plain rows),
broken remains non-proven, raw/results/phase summaries agree. consensus_epr
exhausts the 15M diagnostic allowance during preflight, with zero EPR work.
The 50M follow-up (`20261111-015254-2waz3y`) likewise stops in preflight at
49,841,887 evaluations. Both failures are retained; no original EPR coverage
claim. Replay `calibration/audit-original.ts` on the old folder, or add
`epr-only 50000000` on `runs/lane-i/original-epr-50m`.

Completed native first run (`20261111-014727-41pz5e`), frozen `32a59b2a`:
raw/verdict/exclusive phase totals match the saved original-MLDR baseline;
three timestamp-valid stable windows, six changed windows. The 10M span guard
saturated and zero invocation attributions were accepted. Replay
`audit-native.mjs` with its log and
`runs/lane-i/resume-numeric-f3/f3-numeric-mldr-pilot.log`.

IN FLIGHT — do not duplicate:
- Native 100M guard follow-up: task `336b73f9-cccd-4637-893b-28d72a048c5e`,
  batch `20261111-015254-rydo8b`, output `runs/lane-i/native-profile-100m/`.
  Same source/model/baseline; only diagnostic cap changed. Require full
  comparison and audit. Invocation spans include callbacks/reflection/GC,
  not exact native instructions; full F3 and calibrated W remain open.
Final type/lint retry after explicit audit receipt types PASSED in
`20261111-015523-rjj9on`, output `runs/lane-i/native-final-typed/`: six span
controls, 22 assertions, zero warnings/errors on 1,727 files. The prior
audit-only TypeScript inference failure remains preserved.

Native controls: six tests / 22 assertions pass. Production canonicalization
identity: 96 cases, 335 spans, all raw counters and outputs unchanged across
original/wrapped-off/wrapped-on. COMMIT-30 has passed commitlint. New F3 and
original-coverage files await final checks and commit; leave `.reflex-saved/`
untouched. Update REPORT/README and this checkpoint with actual results.
