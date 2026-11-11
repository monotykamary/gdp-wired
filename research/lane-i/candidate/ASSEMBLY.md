# PENDING-D candidate assembly checkpoint

Pins: A 5aa76818; B 8ad0072f; F 9a3e3792; clock 353713c9.
Candidate worktree: ../gdp-wired-candidate, branch claude/mldr-candidate.
Clock cherry-pick: 93e4e3bf. B merge checkpoint: 915ab320.
F merge checkpoint c317a75a; compatibility fix db14ee14. Initial validation
passed the full-work tripwire; 85/86 focused tests passed. The one failure was
a six-argument API mismatch (A recovery boolean versus B selected-law Set),
now supporting both. Typecheck also exposed a missing F research helper
export; F's backwards-compatible frozenTarget extension is restored.
Validation on db14ee14 now PASSED: 86 focused tests and full type/lint on
2,036 files; full-work tripwire passed. Original consensus proved and checked.
Original MLDR at 15M units is unknown: generation allowance exhausted after
4,424,579 search units (zero queries), versus A baseline 4,424,769. Paired
28-model census and 150M/1.5B MLDR diagnostics are in flight; no no-loss or
whole-model proof claim yet.

Resolution policy:
- A: full-work scopes, counters, bounded generation, late recovery, telemetry.
- B: production strategy selection, shared tier endpoint, ordinary fallback,
  stronger exact count-definition admission and leaf cap options.
- F: lifted load/copy modules, provenance, guard-fact minimal views, branch
  ordering and carried-write classification. New F modules are retained.
- count-frames combines B's deferred precheck/minimal views/leaf budgets with
  F's extraWhen and zero-coefficient normalization. Neither is dropped.
- Preserve both differing test versions with .lane-b/.lane-f names.
- Non-runtime research conflicts keep A/B versions; F remains in merge ancestry
  and all F-only research files survive. No experiment fixture is proof authority.

Trusted overlay:
Use reconciled B tree becd98e30bf4b7df29217fa820b82b7aa259bf28 for kernel/ and
lean-kernel/. Lean is exactly b9039b851d59b7621e322a797096fcd724019f68.
Necessary declared kernel exceptions: kernel/prove.ts retains A+clock scope
helpers; kernel/meter.ts and kernel/work-budget.test.ts retain A's raw-meter
module and scope tests. Thus the FULL kernel subtree is not literally the
old db5bc38... hash; the checking sources are pinned to that subtree. This is
not a new checker implementation and remains PENDING-D. Do not merge to main.

Next: finish F resolution, commit candidate snapshot, run full type/lint and
focused combined tests on supercomputer; then original MLDR + 28-model census
with raw counters/phase/case events. Units are diagnostic, not calibrated W.
