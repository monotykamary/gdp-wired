# Robustness fixes — complete

Validated on `gen/robust` against pinned base `9d6fda8a19e31611203f653ef78611e4ece737e9`.
Three separate fixes: bounded cyclic certification; deterministic counted witness/support queries; reserved soundness fuzz for changed kernel inputs. No trusted checker/Lean change, no rate recalibration, no push or GitHub writes.

## Evidence
- Detailed report and commit IDs: `runs/REPORT.md`.
- Fix 1 final source: `runs/final1`; gate receipts `runs/final1-gates/recovered` plus `missing-interactive` (see `PROVENANCE.md`). Check, all seven shards, touched tests pass.
- Fix 2/final cumulative source: `runs/final2-ready`; `runs/final2-gates/out` plus unchanged shard-2 retry in `recheck`. Check, all seven shards, touched tests pass.
- Paired IC3Syn: candidate and main 24/29 in all three runs for both fixes. DuoAI: both candidates 10/10 in all three runs; main 10/10 throughout except one 9/10 run for fix 2. No every-run loss or error. `runs/final{1,2}-gates/paired-summary.json`.
- Ten fresh no-lost-keys processes: all proven, counted work exactly 1605477; repeated in the final gate under load. `runs/fix2/ten` and final2 `touched.log`.
- Treadmill own suite: 25/25, `runs/fix3/tests`; current runtime source covered by final cumulative check/shards. No live deployment or multi-hour soak.
- Quick bars: `runs/bar/runs/robust-final1` and `robust-final2`, with incomplete queue-capped TIP/SV groups superseded by `robust-final1-recovery` and `robust-final2-recovery`. Complete recovered coverage; wrong 0, solid losses 0. Lean samples 6/6 each.
- Three-round matched-VM speed experiment: `runs/speed-measurement/speed-summary.json`; complete, all assertions pass, overlapping ranges and no solid slowdown. This timing-only experiment uses a 60s test harness timeout equally on all trees; original required test gates remain unchanged. Earlier censored diagnostics are retained, not counted as passes.
- All three conventional commit messages passed strict commitlint in `runs/commitlint/verified`.

## Cleanup and remaining work
No required work remains. All owned shell controllers are terminal. All five owned fallback Modal apps stopped with zero tasks (`runs/owned-modal-status.json`); `supercomputer reap` reports zero Modal apps/pods. The shared scheduler/pool is intentionally left alone. Pre-existing untracked `brief.md` preserved. No push.

Possible follow-up, not part of these fixes: improve bar recovery after queue caps, and inspect the shared worker disk-full incident documented in the report. Neither changes this task's validated source.
