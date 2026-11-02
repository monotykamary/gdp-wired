# Lane TB2 — ready for coordinator review

## Outcome

General container-observer synthesis and guarded equations are implemented on `gen/laneTB`.
Main `c6036e6` was merged as `0e27f34` before final verification. Solver freeze used by the accepted bars:
`0e27f345df99+09b85b07`. No clock-rate or benchmark-limit changes.

All requested gates pass. Three full paired TIP runs prove **225 / 225 / 222** against main's
**222 / 221 / 222**, wrong **0** throughout. Each run has **three solid per-task gains and zero losses**
after three reruns per side. The three gains (`isaplanner/prop_52`, `prod/prop_06`, `sort_TSortCount`)
each prove **12/12 against 0/12**. There is no aggregate min/max solved-count gain: 222 equals 222.
Tree-sort count answers in 11.0–30.1 s. Full heap-sort, selection-sort count and the large quicksort case
are not claimed solved.

## Accepted evidence

- `runs/bar/runs/laneTB2-lazy-tip{1,2,3}/REPORT.md`: full TIP pairs against `c6036e6`.
- `runs/bar/runs/laneTB2-lazy-quick/REPORT.md`: wrong 0 in every view, no solid solve loss,
  no failed one-vCPU jobs, Lean ITS 6/6.
- `runs/tb2/final-speed.json`: all 34 paired one-vCPU tests have complete triples and overlapping bands.
- `runs/tb2/lazy-checks2/`: type/lint, seven shards, synthesis/negative tests, datatype suite,
  new TIP/guard Lean replays, same-VM profiles, commitlint — all 15 jobs successful.
- `runs/REPORT.md`: full implementation, trust boundary, failures, measurements and limits.

## Important implementation details

- `core/data-synth.ts`: additive observer algebras lifted to recursive containers; guarded removal and selector laws.
- `core/data.ts` / `core/transfer.ts`: every candidate kernel-proven, certificate fact indices preserved.
- Lazy call-count admission after the first light proof attempt; refutation/transfer inspection do not pay for unused
  counters. Normal definition admission remains mandatory. The prior eager version failed speed and was not committed.
- `lean-kernel/data.ts`: arithmetic closes the simplified guarded statement; only standard Lean axioms.
- New regression files and shard registration are included. No trusted checker or Lean kernel definition changed.

## Handoff

Review the local branch's implementation commit and merge only through the coordinator; nothing was pushed.
All owned work is stopped/completed. Both final automatic fallback apps are stopped with zero tasks.
The optional 68-false-TIP driver never launched: its slot waiter was canceled after required gates passed.
Do not count that corpus or a full replay of all unchanged TIP theorems in Lean as run.
The unrelated `brief-sol.md` was left untouched. Older rejected gates remain under `runs/` for provenance;
use only the final `lazy-*` reports above for acceptance.
