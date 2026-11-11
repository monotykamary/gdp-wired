# Lane I checkpoint — 2026-11-11

Main checkpoint `55c8ed96`. No production kernel merge or calibrated W.
Do not restart completed batches. Leave `.reflex-saved/` untouched.

## Closed EPR preflight diagnosis

Original consensus_epr on frozen cd00524f, unchanged inputs and diagnostic
all-one extra weights: small.bfs consumes 12,782,447 / 47,782,487 units at
15M / 50M allowances. Initial rule.refute-by-runs is 2,216,476 in both.
Guards 158; other small setup 39; law construction 25; other prove work 1,017.
No EPR is reached. Full raw events are retained in
`runs/lane-i/epr-preflight-split/receipts/`. Both raw vectors and verdicts
match the original unsplit runs. Lane A's exact handoff is in runs/REPORT.md.

## Weighted F3

Raw heartbeat is insufficient when coefficients may be zero. Atomic monotone
unit snapshots and publisher controls passed; the global-seqlock starvation
failure is preserved. 25 tests / 48 assertions and type/lint passed; the
latest typed check after the reconciliation driver covers 1,741 files.
Node live silent/zero-price/priced controls passed with archived profiles.
See UNIT-OBSERVER.md. This is not Bun/reference-host/full-original F3.

Extended native profile batch 20261111-021337-yl5wyh completed: exact original
raw/result/phase equality, 49,327,232 spans, no overflow, two timestamp-valid
stable raw windows, zero accepted native spans (both returned during capture).
Three complete profiles including an invalid profile are retained; independent
archive/hash/window reselection passed at `runs/lane-i/native-extended/audit.log`.
Do not reinterpret the changing operation fence as accepted attribution.
Original certFor/walker windows remain open. Next instrumentation would need
to retain an operation's completed interval, not weaken the fence.

The corrected extended identity check passed in 20261111-022047-wua0xx:
103 cases, 388 calls, original/wrapped-off/wrapped-on result and raw equality,
and composed-source type/lint. Prior fixture typing failure remains retained.
All owned batches are now terminal; the successful profile was not rerun.

## Kernel reconciliation

B69b8ef2b/Fcd671ac1 overlays passed both source checks and selected tests at
20261111-021552-pnmybx. Exact common kernel tree db5bc38ac2e08e25d392d7a7daa748c7a6c8245a;
Lean tree b9039b851d59b7621e322a797096fcd724019f68. Unpatched F fails all three
frame-only exporter columns; B and both patched trees pass. Patches and
reproducer are in research/lane-i/kernel-reconcile/. TWO semantic changes
were flagged to D BEFORE MERGE (CDCL alias orientation, frame-only exporter
columns). Wait for that audit before promoting; continue independent work.
Full B/F source integration also must merge extraWhen and deferCheck correctly.
The active integration trusted kernel is older, so copying five files alone
would not be a valid combined source. Mini's running calibration must not be
repinned implicitly.
