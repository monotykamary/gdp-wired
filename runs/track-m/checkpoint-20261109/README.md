# Paused Lane B checkpoint — 2026-11-09

User requested an immediate pause. No new batch or validation was started.

## Cancellation inventory

- Exact task **1d02306c-85e3-46cc-848a-8a55e2a6d00a** (PID 23225), batch
  **20261109-154233-07us9f**, output **runs/track-m/lane-b-range-final-audit-v1**.
  Purpose: four new p1 certificate replays, the corrected Inv1758 unknown replay,
  final source validation, and the consolidated 13-record receipt projection.
  The task is killed; the exact batch was closed through the scheduler's
  batch-scoped API and is absent from status, with no running items.
  No job output was collected, so there are no usable partial final-audit results.
  Rerun all three jobs only after the user resumes.
- Three stale, single-item submissions registered to `gdp-wired-trackM` were also closed by exact batch ID: **20261109-000842-7lxjwd**, **20261109-001003-ts9wn1**, and **20261109-120151-t1kpp9**. Their original shell-task IDs, output directories and exact purposes are not present in the retained task registry. They are not usable evidence for new claims and must not be blindly rerun. The scheduler returned successful close receipts; all owned batch registrations and running items are now absent.
- No other live background task owned by this session remains. See `cancellations.json` for all four exact batch IDs and the available metadata.

## Completed, reusable evidence

`00a7d516` records all nine completed measurement archives' manifests, logs,
hardware placements and the first eight-record independent audit. Do not rerun
valid measurements just because the final audit was cancelled.

- Inv1758 remains unknown, including early focused and dual-clock experiments.
- Inv* remains unknown with active per-read ranges in both execution orders.
- p1 is worker-checked in all four paired arms; range seeding changes its cost
  from 2,175.512 to 2,295.746 units, still under 6,000 units / seven seconds.
- The earlier eight-record independent audit passed (one p1 certificate,
  seven reconciled unknowns). The remaining four p1 certificates and one unknown
  are not independently accepted yet.
- Finished integration passed typecheck/lint and 17 tests / 65 assertions.
  The later expanded projection script's final check is still WIP.

## Large local outputs (not in the current Git tree)

Keep the existing `receipts.tar.gz` files under:

- `runs/track-m/lane-b-range-pair-v1/receipts/{star-ab,star-ba}/`
- `runs/track-m/lane-b-early-focus-v1/receipts/{rows-only,rows-third,rows-classes,p1-base}/`
- `runs/track-m/lane-b-range-followup-v1/receipts/{p1-ab,p1-ba,rows-third-wall}/`

All nine have already been fetched and SHA-256 verified. Their committed
`archive-manifest.json` files identify each archive. Expanded raw receipts and
staged `lane-b-range-final-audit-input` / `lane-b-projection-input` directories
also remain local/ignored. Preserve or copy these before any clean/reset or
moving to a different machine. Existing historical commits are not rewritten.

The exact next commands and open blockers are in the top RESUME section of
`runs/REPORT.md`. The research early-entry policies remain unadopted.
