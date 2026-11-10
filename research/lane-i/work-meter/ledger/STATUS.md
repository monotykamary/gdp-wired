# Resumed — constructor/ledger composition checks running

The isolated pre-constructor ledger passed 39 tests, roster, decoder,
type/lint and source/receipt audit at the pause. Those receipts are retained.

The raw constructor source is now verified and frozen at `9a36137e`.
`recovery/compose.ts` applies only the ledger delta over that source with
three-way per-file merges; unresolved conflicts are failures, never silently
resolved by dropping constructors or phases.

Current batch: `20261110-201507-9tl8lf`, results
`runs/lane-i/resume-composition-validation`, task
`23d241b4-e68b-4762-aec9-19ac8b2b8ea2`. The first ledger-only job returned
exit 0 (74.79 s); its compressed receipt audit and the boundary/bitmap jobs
remain pending. No composed source is promoted yet.

Historical coefficients are unchanged. Extra weights remain explicit test
fixtures, not calibration. Full coverage, F3 and the all-29 census remain open.
