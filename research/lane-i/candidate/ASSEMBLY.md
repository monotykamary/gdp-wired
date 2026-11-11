# Candidate assembly — D kernel admitted

## Current exact-tree checkpoint

- Integration branch: `be661632` on `claude/mldr-integ`.
- Candidate branch: `7eccce26` on `claude/mldr-candidate`.
- D reconciliation receipt: `72377361`.
- Both complete trees are exactly `kernel=db5bc38ac2e08e25d392d7a7daa748c7a6c8245a`
  and `lean-kernel=b9039b851d59b7621e322a797096fcd724019f68`.
- No A-specific prover, meter file or scope-test exception remains in kernel/.
- Reconciliation no longer has a PENDING-D label. Full counted integration
  remains separately under test, not admitted by that label change.

See `KERNEL-GATE.md`: clock gate 565ecd01 admits 353713c9 only on A's exact
parent, not on the different common kernel. Never conflate these approvals.

## Historical measured checkpoint (preserved, not current validation)

Pins: A 5aa76818; B 8ad0072f; F 9a3e3792; clock 353713c9.
Clock cherry-pick 93e4e3bf; B merge 915ab320; F merge c317a75a; compatibility
fix db14ee14. This historical source had three A-specific kernel exceptions.
It passed 86 focused tests, the full-work tripwire, and type/lint on 2,036 files.
Original consensus proved+checked. MLDR at 15M stopped in generation after
4,424,579 search units; no proof query was reached. Its census and wider
allowance diagnostics retain that exact hash; they are not reused as evidence
for 7eccce26.

## Non-kernel conflict decisions

- A: full-work scopes, counters, bounded generation, late recovery, telemetry.
- B: strategy selection, shared tier endpoint, ordinary fallback, exact
  count-definition admission, leaf cap options, deferred/minimal frame views.
- F: lifted load/copy modules, provenance, guard-fact minimal views, branch
  ordering, carried-write classification, extraWhen, zero normalization.
- Keep both differing test versions with .lane-b/.lane-f names.
- Non-runtime research conflicts keep A/B versions; all F-only files survive.
- A's recovery-boolean / B's selected-law Set call forms are both supported.
- F's frozenTarget backwards-compatible helper export is restored.
- Experiment fixtures never supply the original model's final proof.

No main merge or push. Units are diagnostic, not calibrated W.
