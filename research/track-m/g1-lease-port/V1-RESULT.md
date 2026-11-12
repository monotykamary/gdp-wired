# Immutable source-gate V1 result

Batch `20261112-002903-3o1zlm`, submitted source tree `53983c8136dd`, source-only, strict once/max attempts 1. Completed one placement; zero starts charged to this batch. `runs/lane-f-g1-replay-lease-source-v1/` retained unchanged.

- 27 tests / 127 assertions PASS.
- Typecheck FAIL: exactly `core/count-g1-lease.test.ts(19,22)` TS2345, ExactRaw passed to compareWork instead of converting with workFromExact.
- Lint and commitlint did not run after the typecheck failure.
- No native paired draw and no production activation.

Corrected source is a new revision; V1 is not retroactively passed. The corrected revision also adds a direct production fresh-load fallback seam with a real rebase miss, forwarded-option checks, full-goal native acceptance, and invalid projection refusal.
