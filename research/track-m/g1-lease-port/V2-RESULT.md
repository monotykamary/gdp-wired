# Corrected source-gate V2: PASS

- Batch `20261112-003202-ivxcia`, submitted source tree `bed0b22a07c8` (6544 files).
- 32 tests / 173 assertions / 0 failures across the G1, replay, deferral and exact-lease suites. Five added tests force the production fresh-load fallback with a real rebase miss and verify its options/native behavior.
- Whole-tree `tsc -p .`: PASS, including the paired constructor, portable binding helper and fresh native replay harness.
- Type-aware oxlint on all three changed core files: PASS, 100 rules, zero warnings/errors.
- Both child commit-message files: commitlint PASS.
- Bun 1.4.3 executable SHA256 `7ce7d6b654eddeec20afddf2396317fba6dc19ab52788a27e894e1806bf8f24b`, runtime verified and stable.
- Exactly one strict-once attempt, no reconnect, no fallback, zero starts charged to this batch. Runtime/custody/output artifacts at `runs/lane-f-g1-replay-lease-source-v2/`.
- Terminal SUCCEEDED/code 0; admission closed, journals retained, cleanup_complete=true. Close receipt SHA256 `4fc192e2ef4aec3135d3b4dbac8ba37851c7e9a271319ddc13133f6ae479c75a`.
- Output manifest SHA256 `9b03226bec61991fb3694fee606925e04b31d29d439f1fc58f28a25d5b1dd02f`; immutable exported logs retained.

This is a source gate, not a native 19-law result or a timing/budget qualification. No paired native launch or production activation is implied.

V1 remains a separate retained FAIL; see `V1-RESULT.md`.
