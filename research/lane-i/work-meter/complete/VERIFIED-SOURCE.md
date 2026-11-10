# Verified raw-accounting source (isolated)

Commit: `9a36137ece0525d077ecf4509b686b2e6bdf3058`
Branch: `claude/lane-i-complete-raw`
Tree: `2a21332d3fb0717cf0d4f0f3ba502ffd4d1f9a22`
Parent: `b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3`
Original models: `0541fa9436e307a6fb716aa5064637b30b893b79`

This freezes the already-collected raw accounting artifact, including its
isolated A2 work-entry changes. It is not merged into the active integration
branch and is not a complete-work or final-gate claim. Do not treat the entire
commit as only the constructor diff: the retained pre-constructor identity
and patch in this directory describe its prior raw/A2 state.

Evidence:
- Artifact hash/source validation: `20261110-201003-umjycw`, all 29 chunks,
  982162 bytes, SHA-256 `52571387a7f165ec76af1e34ea9fe06192abd43d555cd6aa78b2cef93c1734ba`,
  1626 allocation sites in 78 files.
- First validation `20261110-201047-bdfcqp`: checker erasure, 132 targeted
  tests, roster and decoder passed; type failed in the staged tooling's
  relative recovery import (TS2307), not in candidate production source.
  Zero/double/random mutation suites each passed 267 tests, with source
  unchanged receipts.
- Corrected tooling, same candidate source: `20261110-201440-608dz0`,
  erasure, roster, decoder and type/lint passed. Successful targeted tests
  were not repeated just for this tooling repair.
- First compressed-receipt hash audit: `20261110-201404-7rf4tk`.
  Expanded source/mutation audit is in `runs/lane-i/resume-complete-final-audit`.

No extra weight vector or W is selected. Ledger composition, bitmap coverage,
F3, original-model census and final gate remain separate pending work.
