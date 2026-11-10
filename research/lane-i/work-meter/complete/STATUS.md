# Raw accounting source verified and frozen (not integrated)

Source `9a36137ece0525d077ecf4509b686b2e6bdf3058` on
`claude/lane-i-complete-raw`, tree `2a21332d3fb0717cf0d4f0f3ba502ffd4d1f9a22`.
Original models: `0541fa9436e307a6fb716aa5064637b30b893b79`.

- `20261110-201003-umjycw`: original retained 29-chunk artifact materialized
  on boat and hash-verified; 982162 bytes, 1626 allocation sites, 78 files.
- `20261110-201047-bdfcqp`: 132 selected tests, erasure, roster, decoder pass;
  zero/double/random suites each 267 pass. Original plain-job TS2307 in
  staged tooling is retained, not rewritten as a clean first attempt.
- `20261110-201440-608dz0`: corrected tooling on unchanged candidate source
  passes erasure, roster, decoder and type/lint; selected tests not repeated.
- `20261110-201859-i4jf59`: source hashes, compressed receipt hashes and
  exercised mutation controls independently audited on boat.

Ledger/boundary/bitmap composition is in flight. Full raw coverage, F3,
calibrated weights/W and original-model repeated cross-CPU census are still
not complete. The active integration branch has no production changes.
