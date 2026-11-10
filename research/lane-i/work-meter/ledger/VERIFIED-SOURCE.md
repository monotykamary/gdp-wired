# Verified raw-ledger composition

Commit `feeaccf26f945b8ec9ff19990ffe32e72023ec2c`, branch
`claude/lane-i-complete-ledger`, tree `8b74e9043c5712be7a80c3eb943943d16fcd85f1`.
Parent `9a36137ece0525d077ecf4509b686b2e6bdf3058` (verified raw observations).
Original model blob remains `0541fa9436e307a6fb716aa5064637b30b893b79`.

Six files change: the raw/weighted projection, inclusive/exclusive phase ledger,
ledger tests, its counts/prover integration and test roster. The twelve old
coefficients and their summation order are preserved. Extra coefficients are
an explicit caller-provided API, with no default fitted weights and no W.

Checks: `complete-ledger-checks`, batch `20261110-201507-9tl8lf`, all 151
selected tests, checker erasure, roster, decoder, type/lint. Independent
source/receipt audit: `20261110-202057-8r5tcl`. Exact source re-export (no
constructor regeneration): `20261110-202144-a5gfj2`. Transport hash audit:
`20261110-202257-o544wu`, 993568 bytes, 29 chunks, SHA-256
`0b428fa7e0ed2d0f7ca673e7f4d1d627be44b322c1955d49d0a530eb968cb752`,
identical to the tested source.

This source does not yet contain the later boundary/bitmap additions, and is
not merged into the integration branch or qualified by the full final gate.
No F3/complete-coverage, cross-CPU census, calibrated weights or W claim.
