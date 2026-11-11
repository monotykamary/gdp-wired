# D-admitted common kernel and counted-integration boundary

Lane D's receipt **723773616f222d68db21414a5dcbc7cbaa11b05d** admits the
B/F reconciliation at B `69b8ef2b` and F `cd671ac1`:

- Entire `kernel/`: `db5bc38ac2e08e25d392d7a7daa748c7a6c8245a`.
- Entire `lean-kernel/`: `b9039b851d59b7621e322a797096fcd724019f68`.
- Trusted checker: `6f6c9526003afcfc3ea1e48106ee44b4bf8649fd`.
- Materialized common source: `becd98e30bf4b7df29217fa820b82b7aa259bf28`.

Both full subtrees, not five selected files, are integrated into
`claude/mldr-integ` and `claude/mldr-candidate`. No extra kernel files and no
A-specific kernel/prove.ts, meter.ts or work-budget.test.ts are retained.
This removes the current candidate's PENDING-D status for reconciliation.
It does not grant full strategy, MLDR, release or W approval.

Clock receipt **565ecd01b0f6c388650031beabf05259e81a741e** independently
admits **353713c9 only on parent 5aa76818**. Its checker has a different
identity (`5a5973de`). These approvals are not interchangeable.

The former measured candidate `db14ee14` used the admitted checking sources
but retained three A-specific kernel files. Its saved runs remain diagnostic
measurements of exactly that historical hash, not of the exact common tree.
They must not be silently relabelled or reused as current-tree validation.

Integration hypothesis to test: the exact common kernel lacks A's raw-meter
module and counted API exports (`withBudget`, `checkBudget`, `inWorkScope`,
`searchNow`, `wallAt`). Therefore restoring D's whole tree will expose a
counted-integration API gap even though the two changes are separately sound.
Do not hide this by replacing the common prover, adding kernel files, or
modifying a checking path. Report validation evidence and the boundary to D/A.

Original receipts:
`../gdp-wired-verifyP/research/verify-all/kernel-reconcile-20261111/RESULT.md`
and `../gdp-wired-verifyP/research/verify-all/clock-scope-353713c9/RESULT.md`.
No main merge or push.
