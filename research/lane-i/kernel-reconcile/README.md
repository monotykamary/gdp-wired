# B/F common-kernel reconciliation — pending lane-D audit

Inputs: B `69b8ef2b`, F `cd671ac1`. This prepares and tests a common overlay;
it does NOT merge either strategy lane into `claude/mldr-integ` yet.

Both lane inputs have trusted `kernel/kernel.ts` blob
`6f6c9526003afcfc3ea1e48106ee44b4bf8649fd`. The active integration branch
still has an older trusted kernel; a five-file copy is not full integration.

## Semantic choices submitted to lane D

1. Keep F's `831d89dba` fix: derive CDCL root orientation from the actual row,
   not from the path map's potentially aliased key. Retain its three regressions.
2. Keep B's exporter registration for frame-only condition columns (cell,
   term and monomial). F omits it. The new three-case regression must fail on
   unpatched F and pass on unpatched B plus both patched sides.
3. Keep B's stronger frame-activation assertions; correct the README's stale
   claim that TypeScript frame cuts are not wired.

`B.patch` and `F.patch` produce EXACTLY the same kernel and Lean subtrees:
- kernel: `db5bc38ac2e08e25d392d7a7daa748c7a6c8245a`
- lean-kernel: `b9039b851d59b7621e322a797096fcd724019f68`
The whole trees differ because the strategy code differs. `trees.txt` pins both.
`SHA256SUMS` records the initial source packs and patch bytes.

`prepare.sh NEW_DIRECTORY` rebuilds the packs/patches without touching the
working index or a production file. `verify.jobs.json` runs each lane source
with `verify.ts`, checks the three-case baseline differential, applies its
patch, verifies the common subtree hashes, then runs duplicate-root/frame/
export/helper tests and full type/lint. Batch: `20261111-021552-pnmybx`,
`runs/lane-i/common-kernel/`. Both sides PASSED: the three-case baseline
control passes on B and fails all three cases on F; after the overlays,
all selected kernel/export/helper tests and full type/lint complete on both.
The source-bound `COMMON_KERNEL_CHECK` records the equal subtree hashes.
These checks do not substitute for lane D's semantic audit.

A full B/F merge has additional conflicts. In particular `count-frames.ts`
must retain both B's deferred untrusted pre-check option and F's `extraWhen`
conditions/zero normalization; neither may be silently replaced by the other.
The final kernel still checks every admitted certificate. The merge preview
alone is not a tested combined strategy source. Lane D must audit the two
semantic kernel-adjacent choices before a production merge or repin.
