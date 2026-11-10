# Verified finite-budget source

- Branch: `claude/lane-i-finite-budgets`
- Commit: `32a59b2a4cb38e60ee14cd54a2533bfee76bce89`
- Parent: `94b65671b0f81ccfd5e7be71686fc81f35387c94`
- Tree: `27b8a07cbd5500c7c7f7549df7d6f15fa41092ab`
- Full composed patch SHA-256:
  `8df0cf2ac466465a45683a639124d5f774e1b85b72d7f36c1b42b682c4e46fbd`
- Three-file delta SHA-256:
  `b3c8cd7b2b0d7990b81553d199d314ba3891254db18af5fe92367d721c584743`

The delta changes only `kernel/prove.ts`, adds
`core/work-finiteness.test.ts`, and registers that test in
`scripts/test-shards.ts`. Reversing those changes reconstructs exact parent
tree `1fe9fc742ebe0c4fa25fcf60916f37c54e7ccc37`.

## Evidence

- `20261110-215401-xhkj8q`: both overflow defects reproduced on `94b65671`,
  ordinary cutoff control passed, all 110 source blobs unchanged.
- `20261110-215908-wplx8m`: 169 selected tests, checker erasure, roster,
  decoder, and type/lint pass. Zero/double/random mutation runs each pass 267
  acceptance tests. All four complete 111-file source manifests are identical.
- `20261110-220315-mmyn0j`: the identical five-test regression fixture on
  unchanged `94b65671` gives exactly three required failures and two passes.
- `20261110-220408-fj9hms`: independent receipt hashes, source equality,
  negative-fixture identity and exact-parent three-file export pass.
- `20261110-220331-o8j51x`: audit-tool type/lint and commitlint pass,
  1,698 files, zero warnings/errors.

Original model blob: `0541fa9436e307a6fb716aa5064637b30b893b79`.
The integration production tree is unchanged. This closes the reproduced
nonfinite entry/completion cases, not all floating-point precision questions.
It is not an unbounded numeric proof, fresh F3/F4 qualification, calibrated
weights, W, or GATE GREEN.
