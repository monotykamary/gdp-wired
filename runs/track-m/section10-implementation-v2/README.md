# Section 10 — default-on implementation, before the family gate

Generic production changes:
- Equality consequents `cell[member] = cell[anchor]` are substitutions into a
  target count body. Known memberships and reflexive comparisons discharge
  conjuncts; only witness-free scalar residues become preferred source scopes.
- The outputs are ordinary `CountInst`s, not asserted bounds. Source proofs and
  conditional cut admission retain the required guards.
- At each numeric model, violated facts are selected in batches using the
  all-assumed core. Every selected source is attempted before the next plain
  numeric query. A SAT query over only the current violated subset is not a
  generator-gap verdict; those candidates can still provide checked progress.
- Source reuse zero-completes missing names and validates the entire source and
  scope. Local scalar splits share one absolute leaf deadline.
- Leaf draws use the exact existing `supportBudget` formula, factored without
  changing the law-level behavior: `min(remaining,max(remaining/leavesLeft,
  remaining/3))`. The existing row-case 1,500-unit cap can further clip the draw.
  No source/core/depth/total cap changed; no new budget is minted for children.

**Kernel and final certificate admission are unchanged.** F1 deferral and F2/F3
slicing/check caches remain default-on. No names from the protocol occur in the
new production mechanisms.

## Validation

`bun run check` passes (TypeScript + type-aware lint); **245 tests / 1,198
assertions** pass. The fixture's generic proposer emits three equality-derived
inclusions for Inv*, including r$4 <= r$16 with CT[i] < CfgT[j$], and four for
Inv2973. These are proposed facts, not a claim that every one checks.

One initial generic test caught treating membership `cell=1` as a cell-to-cell
substitution. The implementation now keeps membership facts separate; v2 passes
all tests. Earlier complete-implementation v1 is also retained; its partial-set
SAT stop prompted the generic two-inclusion progress test and correction.

## Negative active-probe result (not a gate)

Both full-pool op-5 probes used **bx_25xas5gt**, exclusive, eight pinned vCPUs.
Neither completes. In Inv*, one scalar subbranch checks, but another returns no
numeric model at the shared row deadline. Inv2973 exhausts the first row share.
The T-9D predicted early-leaf thresholds therefore **do not pass**.

| Probe | Remaining at first draw | Nominal draw | Existing row cap grants | Cuts admitted | Source calls: checked / SAT / reused / unknown |
|---|---:|---:|---:|---:|---:|
| Inv* | 4914.372555 | 1638.124185 | 1500 | 16 | 15 / 16 / 39 / 20 |
| Inv2973 | 4999.649654 | 1666.549885 | 1500 | 25 | 25 / 14 / 55 / 32 |

These are single diagnostic probes, not A/B performance ratios. Their complete
trace logs are retained. The original five-law harness is the next test, with
three interleaved repeats against exact 50109a36. No later gate has run.
