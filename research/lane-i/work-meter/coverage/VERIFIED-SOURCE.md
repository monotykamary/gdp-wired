# Verified canonical-key accounting source

- Commit: `41d39043a75e279dc9600e6a33c8107014b67025`
- Branch: `claude/lane-i-complete-canonical`
- Parent: `84ffacf2be0364ab2ee0758405d779c027338c56`
- Tree: `1938f7d70a7ed5fb0369a0e76e2e0c2b5a113131`
- Original model blob: `0541fa9436e307a6fb716aa5064637b30b893b79`

The three-file delta adds discarded `tableCells` observations to existing
canonical-key lookup/serialization, coefficient inspection and key parsing;
three exact cold/cache counter tests; and their test-roster entry. It changes
no formulas, sorting, cache decisions, acceptance branches, weights or W.
The trusted checker is structurally identical after instrumentation erasure.

## Receipts

- Source checks: `20261110-203555-pkp0td`, 158 selected tests, erasure,
  roster, decoder and type/lint.
- Noninterference: `20261110-204037-4iirg6`, 267 acceptance tests each
  under zero/double/random counter mutations. Exact counter fixtures remain
  required in the plain suite; they are intentionally separate from mutation
  controls. Independent control audit: `20261110-204453-7zv6lt`.
- Exact source transport and receipt audit: `20261110-204538-t42ntt`.
  1017509 bytes, 30 chunks, SHA-256
  `f59720c766a68a2647cb150c6f3e0793363aa36804eb6bc3185430488f0eebe0`.
- Node original-MLDR off/on pilot: same raw vector and same `unknown`
  (`work budget (completion)`) result. Every raw component reconciles with
  nonnegative exclusive phase totals. Strict sampler: zero stable reported
  windows, nine changed-during-capture windows. These are not proof of full F3.

No full 29-protocol/cross-CPU census, Bun F3, calibrated vector or W claim.
Not merged into the final-gate integration. All earlier failures remain logged.
