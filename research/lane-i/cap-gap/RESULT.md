# Cap repair and scoped A integration — ready for D review

**Exact tested source:** `17119b508485c0f0d104c71df28b11e5f48656d2`,
`claude/mldr-integ`, descending from `00b58ee5`. D composition approval and
final calibration remain pending.

## Cap repair

The I6 crossing spent **154,479.9744 units between polls**, including 151,706
table units, in row construction and open-atom discovery (`LOOPS.md`).
The repair changes only untrusted proof search: four full-profile-only
traversal checks and a checkpointed row proposer. The checker still uses its
unchanged reference construction and acceptance. Rows are charged on append:
cancellation cannot lose pending observations or cache a partial row result.
Flags-off retains the original builder and skips all four new checks.

| 15M measurement | Before, I6 | Final source |
| --- | ---: | ---: |
| sharded_kv | 15,120,328.2561 | **15,000,018.2817** |
| corpus maximum | 15,120,328.2561 | **15,000,276.18** |
| maximum excess | 120,328.2561 | **276.18** |

Allowance: **1,024 provisional raw-work-v1 units**. Worst final case is
`paxos_epr`, stopping at `inference sample`. sharded_kv returns its own unknown
outcome: `work budget (row cell pair)`.

## Final gates — native Boat through supercomputer

- **20261111-050507-9xdfen: 58/58 jobs pass** on the exact source: 28 strict
  pre-import-tripwire originals, 28 flags-off originals, native tests, static.
- **162 suite tests / 3,145 assertions pass**. Two native deadline controls
  are explicitly skipped in legacy mode, then included in the separate
  full-work group: **9/9 controls / 28 assertions pass**. Row tests compare
  480 mixed path contexts, cancellation/no-refund, an uninterrupted negative
  control, and retry after cancellation.
- TypeScript and type-aware lint: **1,808 files**, zero errors/warnings;
  explicit test roster complete.
- **132 protected identities** match pre-cap `48cd625c`, including
  `kernel/kernel.ts`, `core/check.ts` and all Lean files. The two existing-file
  exceptions in this manifest are untrusted prover code.
- Independent audit **20261111-050850-qqivwk** validates all 56 receipt hashes,
  exact source/baseline/profile, ordered schema, weighted totals, root and
  exclusive ledgers, integral nonnegative raw counters, zero forbidden clock
  reads and the cap. **10 proved and checked, 18 unknown; every I6 proof and
  result preserved, no new refutation. All 28 flags-off normalized receipts
  unchanged**, with the added native counters zero. `AUDIT.json` has all rows.
- Commitlint **20261111-050843-f74pko** passes the six new source/test messages
  and planned evidence message.

The no-loss baseline is **I6 `1066f267`**, not the earlier 12-proof `00b58ee5`
census. Its two accounting-driven bounded changes remain in `../i6/CAUSAL.md`;
this repair introduces no further lost proof.

## Scoped A port

`046e5ae3` ports `9b7485e5`'s exact local-expiry helper and qualified catch,
with compatible optional factory parameters. `A-PORT.md` gives the scope.
Active/inactive, public/phase, nested-scope and unrelated-error controls pass.
D's later-external-deadline limitation is deliberately reproduced.
**The full A generation/strategy/rejection pipeline is not imported**; no
current common-tree production caller supplies an active tier plan. Its
closure and original-MLDR progress gate remain outstanding.

## Artifacts and limits

`hard-cap.patch` is the three-file untrusted delta; `a-local.patch` the two-file
A port; `combined-production.patch` the complete eleven-file runtime delta
since `00b58ee5`. Also see `D-HANDOFF.md`, `SOURCE.json`, `AUDIT.json`, `results/`.

Failed initial gates are retained: a research-script namespace collision,
legacy expectations copied from full-mode controls, and a one-column charge
assertion initially expecting two. The first proposer also required append-time
observations to retain work on cancellation. None is a successful final gate.
The first census submission refused an archive still being prepared; it was
resubmitted after hashes stabilized, before any measurement ran.

No checker shortcut, wall fallback, price/schema change or counter refund.
D's `a0e281ee` provisional reference is source-bound to `00b58ee5`; it cannot
transfer here. Refit/recheck the cap on final prices. This finite census is
not an instruction-level proof for arbitrary-size unchecked inputs or
still-unported B/F paths. No final W, original-MLDR success, B/F GREEN
promotion, main merge or push is claimed.
