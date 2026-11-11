# Lane D handoff — bounded common source 17119b50

Review **17119b508485c0f0d104c71df28b11e5f48656d2**.
Prior common production: `48cd625c` (same I6 runtime as `1066f267`).
Local results: `RESULT.md`; full census: `AUDIT.json`.

## Minimal new runtime deltas

1. `hard-cap.patch`: untrusted `kernel/prove.ts`, `kernel/prover-rows.ts`,
   and new `core/prover-row-budget.ts`. Four checks are full-profile-only.
   Row construction polls inside the call and charges rows on append.
   The checker still uses its own unchanged reference rows.
2. `a-local.patch`: exact A `9b7485e5` helper in `core/count-tier-budget.ts`
   plus the qualified catch/captured endpoint in `core/counts.ts`, with
   compatible optional factory parameters. No generation dispatcher import.

`kernel/kernel.ts`, `core/check.ts`, Lean, raw observer implementations,
work schema/weights and admission arithmetic are byte-identical to pre-cap.
The manifest verifies 132 identities; its two intentional existing-file
exceptions are untrusted prover code, not checking rules.

`combined-production.patch` includes the earlier admission and I6 layers
since `00b58ee5`, not a claim they were already composition-GREEN. It covers
all eleven changed runtime files. SHA-256:
`ace5c950b00b5858ba3bccb40bf1e44491480352ace5af44949d8a384a6a3d0e`.

## Local evidence

Exact-source batch **20261111-050507-9xdfen**: 58/58 jobs pass; 162 suite tests
plus 9 full-mode controls; 1,808-file static check; complete roster.
Independent audit **20261111-050850-qqivwk**: 56 source-bound receipts,
10 I6 proofs retained, 18 unknown, no new refutations, no forbidden clock
reads, 28 flags-off receipts exact. Maximum **15,000,276.18 <= 15,001,024**;
sharded_kv **15,000,018.2817**.

Please gate this combined source, especially partial-row charging,
cancellation/cache restoration, reference row equality and the active-plan
catch. A's known exported-factory later-external-deadline counterexample
remains explicitly tested; scoped approval is not universal cancellation
preservation. No current production caller passes the optional active plan.

No fit transfers from the provisional `00b58ee5` reference. Reprice/recheck
on the final integrated source. No B/F source is promoted without its actual
GREEN closure. Local completion is not D approval or a final W claim.
