# Scoped A 9b7485e5 port

Source `9b7485e5cb4a550497a2992e028c11779befc1b1`; D scope in
`lane-a-local-expiry-9b7485e5/RESULTS.md`. Integration `046e5ae3`;
final combined runtime `17119b50`.

The exact seven-line `isLocalCountExpiration` helper is added to
`core/count-tier-budget.ts`. `core/counts.ts` captures factory
`withinDeadline(until)` and contains BudgetExpired only for an explicitly
active tier plan and an expiry the helper classifies local. Unsupported
proposals and legacy wall expiry retain their logic. No checking/price change.

The former five-argument common factory gains compatible optional
`allowFocused` and `tiers` parameters. Existing calls retain defaults.
A's full generation/strategy/rejection dispatcher is **not** imported, and
no current common-tree production caller supplies an active plan. This is a
tested integration seam, not a claim that original MLDR reaches its second
ordinary attempt; that regression requires A's outstanding dependency chain.

D's controls are adapted to this tree's real `query` event rather than
`count-final-goal`. They cover active/inactive local expiry, public expiry,
a prior shorter enclosing phase, unrelated exception identity, nested local
scopes in both passes, and EPR classification. Prior-phase and later-external
native tests are full-profile-only; legacy checkBudget does not throw solely
for a local phase deadline. Those two skips in legacy mode are explicit.
Full-mode controls run separately.

D's known exported-factory limitation remains reproduced: an external shorter
deadline installed **after** factory creation can be contained as local. No
blanket claim that every later external cancellation propagates. Future
dispatcher integration must obey the scoped call shape or address it.

`a-local.patch` is the minimal runtime diff. Local composition still needs D's
gate: A's scoped GREEN is not approval of the combined runtime.
