# Section46 source-review boundaries (unvalidated candidate)

No activation or new b0/F policy. `runCountRecipeController` still uses the flat retry planner. Explicit disjoint owner forwarding is staged only. No test, compiler, model or native pass is claimed for this candidate.

## Search work versus closing

Adapter context encoding, pass construction and lookup/target preparation are inside `beforeClosing`. Initial graph construction, selection/closure scoring, reserve calculations and post-result graph recomputation are inside a live search endpoint. Search exhaustion unwinds before final closing. Closing builds conservative S using `countRecipeRequirements`, the same function used by the graph, rather than trusting a possibly stale graph. It traverses only held premise edges and invokes the unchanged native replay/check path; it cannot start another recipe.

## F5: why production has no external checked basis

The pass contains every law in the adapter's complete ordered `set`, not only selected strategies or the target closure. `countPrerequisiteSchedule` gives each member an ordinary recipe. Known strategy requirements are emitted by `family.filter(l => offered.has(l)).map(l => l.name)`; thus only members of this same family become known edges. The adapter adds operation case keys, never outside premise names. This planner emits no synthetic external `closed-family` basis recipe.

Held scopes are captured over that same set. `scopeCountProof` validates declared premise names against the family, rejects external/duplicate names and verifies that actual native-obligation references are not omitted. Previously closed members remain held pass members, not externally assumed facts. Therefore the present adapter legitimately passes no external basis. The graph must continue to block malformed external requirements. A future external-basis path needs independently checked evidence and native controls; adding arbitrary names is forbidden.

## Fixed inventory across contexts

`countScopeContextKey(machine, laws)` is a metered ordinary-data encoding of the entire machine and ordered law array, including field values, keys and array positions/length. It is not merely a list of law names.

Production reuses a pass only when that key equals its original key. On a different machine/formula/ordered-family context it returns unproven before invoking the controller: it does not regenerate members, rebind recipes/case keys, clear terminal tickets or call the standalone `reconcile` API to bridge incompatible inventories. A smaller-to-full fallback can therefore conservatively remain unknown. This is not a completeness/performance claim.

Structured mode affects ordinary request representation, not the structural planner's inputs or case inventory. Re-entering with the same machine/law key never creates fuel or restarts terminal instances. If structured mode later changes the inventory itself, extend the identity or refuse reuse.

## Disjoint atomic-start contract

`countDisjointContext(tickets, bank)` records the actual ticket and ledger objects, parent scope id/epoch and started-generation. Plans retain rootEpoch too. `runDisjointCountRound(plan,tickets,run,bank,eligible?)` checks identity/context before entry; paid body metadata runs eligibility and rechecks scope/generation before committing a ticket. Foreign ledgers, matching-sized sibling scopes, old generations and false eligibility start no producer/new ticket.

Logical owners use the existing bank's scopes, not a borrow/release API. Repeated body/case segments are cumulative. Case and body cannot overlap. A leaf must have its actual owner; body-owned leaves/body stops/ancestor ties are hard. At most one authenticated failed physical slice is retained.

The runner withholds four tick units within the existing body cap for terminal entry, classification/coverage, ticket settlement and receipt preparation. Productive body segments cannot consume that tail. Success and interruption settle tickets in the terminal body before the receipt is sealed. Receipts include the terminal work. If even this tail cannot run, no free cleanup grant is manufactured and any active ticket stays unusable. This is control-plane accounting, not b0/F selection.

## Immutable ledger and open proof obligations

Underlying ledger is unchanged from committed `ab99a14d152c9adbf7b2d8bb6e3cbd51de545985`, tree `6ec367927e588230ede05a93863521d7861b352e`; `core/work-admission.ts` SHA256 `a0161d26d4dee4fe019982dc2eaca098d9a020ddd34ea03aff2915435c7720bf` (last touched by `4f7d4c1b44ceeb951dcac0448d2887cc8108bc86`). This does not transfer any older f585 proof.

K's acquisition-prefix obligation remains open: `withChunk` adds state/increments held/calls invariant/freezes the lease before entering its cleanup try/finally. Section46 does not prove those operations nonthrowing or repair that prefix. Cleanup postdominance alone is insufficient. Full M1/source-model coverage, new regression/native controls, exact half-law inventory and immutable-pin review remain pending.
