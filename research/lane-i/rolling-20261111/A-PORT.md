# A local-first premise factory stage

Approved source: `5dec706542a2c97993589f47f89e0ce5fe208188`.
D source decision: `research/verify-all/lane-a-premise-local-0e5014b4/DECISION.md`.
Exact tested B+K3+A tree: `88c25052120348355888613456865d3142cb4529`.

The port adds A's family containment API and local-first scheduler to the
existing `countedAttempts` factory. B's fixed-operation premise API remains
compatible. A's recognizer is local rather than importing the frame strategy.

When tiers are active, selection and both local trials share the first 3/4 of
the existing attempt allowance. Only a transported and natively checked proof
for the complete original family can be retained. Local refutations/unknowns
cannot become whole-family verdicts. The remaining quarter is reserved for
the full-context fallback. A stale narrowed model is not reused as if it covered
a newly widened family. With tiers inactive, I's existing path is unchanged.

I's enclosing end, qualified local-expiration catch, clock, counters and final
checker remain untouched. The known inherited limitation for an enclosing
external deadline installed later than factory construction remains; this port
does not claim to fix it.

## Local gate, not combined admission

Boat batch `20261111-071350-xzj09m`:
- 16 containment/factory tests, 52 assertions.
- 44 B/A API, scope, tier and clock tests, 639 assertions.
- Type/lint clean across 1,926 files.
- Every driver verified all 181 protected identities.

Receipts: `results/A-pilot/`. The final default-off28, enabled-route/full-family
checks, D composition review and exact-pin calibration remain pending.
