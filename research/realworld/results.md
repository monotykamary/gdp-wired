| Domain | Items | Fully expressible | Laws | Proven | Refuted | Unknown | Timeout |
| --- | --- | --- | --- | --- | --- | --- | --- |
| auth | 4 | 0 | 23 | 19 | 0 | 4 | 0 |
| access | 4 | 1 | 27 | 24 | 2 | 1 | 0 |
| approval | 4 | 0 | 24 | 15 | 0 | 9 | 0 |
| inventory | 4 | 0 | 19 | 10 | 4 | 5 | 0 |
| ledger | 4 | 1 | 27 | 15 | 0 | 12 | 0 |
| payment | 4 | 0 | 23 | 15 | 3 | 5 | 0 |
| circuit breaker | 4 | 1 | 30 | 21 | 0 | 9 | 0 |
| queue | 4 | 0 | 26 | 18 | 0 | 8 | 0 |
| feature flag | 3 | 0 | 18 | 17 | 0 | 1 | 0 |
| quota | 3 | 0 | 17 | 11 | 1 | 5 | 0 |
| rate limit | 7 | 0 | 30 | 15 | 3 | 12 | 0 |
| xstate | 6 | 0 | 47 | 38 | 2 | 7 | 0 |
| **all** | 51 | 3 | 311 | 218 | 15 | 78 | 0 |

- Items: 51; fully expressible (every part of the step said exactly as the code does it): 3 (5.9%); with no language gap (what is left out is by choice or held by another system): 9 (17.6%); none of it: 0.
- Laws: 311 stated (311 run), 10 more a reviewer would ask that the language can't state; proven with nothing stated: 218 (70.1% of those run, 67.9% counting the unstated).
  - safety: 70 / 100
  - liveness: 0 / 35
  - access: 32 / 35
  - step: 116 / 141
- Median time per law: 664 ms over all laws run, 657.5 ms over those proven.
- Refuted: 15: real bugs 15, modelling errors 0, law errors 0, not triaged 0.
- Not proven nor refuted: 78, of which:
  - 31: not inductive alone, and the search found no invariant that proves it
  - 28: liveness: no rank found (no helpful step sampled lowers a linear rank)
  - 7: liveness: a rank fitted to the runs, the kernel's goals not proven with it
  - 7: the prover's budget ran out on a goal (a wide rule)
  - 4: a step law broken from a state no run was shown to reach (it needs an invariant)
  - 1: the library threw
  - (13 of them are laws the original code breaks, each shown by a repro: the search found no run within its budget)
- Proven only through the search's finds (invariants, lemmas, a rank): 26 of 218.

| Gap | Items | Laws it blocks | What |
| --- | --- | --- | --- |
| (scope) | 23 |  | not a language gap: a part of the code left out of the rule by choice (an option, an admin path, a setting fixed for a run, a value shape simplified) |
| (external) | 21 |  | state held outside the code read (a database query, Redis script atomicity, another service) |
| async | 19 |  | concurrency, promises, timers or events firing on their own (a timeout, an interval) |
| float | 16 |  | non-integer arithmetic: binary floating point (Math.floor of a float, a rate in tokens per ms), or decimals of unbounded precision (BigNumber quantities) |
| unbounded-collection | 8 | 3 | a collection read in ways maps, sets and logs do not give (sorting, min over a list, nested scans) |
| nonlinear | 7 | 3 | a product of two unknowns the prover does not decide (rate × elapsed time) |
| chart-subset | 6 |  | a statechart construct chart / fromXState does not take: invoke, after, always, inline guards and actions, entry/exit actions writing the context, a parallel state below the root |
| string | 5 |  | strings compared other than for equality: globs, regexes, prefixes, parsing |
| hash | 3 |  | a hash function (murmurhash, sha) the rule can only take as an uninterpreted input |
| recursion | 3 | 4 | recursion over a structure the rule would need a lemma about (role inheritance to any depth) |
| dynamic-policy | 2 |  | a policy that is data loaded at run time (a model file, policy text) rather than code |
| two-key-map | 2 |  | a map keyed by two values (a mapping of mappings, a link table), encoded as one key |
| time | 1 |  | wall-clock time read inside the step (Date.now()) rather than sent in with the request |
| two-run | 1 | 2 | a law comparing two runs of a rule (stickiness as the params change), not two requests of one run |
| batch | 1 |  | a batch of operations that succeed or fail together (linked events, a transaction rolled back), or one operation over every due record |

| Item | Law | Kind | Intent | Outcome | ms | What the search found, or where it stopped |
| --- | --- | --- | --- | --- | --- | --- |
| auth/better-auth/twoFactorOTP | at most allowedAttempts guesses are compared per code | safety | docs | proven | 12648 | never has is yes and isLocked is yes and ok is yes; isLocked is yes and ok is no → has is yes → compared <= attempts; isLocked is no and ok is yes → has is yes → compared <= 0; isLocked is no and ok is no → has is yes → compared <= attempts; never has is no and isLocked is yes and ok is yes; isLocked is yes and ok is no → has is yes → 1 <= lockOn; never has is no and isLocked is yes and ok is no |
| auth/better-auth/twoFactorOTP | a code is accepted at most once | safety | docs | proven | 9630 | never has is yes and isLocked is yes and ok is yes; isLocked is yes and ok is no → has is yes → accepted <= 0; isLocked is no and ok is no → has is yes → accepted <= 0; isLocked is no and ok is yes → has is yes → accepted <= 0; never has is no and isLocked is yes and ok is yes; isLocked is yes and ok is no → has is yes → 1 <= lockOn; never has is no and isLocked is yes and ok is no |
| auth/better-auth/twoFactorOTP | an expired code is never accepted | safety | docs | proven | 561 |  |
| auth/better-auth/twoFactorOTP | a locked account accepts no code | access | docs | proven | 983 |  |
| auth/better-auth/twoFactorOTP | maxFailedAttempts failures lock the account | safety | docs | proven | 768 |  |
| auth/better-auth/twoFactorOTP | a right code clears the account's failures | step | docs | proven | 1107 |  |
| access/node-casbin/effectorStream | allow-and-deny: any matching deny denies | safety | docs | proven | 6740 | never done is no and res is no and rec is yes and sawAllow is no and sawDeny is yes; never done is no and res is no and rec is yes and sawAllow is yes and sawDeny is yes; never done is no and res is no and rec is no and sawAllow is yes and sawDeny is yes; res is no and rec is no and sawAllow is no and sawDeny is yes → done is no → expr <= 0; never done is no and res is no and rec is yes and sawAll |
| access/node-casbin/effectorStream | allow-and-deny: no matching allow, no access | access | docs | proven | 532 |  |
| access/node-casbin/effectorStream | allow-override: allowed exactly when some policy allows | access | docs | proven | 1330 |  |
| access/node-casbin/effectorStream | deny-override: once evaluated, allowed exactly when no policy denies | access | docs | proven | 18246 | never done is no and res is yes and rec is yes and sawAllow is no and sawDeny is yes; never done is no and res is yes and rec is yes and sawAllow is yes and sawDeny is yes; never done is no and res is yes and rec is no and sawAllow is no and sawDeny is yes; never done is no and res is yes and rec is no and sawAllow is yes and sawDeny is yes; never done is no and res is no and rec is yes and sawAll |
| access/node-casbin/effectorStream | once decided, the result never changes | step | inferred | proven | 804 |  |
| access/node-casbin/effectorStream | priority: the first decisive policy decides | step | docs | proven | 1590 |  |
| access/node-casbin/roleManager | every link joins two known roles | safety | inferred | proven | 564 |  |
| access/node-casbin/roleManager | a name always inherits itself | access | docs | proven | 142 |  |
| access/node-casbin/roleManager | after addLink, name1 inherits name2 directly | step | docs | proven | 222 |  |
| access/node-casbin/roleManager | after deleteLink, name1 no longer inherits name2 directly | step | docs | unknown | 1548 | after deleteLink, name1 no longer inherits name2 directly @step law; sat; the search found nothing that proves it in 1188 ms |
| access/node-casbin/roleManager | a link changes only for the pair named | step | inferred | proven | 207 |  |
| access/node-casbin/roleManager | with maxHierarchyLevel 0 only a name itself is held | access | docs | proven | 229 |  |
| access/cedar-examples/documentCloud | an unauthenticated request is always denied | safety | docs | proven | 50 |  |
| access/cedar-examples/documentCloud | only the owner can delete a document | access | docs | proven | 52 |  |
| access/cedar-examples/documentCloud | the owner can delete their document | access | docs | refuted | 53 | **bug**: Suspected real bug (in an example policy set). The README says owners delete their documents ("DeleteDocument: Only the owner should be able do this"), but policies.cedar has no permit for DeleteDocument at all (the README's own snippet names Action::"deleteDocument", which is not in the schema). The Cedar engine (cedar-wasm 4.14.0) denies alice deleting her own unblocked document, authen |
| access/cedar-examples/documentCloud | a private document is open to its owner only | access | docs | proven | 61 |  |
| access/cedar-examples/documentCloud | a blocked user never sees the blocker's documents | access | docs | proven | 34 |  |
| access/cedar-examples/documentCloud | the owner can always view their document | access | docs | proven | 39 |  |
| access/cedar-examples/documentCloud | the owner never loses the right to share | access | docs | proven | 63 |  |
| access/cedar-examples/documentCloud | the public can view a public document | access | docs | refuted | 39 | **bug**: Suspected real bug (in an example; the intent is the README's, which is ambiguous). The README calls Public "a principal that represents an un-authenticated user" that "can view only when explicitly permitted", but the forbid at policies.cedar:108-109 denies every request whose context has is_authenticated false, Public::"public" included: Cedar denies the unauthenticated public view of a |
| access/cedar-examples/documentCloud | the modify ACL never decides viewing | access | inferred | proven | 261 |  |
| access/kubernetes/rbacRuleAllows | without the verb or "*", a rule allows nothing | access | docs | proven | 198 |  |
| access/kubernetes/rbacRuleAllows | a rule naming only non-empty resources never allows an unnamed request | access | docs | proven | 266 |  |
| access/kubernetes/rbacRuleAllows | "*" everywhere and no names allows every resource request | access | docs | proven | 589 |  |
| access/kubernetes/rbacRuleAllows | a non-resource request needs a matching URL | access | docs | proven | 2177 |  |
| access/kubernetes/rbacRuleAllows | a subresource needs its own grant | access | docs | proven | 203 |  |
| access/kubernetes/rbacRuleAllows | with no resource names, the name never matters | access | docs | proven | 6317 |  |
| auth/keycloak/bruteForceProtector | past the failure factor, a failure disables the user at once | safety | docs | unknown | 47386 | past the failure factor, a failure disables the user at once @step law; sat; a model; the search found nothing that proves it in 45647 ms |
| auth/keycloak/bruteForceProtector | a temporary lockout waits at most maxFailureWaitSeconds | safety | docs | proven | 2286 |  |
| auth/keycloak/bruteForceProtector | too many OTP failures disable the user | safety | docs | proven | 1232 |  |
| auth/keycloak/bruteForceProtector | with permanent lockout, too many temporary lockouts disable the user | safety | docs | proven | 2232 |  |
| auth/keycloak/bruteForceProtector | a successful login clears the failure count | step | docs | proven | 8692 | exists is no → fails + notBefore <= 0 |
| auth/keycloak/bruteForceProtector | a permanent lockout is never lifted by a login | step | docs | proven | 1729 |  |
| auth/lucia/validateSession | an expired session is never validated | safety | docs | proven | 609 |  |
| auth/lucia/validateSession | validation never shortens a session | step | docs | proven | 828 |  |
| auth/lucia/validateSession | no session outlives sessionExpiresIn past the latest time seen | safety | docs | proven | 616 |  |
| auth/lucia/validateSession | a deleted session never comes back | safety | inferred | unknown | 6484 | a deleted session never comes back @step; sat; a model; the search found nothing that proves it in 5881 ms |
| auth/lucia/validateSession | invalidateUserSessions ends every session of the user | step | docs | proven | 531 |  |
| auth/node-oidc-provider/refreshTokenRotation | a rotated token's old value is rejected | step | docs | unknown | 27201 | a rotated token's old value is rejected @2 steps; sat; the search found nothing that proves it in 25288 ms |
| auth/node-oidc-provider/refreshTokenRotation | once reuse is detected, no token of that grant is live | safety | docs | unknown | 49623 | once reuse is detected, no token of that grant is live @step; sat; a model; the search found nothing that proves it in 38798 ms |
| auth/node-oidc-provider/refreshTokenRotation | a refresh token past its expiry is never served | safety | docs | proven | 1088 |  |
| auth/node-oidc-provider/refreshTokenRotation | only the client the token was issued to can use it | access | docs | proven | 1164 |  |
| auth/node-oidc-provider/refreshTokenRotation | presenting a consumed token revokes its whole grant | step | docs | proven | 1304 |  |
| auth/node-oidc-provider/refreshTokenRotation | at most one live refresh token per grant | safety | inferred | proven | 14398 | every k: Tok.st[k] is 1 → Tok.grant[k] + 1 <= nextGrant |
| approval/gitea/reviews | two counted approvals are never by the same reviewer | safety | docs | unknown | 102932 | two counted approvals are never by the same reviewer @step; sat; a model; the search found nothing that proves it in 62541 ms |
| approval/gitea/reviews | after a reviewer approves or rejects, none of their other reviews counts | step | docs | proven | 16537 |  |
| approval/gitea/reviews | with DismissStaleApprovals, a push that changes the diff leaves no approval counted | step | docs | proven | 13144 |  |
| approval/gitea/reviews | only approve and reject reviews are dismissed or undismissed | step | docs | proven | 11872 |  |
| approval/openzeppelin/Governor | with the governor as the timelock's only proposer, a proposal's calls run only after it succeeded and was queued | step | docs | unknown | 17242 | with the governor as the timelock's only proposer, a proposal's calls run only after it succeeded and was queued @step law; sat; the search found nothing that proves it in 16317 ms |
| approval/openzeppelin/Governor | a proposal's calls run at most once | safety | docs | unknown | 17881 | a proposal's calls run at most once @step; sat; a model; the search found nothing that proves it in 17517 ms |
| approval/openzeppelin/Governor | with the governor as the timelock's only proposer, a canceled proposal's calls never run | step | docs | unknown | 7915 | with the governor as the timelock's only proposer, a canceled proposal's calls never run @step law; sat; a model; the search found nothing that proves it in 7293 ms |
| approval/openzeppelin/Governor | every account is counted at most once | safety | docs | proven | 6078 | every k: Counted[k] is 1 → 1 <= HasVoted[k] |
| approval/openzeppelin/Governor | only the proposer cancels, and only while pending | access | docs | proven | 1273 |  |
| approval/openzeppelin/Governor | votes are counted only while the vote is active | step | docs | proven | 1098 |  |
| approval/openzeppelin/Governor | a queued proposal is eventually executed or canceled | liveness | docs | unknown | 99 | no linear rank, in order, that 0 helpful steps sampled lower and 0 others keep |
| approval/kubernetes/csrConditions | Approved and Denied are never both set | safety | docs | proven | 572 |  |
| approval/kubernetes/csrConditions | an Approved, Denied or Failed condition is never removed | step | docs | proven | 581 |  |
| approval/kubernetes/csrConditions | only the approval subresource sets Approved or Denied | access | docs | proven | 539 |  |
| approval/kubernetes/csrConditions | once populated, the certificate never changes | step | docs | proven | 366 |  |
| approval/kubernetes/csrConditions | every request holds at most one Approved condition | safety | tests | proven | 1934 | nA + nD <= 1; nF <= 1 |
| approval/kubernetes/csrConditions | a denied request never has a certificate | safety | docs | unknown | 1767 | a denied request never has a certificate @step; sat; a model; the search found nothing that proves it in 1513 ms |
| inventory/medusa/reservations | a reservation created without backorder never takes more than is available | step | tests | proven | 1695 |  |
| inventory/medusa/reservations | a batch created without backorder never takes more than is available | step | inferred | unknown | 29599 | a batch created without backorder never takes more than is available @step law; sat; a model; the search found nothing that proves it in 27357 ms |
| inventory/medusa/reservations | an update without backorder never takes more than is available where the reservation ends up | step | tests | unknown | 23272 | an update without backorder never takes more than is available where the reservation ends up @step law; sat; a model; the search found nothing that proves it in 21224 ms |
| inventory/medusa/reservations | the reserved quantity at a location is what its live reservations hold | safety | docs | refuted | 994 | **bug**: Suspected real bugs, two paths. (1) Moving a reservation: the old location's -quantity adjustment is computed (:617-628) but applied only to levels ensureInventoryLevels returned (:684-702), which are the new location's: the old level keeps the reservation's quantity forever. (2) restoreReservationItems_ on an id that is already live lists it again and adds its quantity again (:780-796, : |
| inventory/medusa/reservations | only reservations change the reserved quantity | access | docs | proven | 1767 |  |
| inventory/medusa/reservations | every live reservation can be released | liveness | tests | unknown | 1024 | no linear rank, in order, that 0 helpful steps sampled lower and 12 others keep |
| inventory/saleor/allocations | the stock's allocated count is the sum of its allocations | safety | inferred | refuted | 276 | **bug**: Suspected real bug. deallocate_stock appends one Stock instance per allocation, each with quantity_allocated = F(...) - n (management.py:399-405), and saves them with Stock.objects.bulk_update (:449). For two order lines allocated on one stock (two lines of one variant), the list holds that stock twice; Django's bulk_update writes only the first of duplicate objects (its CASE WHEN on the  |
| inventory/saleor/allocations | allocations never exceed the stock unless a fulfilment was let exceed it | safety | docs | proven | 3181 | every k: Row[k] is 0 → Alloc[k] <= 0 |
| inventory/saleor/allocations | an allocation takes all of the line or nothing | step | docs | proven | 568 |  |
| inventory/saleor/allocations | a deallocation returns to the stock exactly what it takes from the allocations | step | docs | unknown | 39 | a deallocation returns to the stock exactly what it takes from the allocations @step law; sat |
| inventory/saleor/allocations | every line's allocation can be released | liveness | docs | unknown | 234 | no linear rank, in order, that 0 helpful steps sampled lower and 36 others keep |
| inventory/solidus/stockItem | a stock item that is not backorderable never has a negative count | safety | docs | proven | 343 |  |
| inventory/solidus/stockItem | backordered units filled never exceed the stock received | safety | docs | proven | 325 |  |
| inventory/solidus/stockItem | stock received fills waiting backordered units first | step | docs | proven | 8973 |  |
| inventory/solidus/stockItem | a stock movement of a variant that does not track inventory never changes the count | step | docs | proven | 455 |  |
| approval/openzeppelin/TimelockController | every operation executes at most once | safety | docs | unknown | 34145 | every operation executes at most once @step; sat; the search found nothing that proves it in 33816 ms |
| approval/openzeppelin/TimelockController | an operation executes no sooner than the minimum delay after it was scheduled | step | docs | unknown | 3028 | an operation executes no sooner than the minimum delay after it was scheduled @step law; sat; the search found nothing that proves it in 2808 ms |
| approval/openzeppelin/TimelockController | an operation executes only after its predecessor is done | step | docs | proven | 311 |  |
| approval/openzeppelin/TimelockController | a cancelled or unscheduled operation never executes | step | docs | proven | 178 |  |
| approval/openzeppelin/TimelockController | only the executor executes, unless the role is open | access | docs | proven | 188 |  |
| approval/openzeppelin/TimelockController | only the proposer schedules | access | docs | proven | 214 |  |
| approval/openzeppelin/TimelockController | every scheduled operation becomes ready | liveness | docs | unknown | 1763 | every scheduled operation becomes ready: each step stays or gets there, the rank kept only with its region @step law; sat; rank (167 + d + minDelay + minDelay$some + t0 − (executor + minDelay0 + now + open + self)) from the runs; the kernel's goals not proven with it |
| inventory/vendure/stockMovements | stock allocated never goes negative | safety | docs | refuted | 17 | **bug**: Suspected real bug (with a caller that triggers it). createReleasesForOrderLines and createSalesForOrder free min(quantity, the line's Allocation records) (default-stock-location-strategy.ts:79-106), and Allocation records are never reduced, so a second release (or a release after a sale) of the same line frees the same stock again: stock 5, allocate 1, release 1, release 1 gives stockAll |
| inventory/vendure/stockMovements | a line's sales and releases never free more than it allocated | safety | inferred | refuted | 68 | **bug**: The same mechanism: the strategy reads the line's Allocation records and never what was already sold or released. run: {"params":{"track":1,"d":8},"trace":[{"op":1,"line":8,"q":7,"n":3,"n$neg":0},{"op":1,"line":0,"q":2,"n":8,"n$neg":0},{"op":1,"line":0,"q":4,"n":0,"n$neg":6},{"op":1,"line":8,"q":4,"n":5,"n$neg":0},{"op":1,"line":0,"q":4,"n":0,"n$neg":4},{"op":4,"line":8,"q":6,"n":1,"n$neg |
| inventory/vendure/stockMovements | once the stock level exists, a sale takes from the allocated stock exactly what it takes from stock on hand | step | docs | proven | 768 |  |
| inventory/vendure/stockMovements | stock of a variant that does not track inventory moves only by adjustment | step | docs | proven | 484 |  |
| ledger/openzeppelin/RefundEscrow | no more is paid out than was deposited | safety | inferred | proven | 9355 | balance + toBeneficiary <= deposited; balance + refunded <= deposited; st is Refunding → toBeneficiary <= 0; st is Active → deposited <= balance; st is Closed → 1 <= balance → refunded + toBeneficiary <= 0 |
| ledger/openzeppelin/RefundEscrow | the beneficiary and the refundees are never both paid | safety | docs | proven | 9382 | balance + toBeneficiary <= deposited; st is Refunding → toBeneficiary <= 0; balance + refunded <= deposited; st is Closed → refunded <= 0; st is Active → deposited <= balance |
| ledger/openzeppelin/RefundEscrow | until closed, every refundee's deposit is covered by the balance | safety | inferred | unknown | 1719 | until closed, every refundee's deposit is covered by the balance @step; sat; a model; the search found nothing that proves it in 1426 ms |
| ledger/openzeppelin/RefundEscrow | the state never returns to Active | step | docs | proven | 223 |  |
| ledger/openzeppelin/RefundEscrow | only the owner changes the state | access | docs | proven | 210 |  |
| ledger/openzeppelin/RefundEscrow | a refund only while refunding | step | docs | proven | 253 |  |
| ledger/openzeppelin/RefundEscrow | once refunding, every deposit is refunded | liveness | docs | unknown | 49 | no linear rank, in order, that 0 helpful steps sampled lower and 1 others keep |
| ledger/blnk/balances | every balance is its credits less its debits | safety | tests | proven | 9350 |  |
| ledger/blnk/balances | every inflight balance is its inflight credits less its inflight debits | safety | tests | proven | 11444 |  |
| ledger/blnk/balances | no inflight debit is ever negative | safety | tests | proven | 1020 |  |
| ledger/blnk/balances | money is conserved | safety | tests | proven | 2043 |  |
| ledger/blnk/balances | inflight money is conserved | safety | tests | proven | 1808 |  |
| ledger/blnk/balances | no balance overdraws past the largest limit it sourced under | safety | tests | unknown | 50775 | no balance overdraws past the largest limit it sourced under @step; sat; a model; the search found nothing that proves it in 48855 ms |
| ledger/openzeppelin/ERC20 | the balances sum to the total supply | safety | docs | proven | 474 |  |
| ledger/openzeppelin/ERC20 | no balance exceeds the total supply | safety | docs | unknown | 1773 | no balance exceeds the total supply @step; sat; a model; the search found nothing that proves it in 1119 ms |
| ledger/openzeppelin/ERC20 | the total supply never passes the uint256 bound | safety | docs | proven | 386 |  |
| ledger/openzeppelin/ERC20 | a transfer neither creates nor destroys tokens | step | docs | proven | 431 |  |
| ledger/openzeppelin/ERC20 | only its owner, a spender it approved, or a burn lowers a balance | access | docs | proven | 464 |  |
| ledger/openzeppelin/ERC20 | transferFrom spends the allowance it uses | step | docs | proven | 396 |  |
| payment/medusa/orderItemQuantities | never more fulfilled than ordered | safety | docs | proven | 602 |  |
| payment/medusa/orderItemQuantities | only a cancelled fulfilment takes the shipped past the fulfilled | step | docs | proven | 626 |  |
| payment/medusa/orderItemQuantities | only a cancelled fulfilment takes the delivered past the fulfilled | step | docs | proven | 632 |  |
| payment/medusa/orderItemQuantities | never more returned than fulfilled | safety | docs | refuted | 6 | **bug**: Suspected real bug at the module's action level. With positive quantities: fulfil 1, return 1, receive 1, return 1, receive 1 leaves return_received_quantity 2 for 1 fulfilled: RETURN_ITEM (return-item.ts:51-61) checks `fulfilled - return_requested` and forgets what was already received. The search's run is a negative quantity: CANCEL_RETURN_ITEM of -2 passes `!quantity` and `-2 > return_ |
| payment/medusa/orderItemQuantities | never more written off than ordered | safety | docs | refuted | 9 | **bug**: Suspected real bug at the module's action level (lower confidence: the claim workflows that emit WRITE_OFF_ITEM were not traced). WRITE_OFF_ITEM (write-off-item.ts:48-53) compares one action's quantity with the item's quantity, not the total written off: two write-offs of 2 on an item of 2 write off 4. The search's run: REINSTATE_ITEM of -3 (any quantity not above the item's passes) raise |
| payment/medusa/orderItemQuantities | a receipt never takes the requested count below zero | step | docs | proven | 295 |  |
| payment/medusa/orderItemQuantities | an update never sets the quantity below the fulfilled | step | docs | proven | 279 |  |
| payment/medusa/orderItemQuantities | every requested return is received in the end | liveness | inferred | unknown | 299 | no linear rank, in order, that 0 helpful steps sampled lower and 364 others keep |
| payment/medusa/captureRefund | never more captured than authorized | safety | docs | proven | 1148 |  |
| payment/medusa/captureRefund | never more refunded than captured | safety | docs | proven | 924 |  |
| payment/medusa/captureRefund | a canceled payment is never captured | step | docs | proven | 1455 |  |
| payment/medusa/captureRefund | a replayed refund moves no funds | step | docs | proven | 1598 |  |
| payment/medusa/captureRefund | a pending refund with a key is resolved once retried | liveness | docs | unknown | 112 | no linear rank, in order, that 0 helpful steps sampled lower and 1 others keep |
| payment/solidus/Payment | refunds never exceed the payment amount | safety | docs | refuted | 106 | **bug**: Suspected real bug (from the source; ActiveRecord models, not run). With the default configuration a Spree::Refund of the whole amount is valid on a pending (authorized) payment (refund.rb:89-109; refundable_payment_states default %w[completed pending]), and a later partial capture! sets the payment's amount to what was captured (processing.rb:88 `update!(amount: captured_amount)`), below |
| payment/solidus/Payment | a failed, void or invalid payment never changes state | step | docs | proven | 480 |  |
| payment/solidus/Payment | when required, a refund only on a completed or pending payment | step | docs | proven | 480 |  |
| payment/solidus/Payment | a capture never lowers what was captured | step | inferred | proven | 303 |  |
| payment/solidus/Payment | a processing payment is resolved | liveness | inferred | unknown | 66 | no linear rank, in order, that 0 helpful steps sampled lower and 13 others keep |
| ledger/tigerbeetle/transfers | an account that forbids it never has more debits than credits | safety | docs | unknown | 115426 | every T cell is a value of its kind @step; unknown; the prover's time budget ran out at 34 hypotheses, 0 case splits deep. Each case a step decides multiplies the cases to refute, so many interacting cases can outgrow it: state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions; the search found nothing that proves it in 600 |
| ledger/tigerbeetle/transfers | an account that forbids it never has more credits than debits | safety | docs | unknown | 116136 | every T cell is a value of its kind @step; unknown; the prover's time budget ran out at 34 hypotheses, 0 case splits deep. Each case a step decides multiplies the cases to refute, so many interacting cases can outgrow it: state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions; the search found nothing that proves it in 600 |
| ledger/tigerbeetle/transfers | posted debits equal posted credits | safety | inferred | unknown | 109080 | every T cell is a value of its kind @step; unknown; the prover's time budget ran out at 27 hypotheses, 0 case splits deep. Each case a step decides multiplies the cases to refute, so many interacting cases can outgrow it: state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions; the search found nothing that proves it in 594 |
| ledger/tigerbeetle/transfers | pending debits equal pending credits | safety | inferred | unknown | 109473 | every T cell is a value of its kind @step; unknown; the prover's time budget ran out at 27 hypotheses, 0 case splits deep. Each case a step decides multiplies the cases to refute, so many interacting cases can outgrow it: state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions; the search found nothing that proves it in 599 |
| ledger/tigerbeetle/transfers | a pending transfer is resolved at most once | step | docs | unknown | 104955 | every T cell is a value of its kind @step; unknown; the prover's time budget ran out at 26 hypotheses, 0 case splits deep. Each case a step decides multiplies the cases to refute, so many interacting cases can outgrow it: state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions; the search found nothing that proves it in 571 |
| ledger/tigerbeetle/transfers | a post never posts more than was pending | step | docs | unknown | 106480 | every T cell is a value of its kind @step; unknown; the prover's time budget ran out at 26 hypotheses, 0 case splits deep. Each case a step decides multiplies the cases to refute, so many interacting cases can outgrow it: state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions; the search found nothing that proves it in 582 |
| ledger/tigerbeetle/transfers | only voiding or expiry moves a closed account | step | docs | unknown | 106782 | every T cell is a value of its kind @step; unknown; the prover's time budget ran out at 26 hypotheses, 0 case splits deep. Each case a step decides multiplies the cases to refute, so many interacting cases can outgrow it: state the law over fewer steps (a one-step law and an invariant often give the same), or split it into laws about fewer conditions; the search found nothing that proves it in 585 |
| ledger/tigerbeetle/transfers | a pending transfer with a timeout is resolved in the end | liveness | docs | unknown | 143 | no linear rank, in order, that 0 helpful steps sampled lower and 0 others keep |
| payment/vendure/orderProcess | a cancelled order stays cancelled | step | docs | proven | 1786 |  |
| payment/vendure/orderProcess | an order is settled only when settled payments cover its total | step | docs | proven | 3917 |  |
| payment/vendure/orderProcess | a placed order is cancelled only with every line cancelled | step | docs | unknown | 8346 | a placed order is cancelled only with every line cancelled @step law; sat; a model; the search found nothing that proves it in 5780 ms |
| payment/vendure/orderProcess | an order ships only once its payment is authorized or settled | safety | inferred | proven | 5141 | never state is PaymentSettled and paid is no; never state is Modifying and paid is no; never state is ArrangingAdditionalPayment and paid is no; never state is PaymentAuthorized and paid is no |
| payment/vendure/orderProcess | a modifying order always gets out of Modifying | liveness | inferred | unknown | 208 | no linear rank, in order, that 0 helpful steps sampled lower and 0 others keep |
| circuit breaker/gobreaker/CircuitBreaker | half-open admits at most maxRequests requests | safety | docs | proven | 4244 |  |
| circuit breaker/gobreaker/CircuitBreaker | an open breaker admits no request before its timeout | step | docs | proven | 4225 |  |
| circuit breaker/gobreaker/CircuitBreaker | a failure in half-open opens the breaker | step | tests | proven | 5512 |  |
| circuit breaker/gobreaker/CircuitBreaker | the breaker closes only from half-open | step | inferred | proven | 6407 |  |
| circuit breaker/gobreaker/CircuitBreaker | a state change starts a new generation | step | docs | proven | 5683 |  |
| circuit breaker/gobreaker/CircuitBreaker | a state change clears the failure counts | step | docs | proven | 10454 |  |
| circuit breaker/gobreaker/CircuitBreaker | an open breaker goes half-open once its timeout passes | liveness | docs | unknown | 40 | no linear rank, in order, that 0 helpful steps sampled lower and 0 others keep |
| circuit breaker/cockatiel/ConsecutiveBreaker | an open circuit stays open on a call before halfOpenAfter | step | docs | proven | 343 |  |
| circuit breaker/cockatiel/ConsecutiveBreaker | at most one half-open test runs at a time | safety | docs | unknown | 20577 | at most one half-open test runs at a time @step; sat; the search found nothing that proves it in 20197 ms |
| circuit breaker/cockatiel/ConsecutiveBreaker | a successful test closes a half-open circuit | step | tests | proven | 516 |  |
| circuit breaker/cockatiel/ConsecutiveBreaker | a half-open circuit reopens only on its test failing | step | docs | unknown | 25 | a half-open circuit reopens only on its test failing @step law; sat |
| circuit breaker/cockatiel/ConsecutiveBreaker | isolation ends only by a dispose | step | docs | proven | 559 |  |
| circuit breaker/cockatiel/ConsecutiveBreaker | an isolated circuit holds a handle | safety | inferred | proven | 465 |  |
| circuit breaker/cockatiel/ConsecutiveBreaker | an open circuit lets a test through once halfOpenAfter passes | liveness | docs | unknown | 66 | no linear rank, in order, that 0 helpful steps sampled lower and 4 others keep |
| circuit breaker/opossum/CircuitBreaker | an open breaker rejects every call | step | docs | proven | 4780 | pendingClose is yes → st is halfOpen |
| circuit breaker/opossum/CircuitBreaker | no call is let through within resetTimeout of the breaker opening | step | docs | unknown | 11835 | no call is let through within resetTimeout of the breaker opening @step law; sat; the search found nothing that proves it in 10255 ms |
| circuit breaker/opossum/CircuitBreaker | half-open lets one call through | safety | tests | proven | 6169 | trials is 1 → pendingClose <= 0 |
| circuit breaker/opossum/CircuitBreaker | a failure in half-open reopens the breaker | step | docs | unknown | 10040 | a failure in half-open reopens the breaker @step law; sat; a model; the search found nothing that proves it in 8581 ms |
| circuit breaker/opossum/CircuitBreaker | a success in half-open closes the breaker | step | docs | proven | 2485 |  |
| circuit breaker/opossum/CircuitBreaker | a failing call opens a closed breaker only past the threshold | step | docs | proven | 2178 |  |
| circuit breaker/opossum/CircuitBreaker | an open breaker goes half-open once resetTimeout passes | liveness | docs | unknown | 45 | no linear rank, in order, that 0 helpful steps sampled lower and 0 others keep |
| circuit breaker/opossum/CircuitBreaker | a half-open breaker closes or reopens | liveness | docs | unknown | 10907 | a half-open breaker closes or reopens: each step stays or gets there, the rank kept only with its region @step law; sat; rank (pendingClose) from the runs; the kernel's goals not proven with it |
| circuit breaker/polly/ConsecutiveCountCircuitController | an open circuit admits no call before the break ends | step | docs | proven | 372 |  |
| circuit breaker/polly/ConsecutiveCountCircuitController | a half-open circuit admits no call while a trial blocks it | step | docs | proven | 335 |  |
| circuit breaker/polly/ConsecutiveCountCircuitController | a success in half-open closes the circuit | step | docs | proven | 373 |  |
| circuit breaker/polly/ConsecutiveCountCircuitController | a failure in half-open breaks the circuit for another durationOfBreak | step | docs | proven | 480 |  |
| circuit breaker/polly/ConsecutiveCountCircuitController | a late result while open does not extend the break | step | docs | proven | 472 |  |
| circuit breaker/polly/ConsecutiveCountCircuitController | a closed circuit has fewer consecutive failures than allowed | safety | docs | proven | 335 |  |
| circuit breaker/polly/ConsecutiveCountCircuitController | an isolated circuit stays isolated until reset | step | docs | proven | 282 |  |
| circuit breaker/polly/ConsecutiveCountCircuitController | an open circuit goes half-open once the break ends | liveness | docs | unknown | 104 | no linear rank, in order, that 0 helpful steps sampled lower and 3 others keep |
| queue/bullmq/jobRetry | a job is finished at most max(attempts, 1) times | safety | docs | unknown | 9777 | a job is finished at most max(attempts, 1) times @step; sat; the search found nothing that proves it in 9052 ms |
| queue/bullmq/jobRetry | a completed job is never retried | step | inferred | proven | 983 |  |
| queue/bullmq/jobRetry | an unrecoverable error fails the job for good | step | docs | proven | 1063 |  |
| queue/bullmq/jobRetry | a job started maxStartedAttempts times is not retried | step | docs | proven | 1034 |  |
| queue/bullmq/jobRetry | an exponential retry waits at least the base delay | step | inferred | unknown | 7093 | an exponential retry waits at least the base delay @step law; sat; the search found nothing that proves it in 5696 ms |
| queue/bullmq/jobRetry | a delayed job is promoted once its delay passes | liveness | docs | unknown | 126 | no linear rank, in order, that 0 helpful steps sampled lower and 0 others keep |
| queue/bullmq/jobRetry | every job completes or fails for good | liveness | docs | unknown | 9390 | every job completes or fails for good: each step stays or gets there, the rank kept only with its region @step law; sat; rank (68 + 44·attempts + 25·backoff + 16·delay + 44·maxStalledCount + 6·maxStartedAttempts + st − (atm + 99·ats + 2·defa + last + 2·stc + until)) from the runs; the kernel's goals not proven with it |
| queue/graphile-worker/jobLifecycle | a job is attempted at most max_attempts times | safety | docs | proven | 280 |  |
| queue/graphile-worker/jobLifecycle | a failed attempt waits at least e seconds | step | docs | proven | 1966 | attempts is 0 → lockedBy <= 0 |
| queue/graphile-worker/jobLifecycle | a failed attempt waits at most e^10 seconds | step | docs | proven | 452 |  |
| queue/graphile-worker/jobLifecycle | a completed job is never run again | step | inferred | proven | 521 |  |
| queue/graphile-worker/jobLifecycle | only the lock holder or the 4-hour sweep unlocks a job | access | docs | proven | 448 |  |
| queue/graphile-worker/jobLifecycle | a locked job is eventually unlocked | liveness | docs | unknown | 26 | no linear rank, in order, that 0 helpful steps sampled lower and 7 others keep |
| queue/pg-boss/retry | without a resume, a job is claimed at most retryLimit + 1 times | safety | docs | proven | 13317 | started is yes and resumed is no → st is retry → claims <= retryLimit; never st is created and started is yes and resumed is no; started is yes and resumed is no → st is active → claims <= retryCount + 1; never st is active and started is no and resumed is no; started is no and resumed is no → st is failed → claims <= 0; started is no and resumed is no → st is created → claims <= 0; started is yes |
| queue/pg-boss/retry | a completed job is never retried | step | inferred | proven | 823 |  |
| queue/pg-boss/retry | a job with no retries left fails for good | step | docs | proven | 1194 |  |
| queue/pg-boss/retry | a backoff retry waits at most retryDelayMax | step | docs | proven | 926 |  |
| queue/pg-boss/retry | a stale settle never touches a newer attempt | access | docs | proven | 805 |  |
| queue/pg-boss/retry | an expired active job is failed or retried | liveness | docs | unknown | 56 | no linear rank, in order, that 0 helpful steps sampled lower and 9 others keep |
| queue/p-retry/pRetry | the retries consumed never exceed retries | safety | docs | proven | 442 |  |
| queue/p-retry/pRetry | no retry waits longer than maxTimeout | step | docs | proven | 664 |  |
| queue/p-retry/pRetry | no retry waits past maxRetryTime | step | docs | proven | 831 |  |
| queue/p-retry/pRetry | an uncapped retry waits at least minTimeout | step | docs | error | 361 | RangeError: 290760102328562900 is not a natural     at naturalConst (/work/gdp-wired/core/dsl.ts:32:52)     at termOf (/work/gdp-wired/core/dsl.ts:37:58)     at lit (/work/gdp-wired/core/dsl.ts:82:50)     at map (native:1:11)     at termOfSide (/work/gdp-wired/core/discover.ts:40:19)     at condOf (/work/gdp-wired/core/discover.ts:44:68)     at <anonymous> (/work/gdp-wired/core/dsl.ts:1297:73)     |
| queue/p-retry/pRetry | an AbortError stops retrying | step | docs | proven | 504 |  |
| queue/p-retry/pRetry | a settled call is never attempted again | step | inferred | proven | 442 |  |
| queue/p-retry/pRetry | with finite retries every call settles | liveness | docs | unknown | 7877 | with finite retries every call settles: each step stays or gets there, the rank kept only with its region @step law; sat; rank (1 + maxTimeout + minTimeout + retries − (attempts + consumed + hasMaxTimeout + waited)) from the runs; the kernel's goals not proven with it |
| feature flag/unleash-client-node/flexibleRollout | a disabled feature serves nobody | safety | inferred | proven | 18 |  |
| feature flag/unleash-client-node/flexibleRollout | raising the rollout never removes a user who was in | safety | tests | proven | 89 |  |
| feature flag/unleash-client-node/flexibleRollout | a 0% rollout serves nobody through the strategy | safety | tests | proven | 13 |  |
| feature flag/unleash-client-node/flexibleRollout | a 100% rollout serves every user with an id who passes the constraints | safety | tests | proven | 31 |  |
| feature flag/unleash-client-node/flexibleRollout | a user failing the constraints is never served by the strategy | access | docs | proven | 26 |  |
| feature flag/unleash-client-node/flexibleRollout | a strategy without a stickiness id serves nobody | safety | tests | proven | 27 |  |
| feature flag/growthbook/forceRuleRollout | a rule with coverage 0 serves nobody | safety | inferred | proven | 29 |  |
| feature flag/growthbook/forceRuleRollout | raising the coverage never removes a user who was in | safety | inferred | proven | 106 |  |
| feature flag/growthbook/forceRuleRollout | widening the range never removes a user who was in | safety | inferred | proven | 79 |  |
| feature flag/growthbook/forceRuleRollout | a user without the hash attribute is never in a percentage rollout | access | docs | proven | 18 |  |
| feature flag/growthbook/forceRuleRollout | a rule with no range and no coverage includes everyone | safety | docs | proven | 12 |  |
| feature flag/growthbook/forceRuleRollout | full coverage includes every hashed user | safety | inferred | proven | 50 |  |
| feature flag/growthbook/forceRuleRollout | a filtered-out user is never served the forced value | access | docs | proven | 12 |  |
| feature flag/flagd/fractional | a variant of weight 0 is never chosen | step | docs | unknown | 20 | a variant of weight 0 is never chosen @step law; sat |
| feature flag/flagd/fractional | once the weights read pass the bucket, a variant is chosen | safety | docs | proven | 96 |  |
| feature flag/flagd/fractional | the chosen variant's range holds the bucket | safety | docs | proven | 1579 | done is no → rangeEnd <= bucket |
| feature flag/flagd/fractional | a chosen variant never changes | step | docs | proven | 89 |  |
| feature flag/flagd/fractional | the chosen variant is one the loop read | safety | inferred | proven | 117 |  |
| quota/kubernetes/ResourceQuota.CheckRequest | an admitted request leaves every resource it charges within its hard limit | step | docs | proven | 891 |  |
| quota/kubernetes/ResourceQuota.CheckRequest | a request that would pass a hard limit changes no usage | step | docs | proven | 735 |  |
| quota/kubernetes/ResourceQuota.CheckRequest | a dry run changes no usage | step | docs | proven | 440 |  |
| quota/kubernetes/ResourceQuota.CheckRequest | admission never lowers usage | step | docs | proven | 651 |  |
| quota/kubernetes/ResourceQuota.CheckRequest | a resource the quota does not limit is never charged | step | docs | proven | 289 |  |
| quota/librechat/balanceReservation | an admission reserves only credits no other request holds | step | docs | proven | 14706 | hasReserved is no → reserved <= 0 |
| quota/librechat/balanceReservation | releasing an unknown or already released reservation changes nothing | step | docs | proven | 970 |  |
| quota/librechat/balanceReservation | a renewal never revives a released reservation | step | docs | proven | 681 |  |
| quota/librechat/balanceReservation | a reservation that has not expired is never pruned | step | docs | proven | 511 |  |
| quota/librechat/balanceReservation | the reserved total is never negative | safety | inferred | unknown | 11059 | the reserved total is never negative @step; sat; a model; the search found nothing that proves it in 10582 ms |
| quota/librechat/balanceReservation | an applied auto-refill is recorded at most once | safety | docs | proven | 10165 | recorded is no → refillTx + 1 <= refills |
| quota/librechat/balanceReservation | once settled, every applied auto-refill is recorded | safety | docs | unknown | 12560 | once settled, every applied auto-refill is recorded @step; sat; a model; the search found nothing that proves it in 12334 ms |
| quota/librechat/balanceReservation | an applied auto-refill is eventually settled | liveness | docs | unknown | 144 | no linear rank, in order, that 0 helpful steps sampled lower and 12 others keep |
| quota/librechat/balanceReservation | every held reservation is eventually freed | liveness | docs | unknown | 154 | no linear rank, in order, that 0 helpful steps sampled lower and 12 others keep |
| quota/litellm/maxBudgetChecks | a key whose spend has reached its max_budget is refused | access | docs | proven | 176 |  |
| quota/litellm/maxBudgetChecks | a team whose spend has reached its max_budget is refused | access | docs | refuted | 7 | **bug**: Suspected real bug (an inconsistency, low severity). team_max_budget_check (auth_checks.py:6386) refuses only at spend > max_budget, so a team whose spend equals its max_budget is admitted, while the key (:5912), user, org and window checks refuse at spend >= max_budget. The original does it (repro: key at spend 1.0 of 1.0 refused, team at 1.0 of 1.0 admitted). The repo's own tests/e2e/qu |
| quota/litellm/maxBudgetChecks | while requests do not overlap, a key's spend passes its max_budget by at most one request's cost | safety | inferred | unknown | 4994 | while requests do not overlap, a key's spend passes its max_budget by at most one request's cost @step; sat; the search found nothing that proves it in 4830 ms |
| rate limit/bottleneck/LocalDatastore | no more weight runs at once than maxConcurrent | safety | docs | proven | 548 |  |
| rate limit/bottleneck/LocalDatastore | a job registers only when the reservoir holds its weight | step | docs | proven | 576 |  |
| rate limit/bottleneck/LocalDatastore | the heartbeat's increase never lifts the reservoir past reservoirIncreaseMaximum | step | docs | proven | 693 |  |
| rate limit/bottleneck/LocalDatastore | two jobs start at least minTime apart | step | docs | unknown | 7871 | two jobs start at least minTime apart @step law; sat; the search found nothing that proves it in 7328 ms |
| rate limit/bottleneck/LocalDatastore | a reservoir below its refresh amount is refreshed | liveness | docs | unknown | 46 | no linear rank, in order, that 0 helpful steps sampled lower and 8 others keep |
| rate limit/express-rate-limit/MemoryStore | no client window lets through more than limit hits beyond its own hits taken back | safety | docs | unknown | 7395 | no client window lets through more than limit hits beyond its own hits taken back @step; sat; a model; the search found nothing that proves it in 7104 ms |
| rate limit/express-rate-limit/MemoryStore | a decrement never lowers a count the store has reset | step | docs | unknown | 25680 | a decrement never lowers a count the store has reset @step law; sat; the search found nothing that proves it in 25175 ms |
| rate limit/express-rate-limit/MemoryStore | the timer drops only clients whose window has passed | step | docs | unknown | 5757 | the timer drops only clients whose window has passed @step law; sat; the search found nothing that proves it in 5320 ms |
| rate limit/express-rate-limit/MemoryStore | a refused client is let through once its window has passed | liveness | docs | unknown | 43 | no linear rank, in order, that 0 helpful steps sampled lower and 46 others keep |
| rate limit/rate-limiter-flexible/RateLimiterMemory | a record lets through nothing, or no more than points beyond its start value and its rewards | safety | docs | unknown | 2829 | a record lets through nothing, or no more than points beyond its start value and its rewards @step; sat; a model; the search found nothing that proves it in 2373 ms |
| rate limit/rate-limiter-flexible/RateLimiterMemory | a key over its points refuses every consume until its record expires | step | docs | proven | 256 |  |
| rate limit/rate-limiter-flexible/RateLimiterMemory | a refused consume with blockDuration blocks the key for blockDuration the first time | step | docs | proven | 275 |  |
| rate limit/rate-limiter-flexible/RateLimiterMemory | a refused key is let through once its record expires, unless it never expires | liveness | docs | unknown | 47 | no linear rank, in order, that 0 helpful steps sampled lower and 49 others keep |
| rate limit/golang-x-time/AllowN | the bucket never holds more than burst tokens | safety | docs | proven | 116 |  |
| rate limit/golang-x-time/AllowN | a refused request changes nothing | step | docs | proven | 239 |  |
| rate limit/golang-x-time/AllowN | no more is granted than burst plus rate times the latest time seen | safety | docs | refuted | 4 | **bug**: Real behaviour, already reported upstream (golang/go#65508, open). reserveN sets lim.last = t when granting even if t is before lim.last (rate.go:378; advance only clamps elapsed to 0, :389-391), so the time between the new last and the old one is credited again: rate 1/s, burst 3, AllowN at 0,3,1,2,1,3 s grants 7 events by t = 3 s against 3 + 3 = 6 (control with time never going back: 4) |
| rate limit/golang-x-time/AllowN | a refused caller is granted one event once it waits long enough | liveness | docs | unknown | 71 | no linear rank, in order, that 0 helpful steps sampled lower and 309 others keep |
| rate limit/upstash-ratelimit/fixedWindow | no window admits more than tokens beyond what was refunded in it | safety | docs | proven | 2930 | every k: Admitted[k] <= Count[k] + Refunded[k] |
| rate limit/upstash-ratelimit/fixedWindow | a rejected request leaves the window's remaining tokens spendable | step | docs | refuted | 8 | **bug**: Suspected real bug, the class PR #156 fixed in tokenBucket only. The script INCRBYs before the limit is checked (single.ts:17, TS :219), so a request whose rate is larger than what is left is refused but still counted: fixedWindow(10) with 8 used, rate 5 is refused and leaves 13, so a following rate 2 is refused too (the 2 tokens left are gone). For rate 1 this is harmless (the count is a |
| rate limit/upstash-ratelimit/fixedWindow | a request blocked by the cache changes no count | step | docs | proven | 623 |  |
| rate limit/upstash-ratelimit/fixedWindow | a rejected caller is admitted in a later window | liveness | docs | unknown | 127 | no linear rank, in order, that 0 helpful steps sampled lower and 160 others keep |
| rate limit/upstash-ratelimit/slidingWindow | no window admits more than tokens | safety | docs | proven | 2857 | every k: Admitted[k] <= Count[k] |
| rate limit/upstash-ratelimit/slidingWindow | a rejected request leaves the window's remaining tokens spendable | step | docs | refuted | 6 | **bug**: Suspected real bug, same class as PR #156: the script checks previous-weighted + current >= limit without the rate (single.ts:82), then INCRBYs and the TS reports failure when the total passes the limit (:92, :340). slidingWindow(10) with 8 used: rate 5 refused, the current bucket left at 13, rate 2 then refused; the over-count also weighs on the next window as its previous bucket. Repro  |
| rate limit/upstash-ratelimit/slidingWindow | a request blocked by the cache changes no count | step | docs | proven | 673 |  |
| rate limit/upstash-ratelimit/slidingWindow | a rejected caller is admitted two windows later | liveness | docs | unknown | 37 | no linear rank, in order, that 0 helpful steps sampled lower and 20 others keep |
| rate limit/upstash-ratelimit/tokenBucket | a rejected request leaves the bucket unchanged | step | docs | proven | 20715 |  |
| rate limit/upstash-ratelimit/tokenBucket | an admitted request takes no more tokens than the bucket holds | step | docs | proven | 24474 |  |
| rate limit/upstash-ratelimit/tokenBucket | only a refund lifts the tokens past maxTokens | step | docs | proven | 17522 |  |
| rate limit/upstash-ratelimit/tokenBucket | tokens never exceed maxTokens plus what was refunded | safety | tests | proven | 15652 |  |
| rate limit/upstash-ratelimit/tokenBucket | a rejected caller is admitted once it waits for a refill | liveness | docs | unknown | 108 | no linear rank, in order, that 0 helpful steps sampled lower and 93 others keep |
| xstate/amplify-ui/forgotPassword | resolved is never left | step | docs | proven | 872 |  |
| xstate/amplify-ui/forgotPassword | it resolves only after a confirmation was sent | safety | inferred | proven | 4881 | state is confirmResetPassword.pending → 1 <= confirms |
| xstate/amplify-ui/forgotPassword | a new password is sent only after the fields validate | step | inferred | proven | 1118 |  |
| xstate/amplify-ui/forgotPassword | a completed reset resolves as RESET_PASSWORD_COMPLETE | step | inferred | proven | 1192 |  |
| xstate/amplify-ui/forgotPassword | every request to Cognito starts with the error cleared | step | inferred | proven | 1095 |  |
| xstate/amplify-ui/forgotPassword | a code is never requested while a confirmation is pending | step | inferred | proven | 1146 |  |
| xstate/amplify-ui/forgotPassword | a submitted new password ends resolved or back at the form | liveness | inferred | unknown | 9096 | a submitted new password ends resolved or back at the form: each step stays or gets there, the rank kept only with its region @step law; sat; rank (1 + confirms + requests + startStep + step − state) from the runs; the kernel's goals not proven with it |
| xstate/electric/pullWakeRunner | the backoff stays between 1 s and 30 s | safety | docs | proven | 468 |  |
| xstate/electric/pullWakeRunner | a stream response is held only while streaming | safety | docs | proven | 494 |  |
| xstate/electric/pullWakeRunner | STOP while running always goes to stopping | step | docs | proven | 734 |  |
| xstate/electric/pullWakeRunner | a successful connect resets the backoff | step | inferred | proven | 624 |  |
| xstate/electric/pullWakeRunner | a second reset while streaming changes nothing | step | docs | proven | 717 |  |
| xstate/electric/pullWakeRunner | START while not stopped changes nothing | step | inferred | proven | 702 |  |
| xstate/electric/pullWakeRunner | a started runner always comes back to stopped | liveness | docs | unknown | 233 | no linear rank, in order, that 5 helpful steps sampled lower and 16 others keep |
| xstate/gapless.js/track | DEACTIVATE from any state lands in idle | step | tests | proven | 7790 |  |
| xstate/gapless.js/track | DEACTIVATE keeps the buffer's loading state | step | tests | proven | 7790 |  |
| xstate/gapless.js/track | the fetch-and-decode child is spawned at most once | safety | tests | proven | 41236 | webAudioLoadingState is NONE → fetches <= 0 |
| xstate/gapless.js/track | Web Audio plays only a loaded buffer | safety | docs | proven | 5667 |  |
| xstate/gapless.js/track | while Web Audio plays the track reports WEBAUDIO | safety | tests | proven | 3519 |  |
| xstate/gapless.js/track | a buffer ready while preloading never leaves the track in loading | step | tests | proven | 7323 |  |
| xstate/gapless.js/track | a buffer error while Web Audio plays changes nothing | step | inferred | proven | 8058 |  |
| xstate/gapless.js/track | a pending play starts on Web Audio or is dropped once the buffer is ready | liveness | docs | unknown | 381 | no linear rank, in order, that 0 helpful steps sampled lower and 9 others keep |
| xstate/open-decision/websocket | the retries stay within the retry limit | safety | inferred | proven | 18950 | never state is retry and hasDoc is yes and hasToken is no; hasDoc is yes and hasToken is yes → state is retry → 10 <= retryLimit; state is retry → retries <= 9; never state is retry and hasDoc is no and hasToken is no; never state is retry and hasDoc is no and hasToken is yes; never state is connected and hasDoc is yes and hasToken is no; hasDoc is yes and hasToken is yes → state is connected → 10 |
| xstate/open-decision/websocket | error is never left | step | docs | proven | 249 |  |
| xstate/open-decision/websocket | a dropped connection under the limit is retried | step | inferred | proven | 310 |  |
| xstate/open-decision/websocket | OPEN while connected changes nothing | step | inferred | proven | 298 |  |
| xstate/open-decision/websocket | CLOSE ends an open connection | step | docs | refuted | 196 | **bug**: The original does it: no state handles CLOSE (xstate 4.34.0): after OPEN and the token, CLOSE leaves the machine connected and the websocket's cleanup (websocket.destroy() in the openWebsocket callback) is not run; a following OPEN for another tree is ignored too (OPEN is handled only in unconnected). TreeContext.tsx:40-42 sends CLOSE in the effect cleanup that runs when the tree id chang |
| xstate/open-decision/websocket | a synced connection resets the retries | step | inferred | unknown | 22 | a synced connection resets the retries @step law; sat |
| xstate/open-decision/websocket | an opening connection ends connected or failed | liveness | inferred | unknown | 12132 | an opening connection ends connected or failed: each step stays or gets there, the rank kept only with its region @step law; sat; rank (1 + hasDoc + retryLimit − (retries + state)) from the runs; the kernel's goals not proven with it |
| xstate/radio-room/radioStream | the retries stay within 3 | safety | docs | proven | 898 |  |
| xstate/radio-room/radioStream | a fourth consecutive failure gives up | step | docs | proven | 1321 |  |
| xstate/radio-room/radioStream | reaching playback resets the retries | step | docs | proven | 1935 |  |
| xstate/radio-room/radioStream | a stream fails with its error set | step | inferred | proven | 1428 |  |
| xstate/radio-room/radioStream | the stream connects only with a url | safety | tests | refuted | 247 | **bug**: The original does it: PLAY with no url (idle, playing), SET_URL a url (active), SET_URL "" enters active.loading again and starts a playback run with url "" (the root SET_URL's first branch, radioStreamMachine.ts:201, checks only event.url !== context.url, not hasUrl). Every other way into active is guarded by hasUrl/canConnect (Boolean(url)), and the machine's test 'waits for a url befor |
| xstate/radio-room/radioStream | TEARDOWN drops the stream and forgets the url | step | docs | proven | 2091 |  |
| xstate/radio-room/radioStream | an element event outside active changes nothing | step | inferred | proven | 11727 |  |
| xstate/radio-room/radioStream | a reconnect wait always ends | liveness | docs | unknown | 190 | no linear rank, in order, that 0 helpful steps sampled lower and 28 others keep |
| xstate/vef-framework-react/uploader | the parts are uploaded at most once | safety | inferred | proven | 2775 | state is initializing → uploads <= 0; state is idle → uploads <= 0 |
| xstate/vef-framework-react/uploader | the backend session is aborted at most once | safety | docs | proven | 3636 | state is initializing → aborts <= 0; state is uploading → aborts <= 0; state is completing → aborts <= 0; state is idle → aborts <= 0 |
| xstate/vef-framework-react/uploader | a failure is recorded exactly when the upload failed | safety | docs | proven | 451 |  |
| xstate/vef-framework-react/uploader | succeeded is never left | step | docs | proven | 397 |  |
| xstate/vef-framework-react/uploader | failed is never left | step | docs | proven | 234 |  |
| xstate/vef-framework-react/uploader | aborted is never left | step | docs | proven | 390 |  |
| xstate/vef-framework-react/uploader | an abort in an active phase always tears the session down | step | docs | proven | 244 |  |
| xstate/vef-framework-react/uploader | a phase that rejects always ends in failed | step | docs | proven | 469 |  |
| xstate/vef-framework-react/uploader | ABORT while idle changes nothing | step | inferred | proven | 389 |  |
| xstate/vef-framework-react/uploader | a started upload ends succeeded, failed or aborted | liveness | docs | unknown | 6922 | a started upload ends succeeded, failed or aborted: each step stays or gets there, the rank kept only with its region @step law; sat; rank (2 + 2·aborts + prepares − (completes + 2·kills + 2·uploads)) from the runs; the kernel's goals not proven with it |
