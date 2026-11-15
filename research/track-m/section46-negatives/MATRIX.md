# Section 46 negative acceptance matrix — B draft

Status: **SOURCE-ONLY DRAFT; NOT COMPILED OR RUN.** No RED or GREEN result is claimed.

- Worktree: `../gdp-wired-trackM-section46-negatives`
- Branch: `claude/b-section46-negatives`, fast-forwarded from `ab99a14d` to A's source-only candidate `0fc836616e98886046cc1c46399d1b071a2b2aaa` (tree `05c8a8e6ef023d3951cf0598076d38e2983f383a`).
- A approved the two new test paths and this matrix. No production files or existing tests changed.
- Main requested a separate child test commit on that exact candidate. Any later A repair is a new child; no dirty-source copying or history rewriting.
- A owns the newly authorized software gates. B has started no builds, tests, scheduler batches or diagnostic workloads.
- Governing inputs: `SECTION-46-AUTHOR-REVIEW.md` (`4bc2b0a2`), section 46.15–46.17 and the body-stop correction, D's `0ebf2fa2` ruling, and A's agreed provisional APIs.

## Missing author-review cases

All eight are explicit tests in `core/count-section46-acceptance.test.ts`.

| ID | Assertion | Execution boundary | Expected unwired-base behavior |
|---|---|---|---|
| N1 | Three different soft case stops, fourth proposal, F−3 tickets remain | Real `CountRecipePass` / `runCountRecipeController`, real lifted slices, fresh native certificate and native closing | Controller module missing at ab99. Once present, test must verify actual stop keys and tickets, not a string-only payload. |
| N2 | Retry certificate bytes equal independently rebuilt larger-first-allowance certificate | Same controller, two fresh native proof constructions and native checks | Controller module missing at ab99. Identical constant strings are not used as evidence. |
| N3 | Scaled T301 dependency shape: half replacement retries, separate body completes, Inv*/K3/safety follow | **Public `admitCountedFamily`**, exact leases, real scope/replay/native checks | **Expected RED even with A's current flat controller**: a C+leaf retry cannot fund the separate body. No skip or expected-failure annotation. Passing requires separately authorized disjoint production integration. |
| N4 | Half's only route declines; no Inv*, Inv3915, K3 or safety attempt after the block | **Public entry**, fixed known-only recipe inventory, actual event stream and producer-call trace | Missing public controller routing must fail the event/attempt assertions. No unknown ordinary alternative is silently added. |
| N5 | A stranded member's alternative replaces its old proof | **Public entry**; old proof has a genuine, independently checked unused cut requiring the subsequently unavailable premise | Old scope cannot replay over the final family. Final native acceptance must use the replacement; merely rewriting premise labels cannot pass. |
| N6 | An unchecked proposal understating its premises cannot enter G | Real controller plus conservative graph S, no closing callback permitted | Module absent on old base. Adding only raw recorded premises to G must fail. |
| N7 | Refused reduction retains funded full-only scope in the prover | **Public entry**, only one reduced replay refusal injected; full fallback and native closing real | Missing routing/fallback must fail explicit canonical/original events and retained full-scope premises. |
| N8 | Target having only an unknown-set recipe considers the fixed inventory | **Public entry**, real recipe inventory, actual proof scopes | Must prove the outside known chain can be considered without fabricating target dependencies; final target-only native closure. |

**Needs the production controller/public path:** N3, N4, N5, N7, N8.
**Needs the controller module but not public orchestration:** N1, N2, N6.
The synthetic topology in N3 is not an execution of retained T301 artifacts and is not cost evidence.

## Additional 46.15 coverage

The acceptance file also has three direct graph tests:

1. Known-empty is distinct from unknown; terminal/usable unknown does not expand candidates.
2. An unknown child expands consideration, recomputes stranding scores using real edges, and leaves Req unchanged.
3. A blocked known route does not block an eligible unknown alternative.

Together with N8 and N4, these cover expansion, shrink/blocked behavior, missing-route propagation and no invented proof edges.

## 46.16–46.17 owner matrix

`core/count-owner-budget.test.ts` contains 23 test definitions:

- 46.16(a): only the stopped key's cap doubles; aggregate previous use affects funding, not other caps.
- All eight 46.17 numbered negatives: T301-shaped case retry/body, one-unit-short admission, exact cap preservation, leaf-parent constraint, complete owner sum, hard body stop despite headroom, ownerless/body-owned leaf, cumulative segmented body.
- Repeated segments of one case share the same cap.
- Only completed same-instance/same-root body history contributes; the largest completed use is the floor, partial history is not b_min.
- Post-proposal rescope/stamps and later closing are outside the callback receipt and protected before H through the ancestor endpoint.
- Overlap, unowned work and mismatched leaf parent are hard defects.
- Native producer rejects owners bound to a foreign ledger before body/request execution.
- One unit of live headroom spent after preparation, with the same bank/tickets/parent, starts neither callback nor ticket; a stale root is rejected separately.

The native owner-sum test uses the new explicit `owners` lease option through real `withLiftedCase` / `withLiftedLeaf`; the native ledger, native proof builder and native checker are not mocked. Other owner tests use an explicit all-unit test ledger to make exact arithmetic inspectable.

No test selects a production b0, F, new W, new flag, funding formula or activation. The `297` / `297_000_000` body costs are synthetic fixture work, not 297.556M measurements or same-instance production b_min. A continues to select the flat formula; direct owner tests are API qualification only.

## D early pre-review additions (not a verdict)

The draft now adds seven regression definitions, plus a correction to existing fixtures, against D's source findings:

- D1: after the actual `count-recipe-admission` observation, withdraw the selected known recipe's dependency while an unknown alternative keeps the target unblocked. The known recipe must emit no attempt and spend no ticket; the unknown alternative still closes natively.
- D2: N1/N2 use 60,000 payload ticks, not 80,000, against 40,000 → 80,000 case caps, leaving room for paid trace bookkeeping.
- D3: a plan prepared for tickets A cannot be used with fresh tickets B.
- D3: another bank with the same numerical root epoch does not own the plan.
- D3: an exited parent cannot be replaced by a funded sibling scope.
- D3: false last-moment eligibility starts no producer and spends no ticket, with a fresh eligible positive control.
- D3: ticket generation changed before admission or inside eligibility invalidates the plan; the latter specifically requires a recheck after the callback.

D1 plus six D3 tests add seven definitions; two more distinguish the runner's finalization reserve from direct-owner behavior (12 acceptance + 23 owner = 35). D2 updates existing fixtures. A's proposed API is `countDisjointContext(tickets, bank)` in each admitted plan and `runDisjointCountRound(plan,tickets,run,bank,eligible?)`. All synthetic fixed plans now use that helper with the exact tickets later passed to `run`. The context and eligibility API is now committed in A's candidate `0fc83661` and the draft matches it. This is a source pin, not software/native/qualification approval; no execution result is claimed. Read-only inspection confirms the one-unit-short planner fixture still accounts for its two paid metadata ticks.

### Deadline-unit correction (source only)

The initial B child `76c35b98` incorrectly nested `withWall(performance.now() + 10_000, ...)` under two FULL-work helpers. Inside a work scope `withWall` interprets its argument as a counted endpoint, not a wall-clock timestamp. The correction removes both nested wall wrappers and the unused imports: the existing raw `withBudget` roots and every case/leaf/body cap stay unchanged. Bun's test timeout and the authorized process timeout must bound wall time separately. No new compile or execution result follows.

### Lane C follow-up gaps

C's `6389f17d` review examines A's `0fc83661`, not this unadopted B test child. B N2 constructs/checks two native certificates; N5 exercises public stranded replacement; N8 exercises public unknown-only consideration. None has executed. N3 remains a synthetic T301-shaped public control, **not** a retained real T301 run. Actual real-model retry evidence remains open.

G1 per-member allotment/used/hard-stop observations, G2 typed production context-refusal events and 29-protocol incidence, and G3 capture expiry after a proposal need follow-up controls and receipts. No new G1-G3 test definitions are claimed here; production touch points/policy remain for A/Main agreement.

## Terminal body reserve alignment

A's runner now reserves four ticks **inside** the declared body cap: terminal owner entry, classification, ticket settlement and receipt preparation. Tests preserve the same six/eight productive-body limits by making those tiny total-body fixtures ten/twelve; no case or leaf cap is reduced. Expected completed/interrupted body receipts include the four charged terminal units.

Exact unit controls include: stopped T301-shaped round body 6/sum 7; completed retry body 304/sum 380; false eligibility body/sum 5; cumulative-body failure body 11/case 2/sum 13. Partial history is taken from the actual returned receipt and still does not establish b_min. A body of four gives the runner no productive budget but pays all four terminal units without starting a ticket; direct `CountFundingOwners` has no reserve by default and can use all four declared body units. No free cleanup allowance, cap reduction or skipped negative is introduced.

## Required future verification (not executed)

After the coordinator authorizes the relevant gates:

1. Use parent `0fc836616e98886046cc1c46399d1b071a2b2aaa` and the separate B test child; record any later repair/integration SHA without silently changing the test target.
2. Type-check and run each test file in **separate fresh Bun processes**, with `GDP_WORK_FULL=1`, default fixture weights and the six strategy/prerequisite flags set by the public fixture. Do not run the module-mocking acceptance file beside other suites in one process. Use explicit Bun test and process wall timeouts, never a wall timestamp passed to a counted endpoint.
3. Run the meaningful public-entry negatives against the unwired baseline plus test files. Record each actual assertion failure. Treat a missing new module separately from behavioral RED; do not call an import failure proof of correct sensitivity.
4. Run the stable flat implementation and report N3 RED separately; never hide it behind `.skip`, `.todo`, `test.failing` or a catch returning success.
5. If a disjoint production successor is explicitly authorized, repeat against that SHA and require N3 GREEN while all negative checks still hold.
6. Run the existing related gates and commitlint remotely through `supercomputer`; collect immutable receipts before declaring success. No job spec has been submitted.

Current totals: **35 test definitions drafted; 0 compiled; 0 executed.**
