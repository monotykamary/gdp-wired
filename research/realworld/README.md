# The real-world corpus

The frontier corpora (`research/frontier/`, `research/frontier2/`) score gdp-wired on academic benchmarks: TIP 2015,
CHC-COMP, TermComp and SV-COMP. This corpus scores it on the job it is built for. It takes real budget, quota,
rate-limit, workflow, ledger, escrow, session and access-policy code from open-source repositories. Each item is that
code written faithfully as a gdp-wired rule, with the laws a reviewer would ask about.

Each law is proven with nothing stated beyond the rule and the law itself:
- `proveRule` or `proveSteps`, with the default search at 60 s per law;
- `proveLeadsTo` with no rank given;
- `proveDecision` for a claim about one request.

    bun research/realworld/jobs.ts > jobs.json                                   # one job per law (311)
    python3 modal/run.py --backend auto --jobs jobs.json --out runs/realworld/<name>
    bun research/realworld/score.ts --from runs/realworld/<name> --md results.md --json results.json
    bun research/realworld/score.ts --item '<item id>' --ms 3000                 # one item's laws, locally
    bun research/realworld/rank0.ts                                              # the liveness diagnostic below
    bun research/realworld/sources.ts > research/realworld/sources.json          # the pinned sources

## The files

| File | What |
| --- | --- |
| `lib.ts` | The item format and the law helpers: the domains, the law kinds, where intent comes from, the gap keys |
| `items/*.ts` | The items, one file per repo or family. Each file's header names the repo, the commit, the licence and the author. Each part of a rule cites the source lines it mirrors. |
| `corpus.ts` | Every `items/*.ts` file's `items`, in file order |
| `jobs.ts`, `score.ts` | The job list (shaped like frontier2's, for `modal/run.py`) and the score |
| `sources.json` | The machine-readable source list, for gen/extract: one entry per file an item mirrors (repo, commit, path, lines, function or export, licence, author, URL) |
| `triage/*.json` | Every refutation, and every law the original code breaks, with its verdict (`bug`, `model`, `law`), a note and its repro |
| `repro/` | Harnesses that run the original code at the pinned version: counterexamples replayed (`<name>.ts`, `.py`, `.go`, `.rb`, `.sh`) and conformance runs of the rule against the original (`conform-*.ts`) |
| `results.md`, `results.json` | The scored run below: every law, its outcome, its time, and what the search found or where it stopped |

**Licences.** Only MIT, Apache-2.0, BSD-2/3 and ISC code is used (rate-limiter-flexible is ISC). Only the short excerpts
the mapping comments need are quoted, each with attribution; the rest is linked by repo and commit. The repro
harnesses fetch or install the original code into a temporary directory. None of it is vendored here.

## The score

Run `runs/realworld/r1` on 2026-10-23, at 1907a00 (the corpus as committed; later commits changed only metadata and
the scorer). It was 311 jobs on Modal (`--backend auto`, which fell back from boat for want of starts), at 2 vCPU each,
with a 60 s search per law and every job killed at 150 s.

| Domain | Items | Fully expressible | Laws | Proven | Refuted | Unknown | Timeout |
| --- | --- | --- | --- | --- | --- | --- | --- |
| rate limit | 7 | 0 | 30 | 15 | 3 | 12 | 0 |
| quota | 3 | 0 | 17 | 11 | 1 | 5 | 0 |
| ledger | 4 | 1 | 27 | 15 | 0 | 12 | 0 |
| payment | 4 | 0 | 23 | 15 | 3 | 5 | 0 |
| auth | 4 | 0 | 23 | 19 | 0 | 4 | 0 |
| access | 4 | 1 | 27 | 24 | 2 | 1 | 0 |
| xstate | 6 | 0 | 47 | 38 | 2 | 7 | 0 |
| queue | 4 | 0 | 26 | 18 | 0 | 8 | 0 |
| circuit breaker | 4 | 1 | 30 | 21 | 0 | 9 | 0 |
| feature flag | 3 | 0 | 18 | 17 | 0 | 1 | 0 |
| inventory | 4 | 0 | 19 | 10 | 4 | 5 | 0 |
| approval | 4 | 0 | 24 | 15 | 0 | 9 | 0 |
| **all** | **51** | **3** | **311** | **218** | **15** | **78** | **0** |

**Expressibility.**
- 3 of 51 items (5.9%) are fully expressible, meaning every part of the step is said exactly as the code does it: OpenZeppelin's RefundEscrow, Casbin's effector and Polly's breaker.
- 9 of 51 (17.6%) have no language gap: what they leave out is left out by choice (`scope`) or is state another system holds that the request carries (`external`).
- No item was inexpressible as a whole. Every one has laws that run.

**Laws proven with nothing stated.**
- 218 of 311 (70.1%). Counting the 10 laws a reviewer would ask about that the language can't state, it is 67.9%.
- By kind: safety 70 of 100, step 116 of 141, access 32 of 35, liveness 0 of 35.
- 29 of the 311 laws are false: the 15 refuted, 13 the original code breaks with no run found, and one law error kept as stated. Of the 282 laws believed true, 218 (77.3%) are proven.
- No false law was proven. Every triaged `bug` and `law` entry is refuted or unknown, or was restated before scoring.

**Search.**
- 26 of the 218 were proven only through what the search found, mostly invariants. Examples:
  - RefundEscrow's "no more is paid out than was deposited", through `balance + toBeneficiary <= deposited` and choice-guarded bounds, in 9.3 s.
  - better-auth's OTP laws, through case splits over the lock flags.
- Median time per law: 664 ms over all 311, 658 ms over those proven. 8 laws took over 100 s: 7 of TigerBeetle's and Gitea's pair law (103 s); none reached the 150 s kill.

**Refuted.** All 15 are suspected real bugs: the original code does what the run shows (below). None is a modelling
error. While the items were written, 4 modelling errors and 14 law errors were found and fixed or restated first.

**The 78 neither proven nor refuted:**

| Count | Why |
| --- | --- |
| 31 | Not inductive alone, and the search found no invariant that proves it. Among them, the laws that need a sum over a map's keys: an ERC20 balance at most the total supply, a refundee's deposit covered by the escrow's balance, LibreChat's reserved total. |
| 28 | Liveness: no rank found ("0 helpful steps sampled lower") |
| 7 | Liveness: a rank fitted to the runs that the kernel's goals don't accept |
| 7 | TigerBeetle: the prover's budget runs out on the kind laws of its map of transfers ("every T cell is a value of its kind") before reaching the law |
| 4 | A step law broken from a state no run was shown to reach |
| 1 | The library threw: `discover` on p-retry's delay recurrence, `RangeError: 290760102328562900 is not a natural` (`core/discover.ts`, `termOfSide`) |

13 of the 78 are laws the original code breaks, each shown by a repro, where the search found no run in its budget
(cockatiel, opossum, express-rate-limit, Medusa, Vendure, Saleor, Keycloak, open-decision).

**Liveness, with a rank stated (a diagnostic, not part of the score).** `rank0.ts` proves every liveness law again
with the constant rank 0 stated, which means each helpful request reaches `to` in one step. No invariant is given.
- **19 of 35 are proven.** For these the language and the kernel were never the obstacle. The rank search misses
  the trivial rank. `findLeadsTo` keeps a helpful sample only when the step stays in `from` and short of `to`, so when
  every helpful step reaches `to` at once it has nothing to fit.
- **The other 16** need an invariant beside the rank, or a real rank. One example is RefundEscrow's refund: the helpful
  withdrawal needs the deposits to be covered by the balance.

### The language gaps, ranked by the items they touch

`(scope)` (23 items) and `(external)` (21) are not the language's and are left out of the ranking. Every gap's exact
construct is in its item's `gaps`.

| Rank | Gap | Items | What it blocks |
| --- | --- | --- | --- |
| 1 | `async` | 19 | No timers, promises or interleavings. Approximated faithfully by sending time and each callback in as requests (admission and outcome as two requests, so they interleave as in the code). It blocks nothing whole. The cockatiel bug was found only because of this split. |
| 2 | `float` | 16 | Binary floats (x/time/rate's float64 tokens, opossum's error percentage, Upstash's weighted floor) and BigNumber decimals (Medusa, Blnk). Taken in integer units, which is exact where the code's values are whole numbers and an approximation otherwise. |
| 3 | `unbounded-collection` | 8 | A list scanned in order: first match over a rule list (Kubernetes RBAC's RulesAllow), flagd's cumulative weights, a COUNT over a table (Gitea's approvals, its law unstated), gobreaker's rolling buckets. |
| 4 | `nonlinear` | 7 | Rate × elapsed time (x/time/rate, Upstash's liveness), threshold × count (opossum), retryDelay × 2^n (pg-boss), flagd's hash × total. The rule says it; the prover does not decide it. |
| 5 | `chart-subset` | 6 | No real XState machine was taken by `fromXState` as shipped (below). |
| 6 | `string` | 5 | Globs and prefixes (Kubernetes' URL `prefix*`), Unleash's constraint operators, Casbin's pattern matching. |
| 7 | `hash` | 3 | Unleash, GrowthBook and flagd bucket by murmurhash. Taken as an input in the hash's range, which is faithful for every rollout law here (the value depends only on the user and the seed). |
| 7 | `recursion` | 3 | Role inheritance to any depth (Casbin, beyond maxHierarchyLevel 1), Cedar's `in`, Unleash's parent features. Blocks transitivity laws. |
| 9 | `two-key-map` | 2 | ERC20's allowance[owner][spender] and Casbin's link table, encoded as one key `a·2^k + b`. Exact only below a bound. |
| 9 | `dynamic-policy` | 2 | A policy file translated by hand (Cedar), a Mongo-style condition (GrowthBook) |
| 11 | `two-run` | 1 | flagd stickiness as the weights change: `relate` compares two requests, not two runs. Two laws unstated. |
| 11 | `batch` | 1 | TigerBeetle's linked chains (all-or-nothing) and its expiry pulse over every due transfer |
| 11 | `time` | 1 | LibreChat's calendar-month refill interval |

**XState.** `fromXState` refused every machine as shipped (`repro/xstate-refusals.ts`). The constructs, by the
machines that use them:

| Construct | Machines |
| --- | --- |
| `invoke` | 5 of 6 |
| inline guards or actions | 3 |
| `after` | 3 |
| entry/exit actions writing the context | 3 |
| `always` | 2 |
| a parallel state below the root | 1 |
| v4 `cond` | 2 |

- **gapless.js** went through `fromXState` once its two inline pieces were named. It conforms to XState's own actor
  over 19,200 steps (`repro/conform-gapless.ts`).
- **The other five** are charts written by hand.
- **v4 `cond` is a library bug, not a gap.** `fromXState` reads only v5's `guard`, so a v4 config is accepted with its
  guards dropped silently: a `cond: 'never'` transition is still taken. It should refuse `cond` or read it.

## Suspected real bugs

The original code does each of these, and each contradicts the code's documented or obvious intent. Nothing was
reported upstream: these are for the user to decide on. Under "Found by", "refuted" means the scored run found a run
or a counterexample request; "unknown" means the prover left the law open and the run was found by `search` or by hand
from the model.

| # | Code | What it does | Found by | Evidence | Confidence |
| --- | --- | --- | --- | --- | --- |
| 1 | opossum 10.0.0, `allowWarmUp` | A breaker that goes half-open during warm-up ignores its trial call's failure (the warm-up check returns before the half-open one). From then on it rejects every call, even after warm-up ends. | unknown | `repro/opossum-warmup-halfopen.ts` runs the npm package | high |
| 2 | opossum 10.0.0, restore from `toJSON().state` | `LAST_TIMER_AT` is set only in the constructor, so a breaker restored from a state that just opened comes back half-open and lets a call through at once | unknown | `repro/opossum-lasttimerat.ts` | high |
| 3 | cockatiel 3.2.1 `ConsecutiveBreaker` | A call that started while Closed and fails after the circuit went half-open reopens it while the test is still in flight. The next call starts a second test, and the first test's success closes the circuit with the second still running. | unknown (found by `search`) | `repro/cockatiel-stale-failure.ts` runs the npm package | high |
| 4 | express-rate-limit (MemoryStore with `skipFailedRequests`) | The middleware decides "the window has reset" from the client's `Date`, which `resetClient` moves forward in place. So a slow request from the old window that fails is taken back from the new window. | unknown | `repro/express-rate-limit-decrement.ts`, on a real express server: limit 1, and the new window lets 2 through | high |
| 5 | Medusa inventory module 2.22.0 | `createReservationItems` checks each item of a batch against the level read before the batch, so two reservations of 1 reserve 2 against a stock of 1. Moving a reservation to another location checks 0 more at the new one and never applies the old one's −quantity. Restoring a live reservation adds it again. | refuted, plus 2 unknown | `repro/medusa.ts` runs the module's own code over in-memory storage. The workflows may guard some paths. | medium-high |
| 6 | Vendure 2.3.4 `StockMovementService` | Releases and sales are taken from the line's Allocation records, which are never reduced, so a second release (or a release after a sale) frees the same stock again: `stockAllocated` reaches −1. `OrderModifier.updateOrderLineQuantity` can trigger it. | refuted | `repro/conform-vendure.ts` runs `@vendure/core` | medium-high (needs a caller that does it) |
| 7 | Vendure 2.2.7 default order process | `if (toState === 'Cancelled') return` in onTransitionStart skips the documented `checkAllItemsBeforeCancel` from ArrangingAdditionalPayment, so a placed order with a live line is cancelled. The same cancel from PaymentAuthorized is refused. | unknown | `repro/conform-vendure-order.ts` runs `@vendure/core`'s OrderStateMachine | high |
| 8 | Saleor 3.23.44 `deallocate_stock` | One Stock instance per allocation, each `F() − n`, saved with `bulk_update`. With two lines on one stock, Django keeps only the first duplicate, so one line's decrement is lost and `quantity_allocated` drifts. | refuted | `repro/saleor-bulk-update.py` runs Django 5.2.18 on Saleor's models and loop: 3 left allocated against 0 in the allocations | medium (needs two lines of one variant at one warehouse) |
| 9 | Upstash ratelimit 2.2.0, fixedWindow and slidingWindow | The Lua increments before checking, so a refused large request still uses up the window: with 10 tokens and 8 used, a rate of 5 is refused and a following rate of 2 is refused too. tokenBucket was fixed for this in PR #156. | refuted | `repro/upstash-rejected-consumes.ts` runs the package's TS and Lua (luajit, a stand-in Redis) | medium (fixedWindow's docs say every request "increases a counter": may be by design) |
| 10 | golang.org/x/time/rate `AllowN` | A grant sets `lim.last = t` even when `t` is before `last`, so time is credited twice: 7 events granted where burst + rate·t allows 6. Concurrent callers read `time.Now()` before the lock, so this happens in practice. | refuted | `repro/go-rate-backwards.ts` runs the module with Go | high; already reported upstream as golang/go#65508 (open) |
| 11 | LiteLLM 1.106.2 `team_max_budget_check` | Refuses only at `spend > max_budget`, where the key, user and org checks use `>=`, so a team at exactly its budget gets one more request | refuted | `repro/litellm-team-budget.py`; the repo's own BUDGET_CODE_MATRIX.md lists it as an inconsistency | high (low severity) |
| 12 | Medusa order module 2.22.0, RETURN_ITEM | Returns are checked against fulfilled minus requested, not minus received: fulfil 1, then return, receive, return, receive leaves 2 received of 1 fulfilled. Negative quantities pass too. | refuted | the action code; `repro/conform-medusa-order.ts` runs the package | medium (module level; the admin route takes any number) |
| 13 | Medusa order module 2.22.0, WRITE_OFF_ITEM | Checks each action's quantity, not the total: two write-offs of 2 write off 4 of 2 | refuted | as above | lower (the claim workflows weren't traced) |
| 14 | Solidus 4.8.0 `Spree::Payment` | A refund is valid on a pending payment; a later partial `capture!` sets `amount = captured_amount` below the refunds | refuted | reasoned from the source (`repro/solidus-refund-capture.rb`, not run) | medium |
| 15 | Keycloak 26.8.1 brute-force protector | `notBefore` is capped at Integer.MAX_VALUE seconds and compared with `now/1000`, so from 2038-01-19 no temporary lockout ever takes effect | unknown (the run needs now ≥ 2^31 s) | reasoned, with the Java arithmetic evaluated (`repro/keycloak-y2038.ts`; no JVM here) | high (a Y2038 issue) |
| 16 | open-decision websocket machine (xstate 4.34.0) | No state handles CLOSE, so the socket's cleanup never runs and a later OPEN for another tree is ignored | refuted | `repro/open-decision-websocket.ts` runs the machine | high |
| 17 | open-decision websocket machine | `connection.ready` is never handled, so retries only grow, and ten drops over a session end in error even with good reconnects | unknown | same repro | medium (intent inferred) |
| 18 | radio-room `radioStreamMachine` | The root SET_URL skips `hasUrl`, so SET_URL `""` while playing starts a playback with an empty url (the app's test: "waits for a url before starting") | refuted | `repro/radio-room.ts` | high (minor) |
| 19 | cedar-examples document_cloud | policies.cedar has no permit for DeleteDocument, though the README says owners delete their documents | refuted | `repro/cedar-documentcloud.ts` runs cedar-wasm 4.14.0 | high (an example policy set) |
| 20 | cedar-examples document_cloud | The README's Public is "an un-authenticated user", but the forbid at :108-109 denies every unauthenticated request; entities.json names `Public::"unauthenticated"`, the policies `Public::"public"` | refuted | same repro | low (the intent is ambiguous) |

Every one of them is in `triage/*.json` with the law it breaks and its notes.

## Modelling lessons

- **Faithfulness checks pay.** 14 conformance harnesses (`repro/conform-*.ts`) run the original package beside the rule's
  interpreter on random request sequences. Two of them caught modelling errors before scoring:
  - Vendure's order process: an early return that skips a whole check, not one part of it. Fixing it exposed bug 7.
  - Vendure's stock level row created on first use.
  
  Two harnesses at first tested nothing: their random generators drew zeros (an LCG's low bits, an overflow past
  2^53).
- **Law errors are common, and the counterexample shows the intent.** 14 laws were stated too strongly and restated
  after the original code was run on the counterexample:
  - RefundEscrow's deposits after Close;
  - Kubernetes' `ResourceNames: [""]`, its status writes and its CSR certificates set before approval;
  - pg-boss's resume;
  - Governor with a second timelock proposer;
  - Medusa's cancelled fulfilments;
  - LiteLLM's overlapping requests.
  
  Each keeps a comment and a `law` triage entry.
- **Split what the code awaits into two requests.** A call in flight as admission and outcome, a timer as an event,
  each callback as a request: that is what found the breaker bugs (stale outcomes) and the express-rate-limit bug.
- **What was hard to say:**
  - Sums over a map's keys: the commonest reason a true law stays unknown.
  - Maps keyed by two values.
  - First match over a list.
  - Two runs under different params.
  - Statechart constructs beyond the subset.
- **DSL behaviour the authors tripped on (none of it changed here):**
  - A step law can't read `.fns`: Keycloak's `sec(now)` became a ghost.
  - `refuteByRuns` skips any rule that reads a non-arithmetic function, so a `floor(now / window)` written with `fn`
    hides every refutation. The Upstash items take the quotient as an input pinned by `.assume` instead.
  - `forall` can't sit under `.or` (`hasForall` reads `undefined.op`); write `forall(k => p.or(...))`.
  - Booleans in charts and map cells need `yes`/`no`, not `true`/`false`.
  - A term as a flag crashes; an input can't share a state variable's name.
  - A flag inside a map's key makes the kernel throw "unknown flag" (ERC20, TigerBeetle).
  - `proveDecision` ignores the time budget: a `relate` ran 120 s.
  - `r.decode` leaves out maps of plain naturals.
  - `encodeParams`' type lists the rule's `.fns` beside its params.

## For the library (not changed here: core/, kernel/ and lean-kernel/ are untouched)

Since fixed (CHANGELOG, "What the real-world corpus found"): items 1, 4 and 5 below, and the traps above it names
(`fromXState` and v4's `cond`, a flag in a map key, `refuteByRuns` and functions, `proveDecision`'s budget). The
corpus again beside main, both on Modal: 237 proven, 16 refuted (the 15 bugs and one law error, BullMQ's, triaged),
58 neither; liveness 18 of 35 (`runs/rwfix/score`, `runs/rwfix/base`).

1. **The no-rank liveness search** (`findLeadsTo`) misses the constant rank whenever a helpful step reaches `to` at
   once. That is 19 of the 35 liveness laws, which `rank0.ts` proves with rank 0. Trying the constant ranks first would
   move the liveness score from 0 toward 19.
2. **Laws over a sum of a map's keys.** A ghost total is the route the docs give; the search doesn't propose one.
3. **The kind laws of a wide map** exhaust the prover's budget before the law (TigerBeetle, 7 laws).
4. **`fromXState`:** read or refuse v4 `cond`; `invoke`, `after` and `always` block most real machines.
5. **`discover`** throws on a recurrence whose step multiplies two unknowns (p-retry).
6. **Deeper runs.** 13 false laws stayed unknown because the search's runs (depth 24) didn't reach the bug; `search`
   by hand at depth 8 found the cockatiel run.

## Cost

| Run | Jobs | Wall | Job time | Hardware |
| --- | --- | --- | --- | --- |
| The scored run | 311 | 551 s | 2,077 s | Modal (boat had no starts left), 2 vCPU and 4 GB each |
| The pilot | 7 | 38 s | 20 s | Modal, same |

Together that is about $0.05–0.10 at Modal's CPU and memory prices. The prover itself ran 1,995 s in all, 8 of the
laws over 100 s. Everything else ran locally: the authors' 3 s checks, the repro and conformance
harnesses, and `rank0.ts` (35 proofs, 6 minutes, most of it TigerBeetle's). `modal/reap.sh` ran after each batch.
