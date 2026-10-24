# The extractor on real code

`gdp-wired/extract` (core/extract.ts) read on code that ships: each source fetched at its pinned commit, extracted, and
checked against itself by running both (core/extract-check.ts); a difference refuses the extraction.

| File | What |
| --- | --- |
| `sources.json` | 22 examples from open-source code (react.dev, redux, statelyai/xstate, rate limiters), each with repo, commit, path and licence |
| `realworld-sources.json` | research/realworld's corpus as of 6c675e4 on research/realworld (its `sources.json`, 41 entries), read as it is |
| `run.ts` | each source extracted (the entry its `export` names, the whole file, its relative imports fetched from the same commit; a class the corpus names without its methods is read for the public methods in its pinned lines; an XState machine on the XState its code is written for, v4 or v5) |
| `verdicts.ts` | each extracted example's laws proven of the extracted rule and of a rule written by hand, the corpus's way |
| `corpus-verdicts.ts` | the real-world corpus's own laws (research/realworld/items) stated again on the rules extracted from the corpus's code, each proven on both sides the corpus's way (60 s of search; a liveness law with no rank) |
| `fetch.ts` | the files at their commits, cached in `.cache/` (not committed) |
| `collect.ts` | a batch's logs into `results/` |
| `jobs.json`, `corpus-jobs.json` | the batch: the tests, both lists, the verdicts; one job per corpus law (`corpus-verdicts.ts --jobs`) |
| `results/` | the last batch's (`runs/extract2/batch3`, the code of 956e28e): `ours.jsonl`, `realworld.jsonl` (one line per source: extracted or refused, where and why, the check's evidence), `verdicts.jsonl`, `corpus.jsonl` (one line per corpus law: both verdicts, or why it has no statement on the code's rule), `rules/` (the rules extracted, as `toSource` prints them) |

```sh
python3 modal/run.py --backend auto --jobs research/extract/jobs.json --out runs/extract/<name> && sh modal/reap.sh   # with corpus-jobs.json, one batch
bun research/extract/collect.ts runs/extract/<name>
```

Evidence per extraction (`evidence` in each line): runs from the start and their requests, steps from drawn states,
the prover's witnesses (proveSteps refuting "this condition never holds" for each branch condition over the state and
the request; conditions over a map's cells aren't asked), requests both sides refused, steps past the safe integers
(the code rounds, the rule's runtime refuses), steps where the rule's runtime refuses a sum past 2^53 while the code's
values stay safe (`edge`), the generated JavaScript's agreement with the interpreter, and the branch arms of the code the
step reads that the requests reached. An XState machine is checked by `conforms` (runs from the start, every state and
kept context field compared, the actors inert and their answers and the timers sent as XState's own events, only where
they can come); its arms counted are its guards' and actions' (what its actors and effects run is outside it).

## On the corpus's code

Of research/realworld's 41 sources, 5 are extracted now (none before), 36 refused (`runs/extract2/batch3`):

| Source | Read as | Evidence |
| --- | --- | --- |
| upstash-ratelimit `src/cache.ts` (`Cache`, the methods of its pinned lines) | a class over a Map given to its constructor (empty, as `new Cache(new Map())` makes it), records and `number \| null` results | 2,306 requests from the start, 400 drawn states, 8 of 8 conditions reached by the prover's witnesses, 2,695 steps where the generated JavaScript agreed, 6 of 6 arms |
| gapless.js `track.machine.ts` (`createTrackMachine`) | the machine a function makes, its initial context argument as params (a start drawn every 4 runs), spawnChild an actor outside | 3,200 events, 1 of 1 arm |
| vef-framework-react `uploader-machine.ts` (`createUploaderMachine`) | a factory's machine, `deps.abortRequested()` an input, four invoked promises (each done and error an event) | 3,200 events |
| radio-room `radioStreamMachine.ts` | `string \| null` context as maybes, `always`, `after`, an invoked callback actor, an entry action writing the context, `emit` | 3,200 events, 4 of 6 arms |
| open-decision `websocket.machine.ts` | XState v4: `cond`, `(context, event)` guards and actions, `services`, `after` with a named delay; id, yDoc, onSync and token left out (written from payloads nothing kept reads) | 1,612 events (each run ends at its final state) |

The 16 other TypeScript and JavaScript sources, each refused where it is: upstash's three `single.ts` algorithms (the
base class's `limiter: Algorithm<TContext>`, a function value: the step is a closure that sends Lua to Redis), its
`negative-rate.test.ts` (a test's name), medusa's two services (`extends MedusaService(...)`, a mixin), its
`fulfill-item.ts` (`FULFILL_ITEM` is registered by a call, `OrderChangeProcessing.registerActionType(...)`), vendure's
stock movements (a field of shipping checkers, function values) and order process (`configureDefaultOrderProcess` returns
the configuration of vendure's own state machine, not a step), librechat (`mongoose`, a module object), unleash (a
`Math.random` generator field), growthbook (`isIncludedInRollout`, a decision about one request, no state),
express-rate-limit (`interval?: NodeJS.Timeout`, a timer handle of no type the subset reads), rate-limiter-flexible (its base class's setter), electric (`!context.streamResetError`: an `Error | null`
read as a condition) and amplify-ui (`services`, a factory argument whose functions are untyped). 20 sources aren't
TypeScript or JavaScript (Solidity 7, Go 6, Python 2, Ruby 2, Lua 1, Zig 1, CoffeeScript 1).

**The corpus's laws on the extracted rules** (`results/corpus.jsonl`): the four XState items' 33 laws, each stated again
in the extracted rule's terms (its events XState's own names, its context the code's fields) and proven on both sides
the corpus's way. 28 have a statement on the code's rule; 5 read a ghost the item adds (vef's uploads, aborts and
failures counters, and the same beside idle; gapless's spawn counter). Of the 28, 25 get the same verdict (23 proven
on both, 1 refuted on both: radio's "the stream connects only with a url"; 1 unknown on both: open-decision's "a synced
connection resets the retries", broken from a lawful state with no run found), and 3 differ:

| Law | By hand | Extracted | Why |
| --- | --- | --- | --- |
| vef: a started upload ends succeeded, failed or aborted | unknown | proven | the item's model: its six ghost counters are in the state the liveness search fits a rank over; the code's machine has none |
| open-decision: an opening connection ends connected or failed | unknown | proven | the item's model: its hasDoc and hasToken flags (the code's id, yDoc and token as whether they are set) in the state the search ranks; the code's machine keeps neither (no guard reads them) |
| open-decision: CLOSE ends an open connection | refuted (a run of 16 steps) | unknown | neither: the law is broken on both (the code takes no CLOSE); on the extracted rule the prover's random runs found no run in their budget and it stopped at a lawful state whose CLOSE step breaks the law, which the corpus counts as unknown without a run |

The upstash cache isn't compared: the item's rule is the token bucket (single.ts and its Lua) with the cache, and its
laws are about both. The extracted radio rule's laws take 27 to 57 s where the item's take 1 to 3 s: its url and error
are the code's strings (`str()`, an id and a length) where the item interned the url as a natural and kept the error as
a flag, and its eventless transition is read by cases where it lands.

## The Go front end (core/extract-go.ts)

A second language, Go, on the same Model: a struct of the package and its methods, read through Go's own parser and
type checker (core/go/reader.go, go/ast and go/types, printing the typed AST as JSON), executed symbolically into the
Model, then printed, built and checked as the TypeScript extractor's are (core/extract.ts's `fromModel`). The check
(core/extract-go-check.ts) is core/extract-check.ts's `drive` with Go's code side: the package built in its own module
(its go.mod and dependencies) with a generated harness beside it, spoken to through two named pipes (runs from the
start, steps from drawn states, steps from the prover's witnesses, as the TypeScript code is checked); every state,
result and refusal compared, the fields the rule leaves out asked to be unchanged, the blocks reached counted with
`go build -cover`. docs/ARCHITECTURE.md's front-end section has the
subset and its semantics (integers wrapping at their width, pointers aliasing, `*big.Int` unbounded, errors and panics
as refusals).

Which language second: by the items whose rule lives in it, Go reaches 8 of research/realworld/sources.json's items
(rbac, gitea, csr conditions, blnk, gobreaker, flagd, resource quota, x/time/rate) and Solidity 4 (Governor,
TimelockController, ERC20, RefundEscrow); in the 41-source list above, Go 6 items and Solidity 4 (7 files). So Go.

| File | What |
| --- | --- |
| `go-run.ts` | every Go source of research/realworld's sources.json: the package at its commit (`go-fetch.ts`, a sparse checkout), each name its `export` gives read (Type.method, a type the methods in its pinned lines, a method alone; a function read as far as the subset goes, for where it stops); a refused struct's part that extracts (each method alone, then those together) beside it |
| `go-options.json` | what a source's callers do with an object a failed call wrote, with where the code says so (blnk's: dropped) |
| `go-verdicts.ts` | the corpus's own laws on the extracted Go rules, beside the items' rules by hand (one job per law, `go-verdict-jobs.json`) |
| `go-setup.sh`, `go-jobs.json`, `go-one.ts` | Go 1.27.1 in a job where the image has another; the tests and the corpus run; one struct through the front end |
| `results/go/` | `realworld.jsonl` (one line per source) and `rules/` from `runs/front-go/step1/extract` (the code of 146ca37), `corpus.jsonl` (one line per law) from `runs/front-go/go2` |

```sh
python3 modal/run.py --backend auto --jobs research/extract/go-jobs.json --out runs/front-go/<name> && sh modal/reap.sh   # with go-verdict-jobs.json
```

**On the corpus's Go code** (`runs/front-go/step1/extract`): of its 25 Go sources (8 items), 1 is extracted whole and 24 are
refused, each where it is. The one extracted is gobreaker's `v2/counter.go` (`Counts`, an `also` of the CircuitBreaker
item): six uint32 counters, their increments wrapping at 2^32 as Go's do; 2,400 requests in 200 runs from the start,
400 steps from drawn states and 24 from the prover's witnesses (24 of 24 conditions), 2,824 steps where the generated
JavaScript agreed, 8 of 8 blocks. Of blnk's `model/model.go` (the ledger item's rule source), the part that extracts is
`Balance`'s addCredit, addDebit, computeBalance, RollbackInflightCredit and RollbackInflightDebit (its `*big.Int`
balances unbounded integers, nil a state of their own; a failed call's writes dropped, as transaction_execution.go:
536-551 drops them): 2,263 requests in 200 runs, 400 steps from drawn states and 28 from witnesses (28 of 30 conditions), 323 refused on both
sides, 28 steps where the code leaves the safe integers and the rule's runtime refuses, 6 where the rule's runtime
refuses a sum past 2^53 while the code's values stay safe, 34 of 34 blocks. CommitInflight* and UpdateBalances are
refused there: `ApplyPrecision` reads the transaction's float64 `Precision` (model.go:286), `canProcessTransaction` its
float64 `OverdraftLimit` and shopspring/decimal.

The refusals, by reason: an interface argument 7 (gitea's four functions over a `context.Context` and the database
behind it, kubernetes's csr strategy and blnk's `applyTransactionToBalances` over one too, flagd's
`parseFractionalEvaluationDistributions(values []any)`), another module's type 6 (kubernetes's
`authorizer.Attributes`, `*rbacv1.PolicyRule`, `*field.Path`, `[]corev1.ResourceQuota` twice, `corev1.ResourceList`),
floats 3 (blnk twice; x/time/rate's `Limit` is a float64 type), not code to read 3 (a test, a type's documentation, a
Markdown file), 2 tallied as not a declaration (gitea's `MarkReviewsAsStale`, declared in models/issues and called
from services/pull; the csr `CertificateSigningRequestStatus`, a struct with no methods in the lines cited: data, not a
step), a generic type 1 (gobreaker's `CircuitBreaker[T]`), a loop 1
(flagd's `distributeValue`), the clock 1 (x/time/rate's `AllowN(t time.Time)`). No item has its rule source extracted
whole.

**The corpus's laws on the extracted rules** (`results/go/corpus.jsonl`): the two items' 13 laws. 3 have a statement on
the code's rule, all blnk's, and all 3 differ, each for a reason the code gives:

| Law | By hand | Extracted | Why |
| --- | --- | --- | --- |
| every balance is its credits less its debits | proven | refuted (1 step: addCredit(3, posted) from the zero Balance) | the item's step is a whole transaction (UpdateBalances: addDebit or addCredit, then computeBalance); the extracted steps are Balance's methods, one call each, and the identity holds between transactions, not between the calls that make one. UpdateBalances is refused (floats) |
| every inflight balance is its inflight credits less its inflight debits | proven | refuted (2 steps: addCredit, then addDebit(3, inflight)) | the same: computeBalance(true) comes after |
| no inflight debit is ever negative | proven | refuted (1 step: addDebit(−3, inflight)) | the item's amounts are positive because Transaction.validate refuses others inside UpdateBalances (refused); addDebit itself takes any big.Int |

The other 10 read what the extracted code doesn't keep: blnk's sums over every balance (tC, tD, tIC, tID) and what a
balance sourced under (Unbounded, MaxLimit), ghosts the item adds (3); gobreaker's breaker state, generation and expiry
(7), the CircuitBreaker's, refused, where the extracted Counts keeps none.

## Other languages (Python, Java, Rust; Solidity)

The Go front end is the template (docs/ARCHITECTURE.md): the language's own parser and type checker printing JSON, an
executor into the Model with the language's integers as they are (Java's wrap at 2^32 and 2^64 as Go's do, Python's
are unbounded, Rust's panic in debug and wrap in release, a choice the build makes, Solidity ≥ 0.8's revert), and a
runner in its own runtime (python, the JVM, cargo, a local EVM such as anvil) printing the state as JSON for the same
comparison. Solidity's 4 items would be next (ledgers and governance: uint256 state, mappings, `require` as the rule's
refusals with the state rolled back, msg.sender an input).
