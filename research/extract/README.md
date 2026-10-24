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

## A second front end (Python, Go, Java, Rust; Solidity)

The other languages are out of this round. A front end would follow the C one's pattern (compare/term/c2ari.py): the
language's own parser and type checker, a subset with the language's exact semantics, refusals where it leaves them,
and an intermediate the rest reads. Here that intermediate is the extractor's Model (core/extract-read.ts: the state's
variables and maps, the step's terms over them, the refusals, how a request is made of the code), so the printer, the
sorts and the rule are shared, and only two pieces are the language's:

- **the reader**: its AST and types (Go's `go/types` from a small Go program emitting JSON; Python's `ast` with its
  annotations; javac or JavaParser; rust-analyzer or `syn`; solc's AST JSON), executed symbolically into the Model, with
  its integers as they are: Go's and Java's wrap at 2^64 and 2^32 (a rule's numbers would need the modular arithmetic
  c2ari.py has, or a refusal past the range, as JavaScript's past 2^53), Python's are unbounded (the simplest), Rust's
  panic on overflow in debug and wrap in release (a choice the build makes), Solidity ≥ 0.8's revert (a refusal, as a
  throw is here);
- **the check's runner**: the code run in its own runtime beside the rule (a subprocess per language: python, `go run`,
  the JVM, cargo, a local EVM such as anvil), driven through a harness that makes the object, calls the entry, and
  prints its state as JSON for the same snapshot comparison core/extract-check.ts makes.

The corpus's 7 Solidity contracts would come first (ledgers and governance: uint256 state, mappings, `require` as the
rule's refusals, msg.sender an input), then Go's 6 (gitea's reviews, kubernetes's validation, x/time/rate's floats would
be refused).
