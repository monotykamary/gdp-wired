# Effect: how stateful logic is written, and what gdp-wired/effect reads

A short survey (2026-10-29) of how projects that use [Effect](https://effect.website) heavily write stateful logic,
done to pick what `gdp-wired/effect` (core/effect.ts) should read. Effect's `latest` is 4.0.7 (2026-10-28); the 3.x
line (`prev`, 3.22.4, 2026-10-22) is still maintained, and many projects are on it.

## What was read

| Project | Effect | What it is | Commit |
| --- | --- | --- | --- |
| [pingdotgg/t3code](https://github.com/pingdotgg/t3code) | 4.0.0-beta (66 to 84) | T3 Code: a desktop and server app for coding agents, written in Effect throughout | 9826dbb |
| [anomalyco/opencode](https://github.com/anomalyco/opencode) | 4.0.1 | opencode, the coding agent: its core, server and CLI in Effect | b799259 |
| [KittyCAD/modeling-app](https://github.com/KittyCAD/modeling-app) | ^3.22.2 | Zoo's CAD app: XState for its machines, Effect at a few edges | 6e6b69b |
| [Effect-TS/effect](https://github.com/Effect-TS/effect) at effect@4.0.7 (b174739) and effect@3.22.4 (5e8c4fe) | | Effect itself: Semaphore, Queue, Ref, SynchronizedRef, SubscriptionRef, TxRef, RateLimiter (4.x persistence), Schema, Match | |

(MapleTechLabs/maple, also on 4.x, was looked at but left out: it is under the Functional Source License.) Uses
outside node_modules and tests, by `rg` over the TypeScript (counts of matches):

| Pattern | opencode | t3code | modeling-app |
| --- | ---: | ---: | ---: |
| `Effect.gen` / `Effect.fn(` | 5,287 / 1,055 | 8,939 / 3,513 | 6 / 0 |
| `Ref.make`, `Ref.update`/`modify` | 58, 37 | 420, 625 | 3, 3 |
| `SubscriptionRef`/`SynchronizedRef` update, modify, set | 1 / 22 | 101 / 54 | 2 / 2 |
| `TxRef` update, modify (v4), STM `TRef` (v3) | 0, 0 | 6, 0 | 0, 0 |
| `ReadonlyMap<`, `ReadonlySet<` | 122, 99 | 385, 393 | 22, 16 |
| `Effect.fail(`, `yield* new E(...)` | 495, 264 | 683, 1,298 | 1, 0 |
| `Schema.TaggedError`, `Data.TaggedError` | 233, 1 | 1,147, 37 | 0, 5 |
| `Clock.currentTimeMillis`, `DateTime.now` | 74, 2 | 222, 514 | 0, 0 |
| `Context.Service` (v4), `Effect.Service` (v3) | 163, 2 | 371, 12 | 0, 0 |
| `Layer.effect`/`scoped(` | 154 | 369 | 1 |
| `withPermits(` / `withPermit(` | 96 | 345 | 1 |
| `Match.value`/`type`/`tag` | 8 | 2 | 9 |
| `Data.TaggedEnum` / `taggedEnum` | 7 | 2 | 0 |
| `.pipe(` | 3,408 | 9,411 | 47 |

## What the code looks like

- **A service is a make effect that creates Refs and returns an object of methods.** `Effect.gen(function* () { const
  entries = yield* Ref.make<ReadonlyMap<string, Entry>>(new Map()); ... return Tag.of({check, record}) })`, given to
  `Layer.effect(Tag, make)`; the tag a v4 `Context.Service` class (v3: `Context.Tag`, or `Effect.Service` with the make
  effect as its `effect` option). Examples: t3code's
  [SourceControlRateLimit](https://github.com/pingdotgg/t3code/blob/9826dbb9904b2591bfbf60d1317486b59132f56b/packages/source-control-core/src/server/SourceControlRateLimit.ts),
  [GitHubQuota](https://github.com/pingdotgg/t3code/blob/9826dbb9904b2591bfbf60d1317486b59132f56b/packages/source-control-github/src/server/GitHubQuota.ts),
  [providerMaintenanceCommandCoordinator](https://github.com/pingdotgg/t3code/blob/9826dbb9904b2591bfbf60d1317486b59132f56b/apps/server/src/provider/providerMaintenanceCommandCoordinator.ts).
- **Methods are `Effect.fn('name')(function* (...) {...})`** (sometimes an arrow returning `Ref.update(...)`), reading
  the Ref once, deciding, and writing it once with a copy: `Ref.update(ref, current => { const next = new
  Map(current); next.set(key, {...previous, retryAt}); return next })`, or `Ref.modify` returning `[result, next]`.
  The state is immutable records in a ReadonlyMap or a ReadonlySet (as often one as the other).
- **Failures are typed errors yielded**: `return yield* new PausedError({...})` (Schema.TaggedError in 4.x code, also
  Data.TaggedError in 3.x code), or `Effect.fail(new E(...))`. They are the step's refusals.
- **Time comes from `Clock.currentTimeMillis`**, read once at the top of a method; `DateTime.now` is mostly a timestamp
  for records, not a decision.
- **Concurrency is a Semaphore of 1 around a method** (`lock.withPermits(1)(...)`), SynchronizedRef, or a TxRef in
  `Effect.tx` (v4); get-then-set across two `yield*`s without a lock also appears.
- **Dispatch is `switch` and `if`**; Match and Data.TaggedEnum are rare in these apps.
- **Combinators in pipes are everywhere** (`Effect.retry`, `catchTag`, `timeout`, `forkScoped`, `ensuring`), mostly
  around calls to the world (HTTP, processes, files), less in the stateful core.
- **Effect's own primitives** are classes with mutable fields and callbacks (Semaphore's `taken` and its waiters, the
  RateLimiter memory store's Maps of counters in `Effect.sync`): not Effect.gen over Refs, so they are written as rules by
  hand and checked against the running code with `conforms`.

## What gdp-wired/effect reads, and what it refuses

Read (core/effect.ts, through core/extract-shapes.ts's factory reader and core/extract-read.ts's executor):

| Pattern | 4.0.7 | 3.22.4 |
| --- | --- | --- |
| make effect: `Effect.gen`, a function returning one, `Effect.fn(...)(function* ...)`, `Layer.effect`/`scoped` of one | tested | tested |
| service classes: `Context.Service` with `Tag.of({...})` (4.x), `Effect.Service` with `effect:` (3.x) | tested | tested |
| `Ref`, `SynchronizedRef`, `SubscriptionRef`, `TxRef` (4.x): get, set, update, modify, updateAndGet, getAndUpdate, getAndSet, setAndGet, the `*Effect` forms | Ref, Ref.modify tested | SynchronizedRef tested |
| state: numbers (integers), booleans, string unions, strings, records, `Map`/`ReadonlyMap`, `Set`/`ReadonlySet`, arrays as lists; typed by a Schema (`typeof S.Type`) as by any type | tested | (same reader) |
| `Effect.fn` / `Effect.fnUntraced` methods and helpers, arrows returning an effect, effects the service keeps | tested | tested |
| `Effect.fail`, `Effect.die`, `yield* new E(...)` (Schema.TaggedError, Data.TaggedError) as refusals | tested | tested |
| `Clock.currentTimeMillis` as an input | tested | tested |
| a Semaphore of 1 (`withPermits(1)`, `withPermit`) as a lock | tested | tested |
| `Effect.succeed`, `Effect.sync`, `Effect.void`, `Effect.log*`, spans and log annotations in a pipe | tested | (same reader) |
| `conforms(rule, service)`: a rule by hand beside the running service | the quota, Semaphore, RateLimiter store, T3 Code | Semaphore |
| `fromSchema`: Struct, Literal(s), tagged Union, Int (and ≥ 0), Boolean, String, NullOr, optional, Class | tested | tested |

Refused, with the reason where it is: a failure after a Ref changed on that path (the Ref keeps it), combinators in
pipes (retry, catch, timeout, forks: their effects aren't read), Match, unions of records as state (Data.TaggedEnum,
Schema unions), STM (3.x's TRef), Refs held in values or made in a step, services and other effects yielded inside a
method or while the service is made (Random, DateTime, a service tag), optional arguments, and everything core/extract.ts
refuses (floats, loops, template strings, other modules' code).

The check runs the code on the Effect given: the service made by `Effect.runSyncExit`, each request run the same way
with a Clock fixed at the request's time (4.x's `TestClock.setTime` yields to its scheduler, which `runSync` can't run:
a Clock whose time is the request's is provided instead, `Effect.provideService(Clock.Clock, ...)` on 4.x and
`Effect.withClock` on 3.x), and the Refs read after it. A take of a Semaphore that would wait leaves, on 4.x, a fiber
that acquires later (runSyncExit returns its AsyncFiberError without interrupting it): `conforms` leaves blocking
requests out.

## The corpus items (research/realworld)

| Item | Code | Laws | Verdicts |
| --- | --- | --- | --- |
| concurrency/effect/Semaphore | Effect 4.0.7 Semaphore.ts, 3.22.4 circular.ts | 6 | 3 proven, 3 refuted: a release past what is taken and a resize below it (laws stated too strongly, both by design), a negative take acting as a release (triaged a minor bug) |
| ratelimit/effect/fixedWindow | Effect 4.0.7 persistence/RateLimiter.ts, layerStoreMemory | 4 | 3 proven, 1 refuted: `options.limit && ...` reads a limit of 0 as none (a minor bug in the store's contract, unreachable through RateLimiter.consume) |
| ratelimit/effect/tokenBucket | the same | 4 | 4 proven |
| ratelimit/t3code/SourceControlRateLimit | t3code 9826dbb | 5 | 5 proven |

Each rule runs beside the real code with `conforms` (research/realworld/repro/conform-effect.ts, 300 runs of 16 requests,
every one agreeing), which also replays each refutation on the real code. The two bugs were reported upstream on 2026-10-29:
Effect-TS/effect#10101 (Semaphore) and #10102 (RateLimiter); both are still there on 4.1.0.
