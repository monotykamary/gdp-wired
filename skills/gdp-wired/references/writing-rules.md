# Writing rules and laws

Every name a builder declares comes back typed in each callback: a law that
reads a request input, or a misspelled name, is a TypeScript error. Nothing in
the builders is trusted; they compile to the plain machine the kernel checks.

## The rule

```ts
import {bool, forall, nat, proveSteps, rule} from 'gdp-wired'

const caps = rule('caps')
  .params({d: nat})                                  // fixed for a run
  .inputs({acct: nat, day: nat, ok: bool})           // each request
  .maps({Acct: 0, Day: 0})                           // per-key state, every cell starting at 0
  .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
  .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
```

- `.state({s: 0})` for scalars; any kind with `kind.from(init)`:
  `.state({open: bool.from(true), status: oneOf('new', 'done').from('new'), note: maybe(nat).from(null)})`.
  `.ints({...})` and `.decimals(places, {...})` are shorthand.
- A flag is decided once per step, before the step; read it in the step and in laws' `when`.
- Each map is written once per step (`M.set(k, v)`, `M.bump(k, cond)`), or at every key with `M.each(k => ...)`.
- `.pre(p => ...)` constrains the params; `.assume(env => ...)` constrains each request.
- `when(c, a, b)` chooses between two values of any kind. `minus` is truncated at 0.

## Laws

```ts
const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
const onlyUp = caps.stepLaw('no count goes down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))
const once = caps.stepLaw('a grant adds one to its day', ({day, Day}, after) => after.Day.at(day).eq(Day.at(day).plus(1)), ({granted}) => granted)
const twice = caps.stepsLaw('two grants on one day add two', 2,
  ({day, Day}, after, [, next]) => next!.day.eq(day).implies(after.Day.at(day).eq(Day.at(day).plus(2))), ({granted}) => granted)
proveSteps(caps, [dayCap], [onlyUp, once, twice]) // {proven: true, checked: true}
```

- `law`: holds after every sequence of requests. Reads params, state, maps, sums; `forall(k => ...)` for every key.
- `stepLaw(name, then, when?)`: about one step; `after` reads the state and maps after it.
- `stepsLaw(name, k, then, when?)`: k steps in a row (k ≤ 16); the third argument holds each step's request.
- Step laws assume the laws you pass beside them (`proveSteps(rule, laws, stepLaws)`).

## Histories

```ts
const window = rule('window limit')
  .params({w: nat, c: nat, now: nat})
  .inputs({forced: bool, t: nat})
  .log('forced', 't')                                                       // what each kept record holds
  .sums({ours: (r, {now, w}) => count(r.forced.not().and(r.t.atMost(now), now.lt(r.t.plus(w))))})
  .queries({seen: (r, {t, w}) => count(t.lt(r.t.plus(w)))})                 // computed from the log at the request
  .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
  .keep(({forced, admitted}) => forced.or(admitted))                       // which requests are logged
  .relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
proveRule(window, [window.law('at most c admitted in any window', ({ours, c}) => ours.atMost(c))]) // proven
```

A relation is proven one record at a time and then assumed at every step.
`.prune(order, after)` lets the runtimes drop records that can no longer count.

## Liveness

```ts
const everyTicket = tickets.leadsTo('every ticket issued is served', {
  from: ({t, next, served}) => t.lt(next).and(served.atMost(t)),
  to: ({t, served}) => served.gt(t),
  rank: ({t, served}) => t.plus(1).minus(served),   // a natural (or several, compared in order) no waiting step raises
  helpful: () => ({op: 1}),                         // the request that lowers it; or [{when, request}, ...]
})
proveLeadsTo(tickets, [noneEarly], everyTicket)
```

"Whenever `from`, later `to`", in every run that sends each helpful request
infinitely often. A helpful request names only the inputs it fixes.

## Decisions, pure functions, two runs

```ts
const trial = rule('trial').inputs({plan: oneOf('free', 'pro'), spent: maybe(nat), allowance: maybe(nat)})
proveDecision(trial.decide('a missing fact means no trial', ({spent}) => spent.isNone,
  ({plan, spent, allowance}) => plan.match({free: () => spent.match({none: () => yes, some: s => allowance.match({none: () => yes, some: a => s.atLeast(a)})}), pro: () => yes})))

const price = fun('price').params({cap: nat}).inputs({qty: nat, unit: nat})
  .returns(({qty, unit, cap}) => ({total: min(qty.mul(unit), cap)}))
proveDecision(price.law('never above the cap', () => [], ({total}, {cap}) => total.atMost(cap)))

const answer = fun('answer').inputs({q: nat, key: nat}).returns(({q}) => ({a: q.plus(1)}))
proveDecision(answer.relate('the key never changes the answer', (a, b) => a.q.eq(b.q), (x, y) => x.a.eq(y.a)))
```

`match` must cover every case. `relate` compares two calls under the same
params (noninterference); a counterexample shows the second call as `b.<input>`.

## Records and variants

```ts
import {bool, fun, nat, no, oneOf, proveDecision, record, rule, variant, when} from 'gdp-wired'

const Pay = variant({card: {amount: nat, verified: bool}, cash: {amount: nat}})
const approve = fun('approve').inputs({pay: Pay, who: record({limit: nat, blocked: bool})})
  .returns(({pay, who}) => ({ok: who.blocked.not().and(pay.match({card: c => c.verified.and(c.amount.atMost(who.limit)), cash: c => c.amount.atMost(200)}))}))
proveDecision(approve.law('an unverified card is never approved', ({pay}, out) => [pay.match({card: c => c.verified.not(), cash: () => no}), out.ok], () => no))
approve.run({pay: {tag: 'card', amount: 40, verified: true}, who: {limit: 100, blocked: false}}) // {ok: true}

const Held = variant({idle: {}, holding: {amount: nat, since: nat}})
const hold = rule('hold').inputs({op: oneOf('hold', 'refund'), amount: nat, now: nat}).state({at: Held.from({tag: 'idle'})})
  .step(({op, amount, now, at}) => ({at: when(op.is('hold').and(at.is('idle')), Held.make({tag: 'holding', amount, since: now}), when(op.is('refund'), Held.make({tag: 'idle'}), at))}))
```

- A record is an object of its fields' values; a variant's fields are read only in `match` (every case, by name), and
  `is(case)` tests the case. `Held.make({tag, ...fields})` builds a case to write or to pass to `when`; `same(a, b)`
  compares two values of one kind part by part.
- At runtime a record is an object with exactly its fields and a variant `{tag, ...that case's fields}`; anything else
  throws a `RangeError`, as a value outside any kind does.
- They are their fields' variables underneath (`pay.card.amount`, the case's index as `pay`), so every prover,
  runtime and the Lean export take them as they are. That a state variant is one of its cases is `r.kindLaws()`, proven
  by proveRule and proveSteps on their own.
- In maps and lists: `.maps({Acct: record({limit: nat, spent: nat}).from({limit: 0, spent: 0})})` gives `Acct.at(k)`
  (a record), `Acct.set(k, value)` and `Acct.each(k => value)`; `.items({Queue: Job})` a list of them with `Queue_len`,
  `push`, `pop`, `set`, `insertAt`, `removeAt`, `apply(...ops)`, `has(x)`, `within()`, `increasing(by)`. A map of variants
  keeps every cell one of its cases by itself: `r.kindLaws()` (proven by proveSteps beside your laws; pass them to
  `toLean` with the rest) (`examples/datatypes.ts`, seats).
- `variant({...}, {tag: 'kind'})` names the case by another key at runtime; `optional(c, value)` is a result that may be
  missing (`null` from `run`).
- Not as values: recursive types (a tree). The name `r` is a history's record.

## Loops

```ts
const gcd = loop('gcd').params({A: nat, B: nat}).state({a: ({A}) => A, b: ({B}) => B})
  .pre(({A, B}) => A.atLeast(1).and(B.atLeast(1)))
  .while(({a, b}) => a.eq(b).not())
  .body(({a, b}) => ({a: when(b.lt(a), a.minus(b), a), b: when(a.lt(b), b.minus(a), b)}))
  .rank(({a, b}) => a.plus(b))
proveLoop(gcd, [gcd.law('a >= 1', ({a}) => a.atLeast(1)), gcd.law('b >= 1', ({b}) => b.atLeast(1))]) // halts
```

`while` and the rank read the state and params, never a turn's input.

## Sets, lists, functions, composition

- `.carries('Candidate')`: a set the request brings; `everyKey`, `has`, `subsetOf`, `disjointFrom`, `sameAs`;
  `someKey(k => ..., witness?)` (`examples/sets.ts`, `examples/quantifiers.ts`).
- `.lists('Scope')`: a list with `Scope_len` (`examples/lists.ts`).
- `.fns({perMinute: divBy(60)})` or `fn(arity, js, {facts, lean})`: the kernel knows a function only by its facts
  (`examples/functions.ts`).
- `recur('delay', {zero: 1, next: (x, d) => min(d.times(2), 64)}, {'at most 64': (x, d) => d.atMost(64)})`: a function
  defined by a recurrence, its lemmas proven by induction when it is made, then facts any rule that reads it uses; with
  `args: ['cap']` it takes further arguments (up to four), with `fns: {rem: modBy(7)}` its step and its start read other
  functions, and a fourth
  argument states laws between two points (`(x, fx, y, fy) => fx.atMost(fy)`, for every x <= y)
  (`examples/lemmas.ts`, [Lean handoff](lean-handoff.md)).
- `gdp-wired/compose`: `product`, `interleave`, `refinement(impl, spec, {relation, witness, stutter})`, `steps`,
  `ghost(m, {name: ever(...) | count(...) | total(...)})` for orderings at any distance (`examples/composition.ts`).
