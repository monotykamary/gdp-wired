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
- By default the search may prove a step law with invariants it finds, which hold only in states reachable from the
  start; the verdict then says `assumes: {states: 'reachable', laws}`. If your code steps the compiled rule from states
  it is handed, prove with `{from: 'any'}`: every step law then holds from every state the laws allow
  ([reading verdicts](reading-verdicts.md#from-any-state-from-any)).

## Sums over a map's keys

```ts
const token = rule('token').inputs({op: oneOf('mint', 'transfer', 'burn'), from: nat, to: nat, value: nat})
  .state({supply: 0}).maps({Bal: 0})
  .flags(({op, from, value, Bal}) => ({mints: op.is('mint'), moves: op.is('transfer').and(Bal.at(from).atLeast(value))}))
  .step(({from, to, value, supply, Bal, mints, moves}) => ({
    Bal: Bal.each(k => Bal.at(k).minus(when(moves.and(k.eq(from)), value, 0)).plus(when(mints.or(moves).and(k.eq(to)), value, 0))),
    supply: when(mints, supply.plus(value), supply)}))
proveRule(token, [token.law('the balances sum to the supply', ({Bal, supply}) => Bal.sum().eq(supply)),
  token.law('no balance exceeds the supply', ({Bal, supply}) => forall(k => Bal.at(k).atMost(supply)))]) // proven
```

- `M.sum()`: the sum of every cell of `M`, exact over every key (no bound on the keys). `M.sum(cell => ...)` sums a
  term of the cell (a count: `M.sum(c => when(c.gt(0), 1, 0))`); on a map of records, `R.sum(r => when(r.deleted, 0, r.amount))`.
  Use it in laws, flags, the step or the assumption; it reads like a state variable (`sum$M`) the step keeps exact.
- A law that reads a sum leaves its rule as it is: the rule's machine, `compiled()` and `decode` gain `sum$M` only when
  the rule's own flags, step or assumption read it. `proveRule`, `proveSteps`, `proveLeadsTo` and `crossCheck` add the
  sums their laws read, and `crossCheck` checks what your callbacks write, not the sum's bookkeeping. Handing a machine
  to the kernel yourself (`toLean`, `gdp-wired/prove`), take `rule.withSumsOf(...laws).machine`.
- The map must start where the term is 0 (`.maps({Bal: 0})`), be part of the state (not a carried set or a function),
  and each step must change the term at keys it names: a write at one key, or a write at every key whose value compares
  the key with terms (`k.eq(from)`, `k.eq(to)`) and keeps every other cell. A write that moves every cell (`M.at(k).plus(1)`)
  has no finite sum: the law about it is not proven.
- The kernel knows a sum by two facts: a step moves it by the term's change at the keys it writes, and the term at any
  key, with the keys the step writes, is at most the sum (`M[t] <= sum`, and `M[t] + M[from] <= sum` when t isn't from).
  So a cell law like "no balance exceeds the supply" is proven from the sum's law; alone, the search adds the sum of
  each map the step writes and finds that law itself (`found: sum$Bal <= totalSupply`).
- The runtimes keep the sum as state (one subtraction and one addition a step), so reading it costs nothing.
- In Lean (Sums.lean): `sum_holds` (every reachable state's sum variable is the sum of its term over the keys, `IsSum`),
  `sum_allowed` (there the machine allows exactly what the rule's assumption allows) and `sum_project_laws` (a law proven
  with a sum the rule doesn't read is a law of the rule).

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

Under strong fairness, `fairness: 'strong'`: an event that keeps coming back is taken. Each helpful request is taken in
its region infinitely often wherever, infinitely often, it is allowed there; the regions need not stay, and a helpful
request may move to the region of one of a higher level instead of reaching `to` or lowering the rank (`levels`, one per
helpful request; found when left out):

```ts
// A worker takes the job (fetch), loses it (stall), takes it again ...: it fails for good only when failed while active.
job.leadsTo('the job fails for good', {from: ({st}) => st.is('failed').not(), to: ({st}) => st.is('failed'), rank: () => 0,
  helpful: [{when: ({st}) => st.is('wait'), request: () => ({op: 0})}, {when: ({st}) => st.is('active'), request: () => ({op: 2})}],
  fairness: 'strong'})  // proven; under weak fairness no rank exists (the regions don't stay)
```

Use it where the code's guarantee is that an event that keeps being possible happens (a retry, a scheduler that keeps
coming back): weak fairness, the default, only covers an event possible from some point on without a break. Each
helpful request is shown allowed in its region; the Lean theorem is Live.lean's `sleads_sf_soundA`.

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
- The name `r` is a history's record.

## Lists a request carries, and trees

```ts
const Line = record({sku: nat, amount: nat, taxable: bool})
const invoices = rule('invoices').params({budget: nat, cap: nat})
  .carriesList('Lines', Line, {
    total: {from: 0, step: (acc, l) => acc.plus(l.amount)},
    taxed: {from: 0, step: (acc, l) => acc.plus(when(l.taxable, l.amount, 0))},
  }, {'the taxable part is within the total': ({taxed, total}) => taxed.atMost(total)})
  .state({spent: 0})
  .flags(({Lines, cap, budget, spent}) => ({ok: Lines.every(l => l.amount.atMost(cap)).and(spent.plus(Lines.fold.total).atMost(budget))}))
  .step(({Lines, spent, ok}) => ({spent: when(ok, spent.plus(Lines.fold.total), spent)}))
invoices.encodeInput({Lines: [{sku: 1, amount: 30, taxable: true}]})
// a decision assumes the folds' equations and lemmas at the list's end (and wherever it reads the list)
proveDecision(invoices.decide('the taxable part is within the total', () => [], ({Lines}) => Lines.fold.taxed.atMost(Lines.fold.total)))

const rollup = fold('spend roll-up').params({cap: nat}).inputs({spend: nat})
  .leaf(({spend, cap}) => ({total: min(spend, cap), teams: 1}))
  .node(({spend, cap}, l, r) => ({total: l.total.plus(r.total).plus(min(spend, cap)), teams: l.teams.plus(r.teams).plus(1)}))
proveFold(rollup, [rollup.law('at most the cap per team', ({total, teams, cap}) => total.atMost(teams.mul(cap)))])
rollup.run({node: {spend: 50}, left: {leaf: {spend: 5}}, right: {leaf: {spend: 9}}}, {cap: 40}) // {total: 54, teams: 3}

// Any number of children: folded into `kids` first, with lemmas about every prefix of them.
const org = fold('org chart').params({cap: nat}).inputs({pay: nat})
  .leaf(({pay, cap}) => ({cost: min(pay, cap), heads: 1}))
  .children({cost: 0, heads: 0}, (acc, kid) => ({cost: acc.cost.plus(kid.cost), heads: acc.heads.plus(kid.heads)}),
    {'at most the cap per head': ({cost, heads}, {cap}) => cost.atMost(heads.mul(cap))})
  .node(({pay, cap}, kids) => ({cost: kids.cost.plus(min(pay, cap)), heads: kids.heads.plus(1)}))
org.run({node: {pay: 90}, children: [{leaf: {pay: 30}}, {node: {pay: 5}, children: []}]}, {cap: 50})

// A tree in the state: a table of nodes that only grows, each made from nodes already there, its folds kept with it.
const tree = rule('search tree').inputs({key: nat, l: nat, r: nat})
  .nodes('Tree', record({key: nat}), ['left', 'right'], {
    lo: {empty: 0, node: (x, k) => when(k.left.empty, x.key, k.left.fold.lo)},
    hi: {empty: 0, node: (x, k) => when(k.right.empty, x.key, k.right.fold.hi)},
  })
  .flags(({key, l, r, Tree}) => ({join: Tree.node(l).empty.or(Tree.node(l).fold.hi.lt(key)).and(Tree.node(r).empty.or(key.lt(Tree.node(r).fold.lo)))}))
  .step(({key, l, r, join, Tree}) => Tree.make({key}, {left: l, right: r}, join))
```

- A carried list's folds start at a number (or a term over the params) and step from the running value, the item and
  the params (`step: (acc, l, {ceil}) => ...`); their equations are assumed of every request (the encoding computes
  them, the runtimes check them). Folds that read the params need them to encode a request: `encodeInput(values,
  params)`; `foldsOf(values, params)` gives the folds at the list's end without running the rule. A lemma about the folds at every prefix is proven by induction over the items when the rule is built; without
  it a law that needs it isn't proven.
- A fold's laws read its values and the params, not the inputs; `toLean` takes `{id, fold: f.fold, laws}` (with
  `.children`, `laws: [...f.lemmas, ...laws]`).
- A table of nodes (`.nodes(name, kind, children, folds)`): node 0 is the empty tree, `T.make(value, kids, when)` makes
  node `T_size + 1` when every child is 0 or already there; `T.node(n)` gives `value`, `kids`, `fold`, `empty`. State a
  law about every subtree as a law about every node (`forall(n => n.atLeast(1).and(n.atMost(T_size)).implies(...))`). A
  fold may read a table declared before (`(x, kids, {Cell}) => Cell.node(x.first).fold.total...`): guard the make so
  the node it reads is already there. Lists of lists are two tables: cells, and rows naming their first cell.
- Not here: claims about a structure that need a lemma nobody stated (that every key is reachable from the root).

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

That some run never ends is a claim of its own: `proveNeverEnds(loop, {from?, ms?})` finds a run that goes on forever (a
closed set of states and the turn taken from each, a start and a stem into it), checked by the kernel and by Lean
(toLean's `{id, neverEnds: v.loop, recur: v.recur}`). A loop can't be proven both ways.

```ts
const pages = loop('pages').params({total: nat}).inputs({page: nat}).state({cur: 0})
  .while(({cur, total}) => cur.lt(total)).body(({cur, page, total}) => ({cur: cur.plus(min(page, total.minus(cur)))}))
proveNeverEnds(pages) // proven: an empty page, again and again
```

## Rules over the rationals

Fees in fractions, tokens that refill by a fraction, a ledger in decimals: `ratRule` (`gdp-wired/rationals`) takes
rationals as they are. 0.1 is 1/10 and a third is 1/3, every run is exact (bigint fractions), and the laws are proven
by linear arithmetic over ℚ, decidable, so a law is proven or refuted by a run from the start (or, where it isn't
inductive, unproven with the step that breaks it, as `proveRule`'s).

```ts
const limiter = ratRule('limiter').params({cap: nonneg}).inputs({cost: nonneg}).state({tokens: ({cap}) => cap})
  .assume(({cost, tokens, cap}) => cost.atMost(rmin(cap, tokens.plus('0.4'))))
  .step(({tokens, cap, cost}) => ({tokens: rmin(cap, tokens.plus('0.4')).minus(cost)}))
proveRatRule(limiter, [limiter.law('within the cap', ({tokens, cap}) => tokens.atLeast(0).and(tokens.atMost(cap)))])
```

A rule is all rationals or all naturals. A natural is a rational that is integral, and over ℚ `x < y` doesn't give
`x + 1 ≤ y`, `s ∸ c + c` isn't `s`, and nothing lies strictly between 0 and 1 only over ℕ: keep counts in `rule`.
Terms are linear: `times` and `over` take a constant, and a product of two unknowns is refused (`w.times(h)`).

## Statecharts

A workflow with many states reads better as a table than as a chain of `when`s. `chart` compiles one to a rule:

```ts
import {chart, nat} from 'gdp-wired'

const order = chart('order')
  .params({tries: nat})
  .context({retries: 0})                                   // extended state
  .states({
    new: {},
    active: {states: {paid: {}, shipped: {}}, history: true}, // re-entered where it was left
    held: {},
    refunded: {final: true},
    delivered: {final: true},
  })
  .on('pay', {from: 'new', to: 'active'})
  .on('fail', {from: 'new', to: 'new', when: ({retries, tries}) => retries.lt(tries), set: ({retries}) => ({retries: retries.plus(1)})})
  .on('hold', {from: 'active', to: 'held'})
  .on('resume', {from: 'held', to: 'active'})
  .on('ship', {from: 'active.paid', to: 'active.shipped'})
  .on('refund', {from: 'active.paid', to: 'refunded'})
  .on('deliver', {from: 'active.shipped', to: 'delivered'})
order.check({params: {tries: 2}}) // {ok, reached: {state: {run} | 'unreachable' | 'unknown'}, stuck: [...], ambiguous: [...]}
order.prove([order.law('retries within the limit', ({retries, tries}) => retries.atMost(tries))],
  [order.stepLaw('a shipped order is never refunded', (_, after) => after.in('refunded').not(), b => b.in('active.shipped'))])
```

- Per region and event, the enabled transition with the most specific source is taken (an inner state over its
  parent), then the first declared; `check().ambiguous` names two as specific as each other that one request enables.
- `.regions({payment: {...}, shipping: {...}})` for parallel regions: paths start with the region (`'payment.paid'`),
  every region reacts to the same event, and a guard reads another region with `env.in('payment.paid')`.
- A transition into a compound enters its initial child (the first, or `initial`), or with `history: true` the state it
  was last in, however deep (`env.last('active')` in a law); with `fresh: true` it enters the initial states all the way
  down, history or not. `prove` and `check` add `chartLaws()` (each history is one of its own states) to the laws.
- `check().reached` gives each state the shortest run that reaches it (a breadth-first walk over every event and small
  payloads), or `'unreachable'` where the prover proves no run gets there; `stuck` lists states with no way out that
  aren't `final`.
- A transition without `to` is internal: it stays where it is (nothing is exited or entered) and runs `set`; `from` may
  name a compound or several states (`{from: 'live', set: ({holds}) => ({holds: holds.plus(1)})}`).
- `.outputs({command: oneOf('denied', 'granted').from('denied')})`: what each step decides, read after it. An output
  starts every step at its default and a taken transition may `set` it, so a step where nothing fires reads `denied`,
  not the last grant (a default is a number, a choice or a yes/no). Context keeps its value instead.
- `.states(tree, {field: 'phase'})` names the state variable, and `.events('activate', 'retain', ...)` fixes the events'
  order and encoding: an existing bridge, its laws and its variants keep their names (`examples/charts.ts`'s binding).
- Entry and exit actions and side effects aren't modeled: the chart computes the next state and its context, and the
  code around it acts on the result. `chart.rule` is the plain rule, for `compiled()`, `compare` and `toLean`.
- Not yet: parallel regions inside a state (regions run at the top, for the chart's whole life), eventless and delayed
  transitions. Guard on the parent instead (`env.in('active')`), and send time in as an event.

### XState machines

An XState v5 machine you already ship becomes a chart with `fromXState`; give each guard and action it names again in
gdp-wired's terms (an action as the context it writes, `null` for one that writes none), then check the chart against
XState's own actor:

```ts
import {createActor} from 'xstate'
import {conforms, fromXState} from 'gdp-wired/xstate'

const c = fromXState(machine, {                 // machine: setup({guards, actions}).createMachine({...}), or its config
  guards: {canRetry: ({retries}) => retries.lt(2), unshipped: env => env.in('active.paid')},
  actions: {count: ({retries}) => ({retries: retries.plus(1)}), notify: null},
})
conforms(c, machine, createActor, {runs: 300, depth: 16}) // {checked} or {checked, failure: 'after PAY, SHIP, REFUND: ...'}
c.check(); c.prove([c.law('retries within 2', ({retries}) => retries.atMost(2))])
```

- Read: nesting, a parallel root (its children the regions), `initial`, final states, transitions as a target, an
  object or a list (`#id.path`, `.child`, a sibling), targetless transitions (internal), named guards and actions with
  their `params`, several actions in a row (each reads what the one before wrote), history nodes (a transition through
  one restores; one straight to the state enters it fresh, as XState does), root transitions (not from a final state).
  An XState v4 machine too: its `cond` is the guard (a name, or `{type, ...params}`, the params its other keys).
- Also read: an `invoke`'s done and error and an `after` timer firing, as events from outside taken only in the state
  that invoked or set them (each once a visit, one timer at a time); `always` transitions and entry and exit actions
  that write the context, folded into each transition as XState's macrostep.
- Refused when built, with the reason: a parallel state below the root, `onDone`, wildcard events, several targets,
  inline guards and actions (name them in `setup`), two timers in one state, eventless transitions or context-writing
  entry and exit actions in a parallel machine or beside a history node, eventless transitions that may run without end,
  two regions writing the context on one event, a shallow history over nested states, context that isn't
  numbers and booleans unless its kinds are given (`context: {status: oneOf('a', 'b').from('a')}`). So is any key it
  doesn't read, by name, rather than dropped (v4's `in`, `strict`, `activities`, `onEntry`; an event XState raises itself;
  `cond` in a v5 machine and `guard` in a v4 one, which that XState ignores, taking the transition unguarded).
- `conforms` is what ties the two: a guard or an action given wrongly shows up as the run where XState and the chart part.
  Payloads come from `payload: (event, rand) => ({amount: rand(10)})`, with `inputs: {amount: nat}` in `fromXState`.

## Sets, lists, functions, composition

- `.carries('Candidate')`: a set the request brings; `everyKey`, `has`, `subsetOf`, `disjointFrom`, `sameAs`;
  `someKey(k => ..., witness?)` (`examples/sets.ts`, `examples/quantifiers.ts`).
- `exists(kind?, k => ..., witness?)`: "there exists" in a law ("the balance is a multiple of 5":
  `exists(int, j => balance.eq(j.times(5)))`), proven through a witness the prover finds (a term of the state, or a
  ghost carried along the run), or the one given (a term, or `{start, step: (k, env) => ...}`). Write it where it reads
  as "there exists" (not under `not`, not before `implies`). In `.assume(...)` it is a value each request brings, found
  by `encodeInput` (`examples/exists.ts`).
- `everyKey((i, j) => i.lt(j).and(j.lt(n)).implies(New.at(i).lt(New.at(j))))`: a condition at every two keys (or
  three), in a step: each key read on its own (a map's key, or compared with a term that reads no key), the keys
  compared with each other only plainly (`i.lt(j)`, `i.atMost(j)`, `i.eq(j)`). The runtimes decide it on every pair of
  a few keys per cell, so it costs the square of the cells; nest no `everyKey` inside another (`examples/pairs.ts`).
- `.lists('Scope')`: a list with `Scope_len` (`examples/lists.ts`).
- `.carriesSeq('Path')`, `.carriesSeqs('Paths')`: sequences a request carries as positions and a length (a path's
  segments as interned names), `A.prefixOf(B)`, `startsWith`, `equals`, `extends(B, k)`, `has(x)`, a table's
  `Paths.row(r)`; a prefix is a condition about every position, so a law about prefixes needs no lemma. Compare rows at a
  witness (an input naming the row), not inside a condition about every row. A permutation (sorting, merging) is
  bookkeeping the request carries, where each item went, checked with `everyBelow(n, k => ...)` (`examples/scopes.ts`).
- `.fns({perMinute: divBy(60)})` or `fn(arity, js, {facts, lean})`: the kernel knows a function only by its facts
  (`examples/functions.ts`).
- `recur('delay', {zero: 1, next: (x, d) => min(d.times(2), 64)}, {'at most 64': (x, d) => d.atMost(64)})`: a function
  defined by a recurrence, its lemmas proven by induction when it is made, then facts any rule that reads it uses; with
  `args: ['cap']` it takes further arguments (up to four), with `fns: {rem: modBy(7)}` its step and its start read other
  functions, and a fourth
  argument states laws between two points (`(x, fx, y, fy) => fx.atMost(fy)`, for every x <= y)
  (`examples/lemmas.ts`, [Lean handoff](lean-handoff.md)).
- `discover(r, laws, stepLaws)` (`gdp-wired/discover`): where a law needs a lemma about a `recur` function or a
  carried list's folds that nobody stated, it finds one among bounds, linear relations, closed forms of degree 2 at most
  and laws between two points, proves it by the same induction and keeps only what the laws need: `out.verdict` is of
  `out.rule`, the rule made again with them, and `out.found` is source to paste into `recur` or `carriesList`
  (`{delay: {lemmas: ["'f(x) <= 64': (_, f) => f.atMost(64)"]}}`). `discoverFold(fold, laws)` does the same for a tree
  fold; `found` is laws to pass as `proveFold`'s `lemmas`, and lemmas for `.children` (`examples/discover.ts`).
- `gdp-wired/compose`: `product`, `interleave`, `refinement(impl, spec, {relation, witness, stutter})`, `steps`,
  `ghost(m, {name: ever(...) | count(...) | total(...)})` for orderings at any distance (`examples/composition.ts`).
