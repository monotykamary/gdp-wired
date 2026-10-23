<picture>
  <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/monotykamary/gdp-wired/main/static/banner-dark.svg">
  <img src="https://raw.githubusercontent.com/monotykamary/gdp-wired/main/static/banner-light.svg" alt="gdp-wired: an automatic prover for stateful rules" width="100%">
</picture>

# gdp-wired

An automatic prover for stateful rules: budgets, caps, rate limits, workflows, access policies. You write the rule and
the laws it must keep. gdp-wired proves them with no proof to write, shows a real run that breaks a law when it's false
(found by searching on the GPU), has every proof checked again by Lean, and ships the rule as JavaScript.

```sh
npm install gdp-wired   # or bun add gdp-wired; plain JavaScript with types, Node 20+, Bun or a browser
```

New to formal verification? [The guide](https://gdpwired.dev/guide) takes a rule from ordinary TypeScript to a proof in
seven steps, with recipes for limits, workflows, permissions and orders with line items.

```ts
import {min, nat, proveRule, rule, when} from 'gdp-wired'

// A request of cost c is admitted while spend s is under budget b; each request is capped at m.
const budget = rule('budget')
  .params({b: nat, m: nat})
  .inputs({c: nat})
  .state({s: 0})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))

proveRule(budget, [bounded]) // {proven: true, checked: true}
```

Names are typed: `({s, bb}) => …` or a law that reads the request `c` is a TypeScript error, not a runtime surprise.
Forget the cap (`s.plus(c)`) and the kernel refuses the proof; a search from the start turns it into a real run:
`{params: {b: 1, m: 0}, trace: [{c: 2}]}`. `bun examples/budget.ts` runs all of it, including the generated JavaScript,
and `examples/domains/` holds 187 rules from 21 domains (finance, access control, public services, operations,
protocols, commerce, supply chains, games, education, healthcare, energy, networking, AI agents, cloud, ad tech,
governance, insurance, bookings, safety and IoT, mobility, media), each checked three ways: the kernel proves every law
and refutes every broken variant, random runs of both runtimes agree, and Lean checks the trees.

## Where it fits

<img src="https://raw.githubusercontent.com/monotykamary/gdp-wired/main/static/venn.svg" alt="What Lean, Bend and gdp-wired each cover, and where they overlap" width="640" />

Lean proves anything you write the proof for. Bend runs programs that carry their proofs. gdp-wired proves one kind of
claim, laws about stateful rules, with no proof to write, and hands every proof to Lean as a theorem. Where a proof needs
more than it decides, the proof is Lean's: a function you define and prove there, which the rule then uses.
[`docs/comparison.md`](docs/comparison.md) goes through each region, compares the three side by side, and measures them
on the same rules.

## What it proves

All of these are proven automatically, and each proof is also a Lean theorem:

- **Invariants**: a law that holds after every sequence of requests ("spend stays within the budget").
- **Maps, sets and lists of names**: laws at every key ("no day passes its cap"), sets a request carries, conditions
  about every key or every two keys ("a batch is taken only when its values increase"), lists kept in order
  (`examples/sets.ts`, `examples/lists.ts`, `examples/pairs.ts`), and two groups of items with a set each, decided at
  every pair at once (`examples/groups.ts`).
- **Step laws**: what one step does ("a balance only goes down", "a grant adds one"), and laws over up to 64 steps in
  a row (`examples/steps.ts`).
- **Histories**: sums and queries over a log of requests, like a sliding-window rate limit.
- **Statecharts**: `chart(name).states({...}).on(event, {from, to, when, set})`, with states nested to any depth,
  parallel regions (at the top of the chart), a compound's history (deep), guards and extended state, compiled to a rule;
  `check()` shows every state reached by a run (or proves it unreachable), no state stuck and no event ambiguous, and its
  laws prove like any rule's (`examples/charts.ts`). Not yet: parallel regions inside a state, entry and exit actions,
  eventless and delayed transitions.
- **XState machines** (`gdp-wired/xstate`): `fromXState(machine, {guards, actions})` builds the chart an XState v5
  machine runs as, with each guard and action it names given again in gdp-wired's terms, and `conforms(chart, machine,
  createActor)` drives XState's own actor and the compiled rule with the same random events, comparing every state and
  context; what a chart can't run the same way is refused when built, with the reason (`examples/xstate.ts`).
- **Rules read from the code** (`gdp-wired/extract`): `extract(code, {entry})` reads a reducer, `useReducer`'s, functions
  over one record, or a class whose methods write its fields, and returns the rule that steps the same way, as a builder
  value and as source to keep (`toSource`); `extractXState` reads an XState machine's guards and actions, named or
  inline, for `fromXState`. The extractor is untrusted: each rule is run beside the code it was read from (requests
  from the start, steps from drawn states and from the prover's counterexamples, every state, cell, result and refusal
  compared, the code's branches counted), and a difference refuses it. Its subset (integers, booleans, string-literal
  unions, records, Map and Record keyed state, branches and early returns, throws as refusals, `Date.now()` as an
  input) and what it refuses, each with the place and the reason, are in `core/extract.ts`.
- **What nobody stated, looked for when the prover alone stops**: where `proveRule` or `proveSteps` doesn't prove the laws
  and no run breaks them, it looks for lemmas about the rule's recurrences and lists (`discover`), lemmas about the
  functions it knows by their facts (`cycleLemmas`, each proven by a cyclic proof) and then invariants (`inferLaws`),
  within 10 s (`{search: {ms}}`; `{search: false}`, the prover alone); the verdict's `found` holds what
  proved them, as laws and lemmas with the source to paste.
- **Invariants nobody wrote** (`gdp-wired/infer`): `inferLaws(rule, laws)` proves a law that holds but isn't inductive
  alone, with the laws it finds (bounds, sums and differences over the state, the same where a flag or a choice holds
  one value, remainders of a value or of a sum or difference of two, x mod 2 = 0 for a counter stepping by 2, and laws
  about every key of a map), each proven by the kernel with yours and handed back as the
  `r.law(...)` call that states it; a false law comes back with the run that breaks it (`examples/infer.ts`).
- **There exists**: laws that say some value is a witness, `exists(k => x.eq(k.times(2)))` ("x is even"), over
  naturals, integers, yes/nos or a map's keys, each proven through a witness the prover finds from the kernel's
  counterexamples (a term of the state, or a ghost the run carries: the witness before, moved by the request's values)
  or the one given; an existential in the assumption is a value each request brings, and `inferLaws` finds parities
  and multiples this way. Lean states each as `∃ w, ...`, proven by ⟨witness, proof⟩ (`examples/exists.ts`).
- **Orderings at any distance**: "a refund never follows a release", through ghost state that watches the rule.
- **Liveness**: "every ticket issued is served", in every run that keeps sending the requests that help, including under
  weak fairness (`examples/liveness.ts`).
- **Refinement**: an implementation behaves like a simpler spec, step for step (`examples/composition.ts`).
- **Functions**: division, remainder, and your own functions, known by their facts; a function defined in Lean brings
  facts proven there (`examples/functions.ts`).
- **Lemmas you state**: a function defined by a recurrence (`recur`), of one argument or several, reading other
  functions, and lemmas about it proven by induction, at one point or between two, which every rule that reads it may
  then use: a backoff delay is at most 64 at every attempt and never shrinks (`examples/lemmas.ts`).
- **Lemmas nobody stated** (`gdp-wired/discover`): `discover(rule, laws, stepLaws)` finds what a recurrence or the folds
  of a list a request carries need, from their values (bounds, linear relations, a closed form of degree 2 at most, a
  law between two points), proves it by the same induction and keeps only what the laws need; `discoverFold(fold,
  laws)` does the same for a fold over a tree. What it finds comes back as source to paste (`examples/discover.ts`).
- **Cycles nobody shaped** (`gdp-wired/cycles`): `findCycles(facts, claims)` proves claims about functions defined by
  their equations with nothing a proof needs stated: the rank each induction drops (from the runs, by linear
  programming, in order: McCarthy's 91 by 101 − n, Ackermann's by (m, n)), where each cycle returns (the calls its
  goal reads), and the lemma a stuck one needs (g(x, 0) = 2x through g(x, a) = a + 2x; a bound on another function);
  `proveLoop` with no rank finds it (two phases' (x, y)) and the invariants it needs; the kernel checks the cyclic
  proof (`examples/cycles.ts`).
- **Runs that never end**: `proveNeverEnds(loop)` proves some run of a loop goes on forever (pagination that accepts an
  empty page, a retry with no cap): a closed recurrent set with the turn from each of its states given, a start and a
  stem into it, checked by the kernel and again in Lean (`NonTerm.lean`'s `never_ends_of`; `examples/nonterm.ts`).
- **Recursive datatypes as values** (`gdp-wired/data`): lists, trees, rose trees and their forests, declared by their
  constructors; functions over them by structural recursion, or by any recursion whose termination is proven first (a
  merge of two lists, a quicksort: the measure found, (size xs, size ys) or a sum of sizes, and each call's decrease
  proven by the kernel before the function's equation is used; one that doesn't terminate is refused with the reason);
  `proveData` finds the induction (structural, mutual, or the function's own call graph ranked by its measure) and the
  lemmas, each proof checked in Lean against the `inductive` and the functions as declared (`examples/data.ts`).
- **Records and variants**: inputs, state, results, map cells and list items made of named fields, or one of several
  cases each with fields of its own (a payment by card or in cash, a seat free, held or sold), every case covered
  (`examples/datatypes.ts`).
- **Lists a request carries, and trees**: an invoice's lines, with folds over them (the total, the taxable part) and
  lemmas about the folds proven by induction over the lines (`examples/invoices.ts`); a fold over a tree as a value (a
  spend roll-up, sign-offs over a document's sections, an org chart where a manager has any number of reports), its laws
  proven by induction over the tree (`examples/folds.ts`); a search tree, and a sheet of rows of cells, kept in a rule's
  state as tables of nodes (`examples/trees.ts`).
- **Pure functions and two-run laws**: laws about what a function returns, and laws comparing two calls, like "the
  secret never changes the answer". `examples/jev-fabric/` ports a Bend project's policy core and proves all 59 laws its
  Bend proofs state.

When a law is false, the GPU search finds a real run that breaks it. When a law needs an invariant nobody wrote,
`inferLaws` finds one on the CPU (and the GPU synthesizer, at scale, in `research/synth/`) and the kernel proves it.

**What it leaves to Lean or Bend.** Two things, and neither is a gap the next feature closes: proofs the prover would
have to invent (induction over a recursive structure whose proof needs a lemma nobody stated and `discover` doesn't find, and arithmetic with
products of unknowns beyond what products of facts and sums of squares give; integer arithmetic with induction or
with products is undecidable; a lemma you state about a recurrence is proven, and `proveData` finds the induction and lemmas for a recursive datatype as a value, up to six symbols a lemma, for
functions structural or whose termination it proves, its values naturals, integers (`integer`, Lean's `Int`, beside
`natural`) and datatypes), and shipping an arbitrary algorithm as its proved source (gdp-wired ships the rule as JavaScript; Bend
compiles the proved source itself). The full list of what is and isn't in scope is in
[`docs/comparison.md`](docs/comparison.md#gdp-wireds-scope-in-detail).

## Why you can trust a proof

A small kernel checks every proof; the prover that finds them is untrusted, and the kernel's twin in Lean is proven
sound.

| Part | Trusted? | What it does |
| --- | --- | --- |
| `kernel/kernel.ts`, `core/check.ts` | **Yes** | Turns a rule and its laws into goals, and checks a proof tree for each: case splits on linear facts, then a linear refutation at each leaf |
| `kernel/cyclic.ts` | **Yes** | Cyclic proofs: builds each node's goals (its own, and for each node it uses, that node's hypotheses and that the rank drops) and checks each tree with kernel.ts's check. Its twin is `lean-kernel/Cyclic.lean` (`cyclic_sound`), and `lean-kernel/Bridge.lean` carries a cyclic proof of a machine's law, a recurrence's lemmas or a fold's law back to the rule itself |
| `kernel/prove.ts`, `kernel/cdcl.ts` | No | Find the proof trees: case splits, and CDCL over a goal's atoms whose refutation is unfolded into a tree. If they're wrong, the kernel rejects the tree |
| `lean-kernel/` | Optional | The kernel's twin in Lean 4.34.0, every rule proven sound there with the standard axioms only. The exporter sends the kernel's real trees; tampered ones compute to false |
| `research/search/`, `research/synth/`, `research/hw/` | No | The GPU searches for breaking runs, and invariant and rank synthesis. Every hit is replayed or proven before it counts |
| `core/dsl.ts`, `core/compose.ts`, the runtimes | No | The builders and combinators compile to the kernel's plain values; the runtimes are held to a reference evaluator |

The untrusted parts are held to the trusted ones by the test suite:

- **Builders**: every law, step law, flag, update and decision in the examples is run again on concrete runs, its
  callback's answer computed by the builders' own arithmetic (each term carries its value beside its expression) against
  what the interpreter makes of the expression that was proven (`rule.crossCheck`, `crossCheckDecision`). A builder that
  writes a different expression than it means is caught, even where the kernel would still prove the law it wrote.
- **Encodings**: `fun.compare(reference)` and `rule.compare({init, step})` run the rule against the code it describes,
  on drawn and edge inputs (strings, decimals and choices as themselves), field by field.
- **Types**: strict TypeScript and a lint that denies warnings; every switch over operations is exhaustive, so a new
  operation fails to compile wherever it's missing.
- **Conformance**: random terms through every evaluator (interpreter, generated JavaScript, the kernel, the GPU search,
  Lean's own evaluator) against the reference one.
- **Examples**: every law proven and re-checked in Lean, every rule run at random, every broken variant broken by a real
  run.
- **Tampering and mutation**: broken proofs must be rejected; every one-operator change to the kernel is run against the
  tests, and the few that survive are equivalent (`kernel/MUTANTS.md`).
- **Fuzz**: the kernel never accepts a refutation of something that has a model.

## With gdp-ts

[gdp-ts](https://github.com/rauchg/gdp-ts) makes every call site present a proof that a check ran on exactly these
values, and trusts the module that performs the check. `gdp-wired/gdp` proves that check: the trusted module hands its
private prover to a `guard` (a function's condition) or a `gate` (a rule's flag), which proves the laws when the module
loads, refuses to load if one fails, and mints a proof only where the proven condition holds. gdp-ts then holds every
call site to it: the policy is proven, every caller is held to it, and Lean checks the proof again.

```ts
// proofs/can-set-protection.ts (trusted: the only module that can mint this proof)
import {defineProof, type Named, type Proof} from '@gdp-ts/core'
import {fun, no, oneOf} from 'gdp-wired'
import {guard} from 'gdp-wired/gdp'

const canSet = fun('can set password protection')
  .inputs({role: oneOf('owner', 'member', 'viewer', 'none'), plan: oneOf('free', 'pro', 'enterprise')})
  .returns(({role, plan}) => ({allow: role.is('owner').or(role.is('member')).and(plan.is('free').not())}))
const laws = [canSet.law('the free plan never has protection', ({plan}, out) => [plan.is('free'), out.allow], () => no)]

const CanSetProtection = defineProof('CanSetProtection') // not exported
export interface CanSetProtection<U, P> extends Proof<'CanSetProtection', [U, P]> {}
const mint = guard(CanSetProtection, canSet, 'allow', {laws}) // proven here, or the module doesn't load

export async function canSetProtection<U, P>(user: Named<U, UserId>, project: Named<P, ProjectId>): Promise<CanSetProtection<U, P> | null> {
  return mint({role: await db.role(user.value, project.value), plan: await db.plan(project.value)}, user, project)
}
```

A `gate` does the same for a rule with state: each request takes the rule's step, and a proof is minted when the step
takes the flag (a one-time token redeemed, a sign-in while the account is unlocked, an email within the hourly cap).
Requests outside what was proven (a failed `assume`, a history read out of order) mint nothing and leave the state as it
was. `examples/gdp.ts` runs gdp-ts's own example this way; `@gdp-ts/core` is an optional peer dependency.

## Writing laws

The builders (`core/dsl.ts`) hand out typed values for every name you declare; everything compiles to the plain machine
the kernel checks, so nothing in them is trusted.

```ts
import {bool, count, forall, fun, maybe, min, nat, no, oneOf, proveSteps, record, recur, relation, rule, variant, when, yes} from 'gdp-wired'

// Maps and flags: a grant is decided once per step; each map is written once; a map law holds at every key.
const caps = rule('caps')
  .params({d: nat})
  .inputs({acct: nat, day: nat, ok: bool})
  .maps({Acct: 0, Day: 0})
  .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
  .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))

// Step laws: about one step, for every request the rule allows; `after` reads the state and maps after it.
const onlyUp = caps.stepLaw('no count goes down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))
const once = caps.stepLaw('a grant adds one to its day', ({day, Day}, after) => after.Day.at(day).eq(Day.at(day).plus(1)), ({granted}) => granted)
// k-step laws: about k steps in a row; `requests` holds each step's request, `when` narrows the j-th step's.
const twice = caps.stepsLaw('two grants on one day add two', 2, ({day, Day}, after, [, next]) => next!.day.eq(day).implies(after.Day.at(day).eq(Day.at(day).plus(2))), ({granted}) => granted)
proveSteps(caps, [dayCap], [onlyUp, once, twice]) // {proven: true, checked: true}

// Histories: a log of requests, a sum over it (state), a query over it at the request's time (an input the runtime
// computes), and a relation between them proven one record at a time.
const window = rule('window limit')
  .params({w: nat, c: nat, now: nat})
  .inputs({forced: bool, t: nat})
  .log('forced', 't')
  .sums({ours: (r, {now, w}) => count(r.forced.not().and(r.t.atMost(now), now.lt(r.t.plus(w))))})
  .queries({seen: (r, {t, w}) => count(t.lt(r.t.plus(w)))})
  .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
  .keep(({forced, admitted}) => forced.or(admitted))
  .relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
  .prune('t', ({w}) => w) // requests in time order: records older than the window are dropped

// Decisions over facts: optional facts and choices, every case covered.
const trial = rule('trial').inputs({plan: oneOf('free', 'pro'), spent: maybe(nat), allowance: maybe(nat)})
const failsClosed = trial.decide('a missing fact means no trial', ({spent}) => spent.isNone,
  ({plan, spent, allowance}) => plan.match({free: () => spent.match({none: () => yes, some: s => allowance.match({none: () => yes, some: a => s.atLeast(a)})}), pro: () => yes}))

// Records and variants: a payment is by card or in cash, each with fields of its own, read only in `match`.
const Pay = variant({card: {amount: nat, verified: bool}, cash: {amount: nat}})
const approve = fun('approve').inputs({pay: Pay, who: record({limit: nat, blocked: bool})})
  .returns(({pay, who}) => ({ok: who.blocked.not().and(pay.match({card: c => c.verified.and(c.amount.atMost(who.limit)), cash: c => c.amount.atMost(200)}))}))
const unverified = approve.law('an unverified card is never approved', ({pay}, out) => [pay.match({card: c => c.verified.not(), cash: () => no}), out.ok], () => no)

// A lemma you state, proven by induction: the backoff delay is defined by its recurrence, and its lemmas are facts
// every rule that reads it may use (its two equations alone don't bound it at an unknown attempt).
const delay = recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {'at least 1': (_, d) => d.atLeast(1), 'at most 64': (_, d) => d.atMost(64)})
const retry = rule('retry').inputs({failed: bool, now: nat}).state({tries: 0, next: 0, last: 0}).fns({delay})
  .assume(({now, last}) => now.atLeast(last))
  .step(({failed, now, tries, next, delay}) => ({tries: when(failed, tries.plus(1), 0), next: when(failed.and(now.atLeast(next)), now.plus(delay(tries)), next), last: now}))
const soon = retry.law('the next try is at most 64 after the last request', ({next, last}) => next.atMost(last.plus(64)))
```


- **Kinds**: `nat`, `upTo(k)`, `bool`, `oneOf(...)`, `maybe(kind)`, `int`, `decimal(places)`, `str({like, maxLength})`,
  `record({...})`, `variant({...})`; their assumptions (a bit is 0 or 1, a choice is in range) go to the kernel by
  themselves, and `encodeInput`/`encodeParams` turn runtime values into the numbers the machine reads.
- **Records and variants**: `record({limit: nat, blocked: bool})` hands out an object of its fields' values;
  `variant({card: {...}, cash: {...}})` a value with `is(case)` and `match({card: c => ..., cash: c => ...})`, the only
  place a case's fields are read. `Pay.make({tag: 'card', amount, verified})` builds a case to write or to pass to
  `when`, and `same(a, b)` compares two values of one kind part by part; `optional(c, value)` is a value present where c
  holds (a result that may be missing). At runtime a record is an object of its fields and a variant `{tag: 'card',
  ...fields}` (or the key given, `variant({...}, {tag: 'kind'})`); a field or case the kind doesn't declare is refused.
  What a kind keeps true of the values a step writes (a case in range, a flag 0 or 1) is a law of its own, `r.kindLaws()`,
  which proveRule, proveSteps and proveLeadsTo prove beside the laws they are given. Both are their fields'
  variables underneath (`pay.card.amount`, and the case's index as `pay`), so the kernel, both runtimes and the Lean
  twin see nothing new. Maps and lists of them: `.maps({Acct: record({...}).from({...})})` (`Acct.at(k)`,
  `Acct.set(k, value)`, `Acct.each(k => value)`) and `.items({Queue: Job})` (`push`, `pop`, `set`, `insertAt`,
  `removeAt`, `apply`, `has`, `within`, `increasing(by)`), one map per variable of the kind; `rule.decode` reads them back
  as objects and arrays.
- **Sequences a request carries** (`.carriesSeq('Path')`, and tables of them, `.carriesSeqs('Paths')`): a sequence of
  naturals as positions and a length, `Path.at(i)`, `Path.len`, a table's row `Paths.row(r)`; `A.prefixOf(B)`,
  `startsWith`, `equals`, `extends(B, k)`, `has(x)`, each a condition about every position below a length, so laws about
  prefixes of paths need no induction or lemma. The request gives an array of naturals (interned names), a table an
  array of them. `everyBelow(n, k => ...)` checks bookkeeping a request carries row by row (where each grant went). A
  condition about every row of a table can't compare the rows' sequences (that is two keys at once); compare a row at a
  named row, a witness, instead (`examples/scopes.ts`: pi-fabric's path scopes, covering, attenuation and normalization).
- **Lists a request carries** (`.carriesList('Lines', Line, folds, lemmas)`): the items one carried map per variable of
  the kind, the length `Lines.len`, each fold (`{total: {from: 0, step: (acc, line) => acc.plus(line.amount)}}`) a
  carried map of its running values whose equations every request is assumed to meet (the encoding computes them from the
  array, and a request that doesn't meet them isn't allowed), read as `Lines.fold.total`; `Lines.every`, `some`, `has`,
  `increasing(by)`, `at(i)`. A lemma about the folds (`({taxed, total}) => taxed.atMost(total)`) is proven by induction
  over the items when the rule is built, then assumed at every prefix; a decision (`decide`) assumes the equations and
  lemmas too, at the list's end and wherever it reads the list. A lemma reads the folds, the prefix's length and the
  params, not the items: a fact about every item is a fold's (a count of the items that meet it). A fold's start and
  step, and a lemma, may read the params (`{from: ({fee}) => fee, step: (acc, line, {ceil}) => acc.plus(min(line.amount, ceil))}`); a request is then
  encoded with them, `rule.encodeInput(values, params)` (`examples/invoices.ts`). `rule.foldsOf({Lines: [...]}, params)`
  gives each fold at the list's end, computed the same way, without running the rule (to compare a decision's folds
  with the code it describes).
- **Folds over trees** (`fold(name).params(...).inputs(...).leaf(env => ({...})).node((env, left, right) => ({...}))`,
  `proveFold`): a tree as a value (`{leaf: inputs}` or `{node: inputs, left, right}`), each leaf's values from its inputs
  and each node's from its own and its children's; a law about the values is proven by induction over the tree (the
  kernel's leaf and node goals, Lean's `fold_sound`), `f.run(tree, params)` evaluates the terms proven and `f.crossCheck`
  holds the builders to them. Nodes with any number of children: `.children(from, (acc, kid) => ..., lemmas)` folds a
  node's children into `kids`, then `.node((env, kids) => ...)`; it is the kernel's binary fold underneath (each child
  list a chain of glue nodes), so Lean's `fold_sound` checks it unchanged, and `f.run` takes `{node, children: [...]}`
  (`examples/folds.ts`).
- **Trees in a rule's state, and lists of lists** (`.nodes('Tree', record({key: nat}), ['left', 'right'], folds)`): a
  table of nodes that only grows, node 0 the empty tree, `Tree.make(value, {left, right}, when)` making node size + 1 from
  nodes already there; each fold (`{lo: {empty: 0, node: (x, kids) => when(kids.left.empty, x.key, kids.left.fold.lo)}}`)
  kept with its node when it is made, and may read a table declared before (a row's total over its cells). A law about
  a subtree is then a law about one node (`Tree.node(n).fold.lo`), proven like any law about every key; the table's own
  laws (children earlier, folds coherent, nothing past the end) are proven beside it (`examples/trees.ts`: a search tree,
  a sheet of rows of cells). Claims that need a lemma about the tree's shape nobody stated stay Lean's.
- **State of any kind**: `.state({open: bool.from(true), status: oneOf('new', 'done').from('new'), owner: str().from(''), note: maybe(nat).from(null)})`;
  a step writes each kind's own values, `when(c, a, b)` chooses between any two values of a kind, and `rule.decode(state)`
  reads them back as runtime values.
- **Integers and decimals**: `int` and `decimal(places)` inputs, `.ints({...})` and `.decimals(places, {...})` state;
  `plus`, `minus`, `negate`, `times(k)` (k may be negative), `min`, `max`, `abs`, `isNegative`, comparisons with numbers
  (a decimal's literals are scaled: `price.atMost(19.99)`), and `modBy(k)`, `divBy(k)` by Euclid's rule (−7 div 2 is
  −4, −7 mod 2 is 1, as SMT-LIB and Lean's `Int` read them). Each is two naturals underneath, so the kernel twin sees
  nothing new; the Lean export states each law about integers again over `Int` (`law0_int`, proven from the law over
  the naturals by `omega`), and `rule.decode(state)` reads them back as numbers. A natural's `minus` stays truncated:
  an integer is a kind of its own, chosen where a value may go below 0 (`examples/arith.ts`).
- **Strings**: `str({like: ['*.internal'], maxLength: 64})`. A string is its interned name, its length and a bit per
  declared pattern (Cedar's glob), all computed from the string itself when the input is encoded. `s.like(pattern)`,
  `s.eq('admin')` (which carries the literal's length and pattern bits, so laws reason from either), `s.isEmpty`,
  `s.length`; sets of strings are carried maps keyed by `s.id`.
- **Arithmetic** over the naturals: `plus`, `minus` (truncated), `times(k)`, `mul` (a product of two terms, a map's
  cell among them: `Used.at(k).atMost(per.mul(Seats.at(k)))`), `modBy(k)` and `divBy(k)` by a constant k ≥ 1 (the rule's
  functions mod$k and div$k, known to the kernel by x = k·(x div k) + x mod k and x mod k < k, Presburger arithmetic it
  already decides; Lean's `%` and `/`, both facts proven by `omega`; division by a term isn't offered: x = y·q + r is a
  product of two unknowns), `min`, `max`, `when(cond, a, b)`, `count(cond)`;
  conditions `lt`, `atMost`, `eq`, `and`, `or`, `not`, `implies`. Where a law with products isn't linear in its
  monomials, the prover multiplies facts together and adds squares, as Lean's `nlinarith` does: (x − y)² for each
  product x·y the law reads, its factors as the step leaves them, and for each monomial split in two halves
  (Cauchy–Schwarz's (ad − bc)²), times each factor past degree two (`research/frontier/nonlinear.ts`).
- **Sets and quantifiers**: `.carries(...)` for sets a request brings, `everyKey(k => ...)` (and `has`, `subsetOf`,
  `disjointFrom`, `sameAs`) anywhere in a step or inside a law, `everyKey((i, j) => ...)` in a step for every two keys
  (each read on its own, compared with the other plainly: `i.lt(j)`), `M.each(k => ...)` to write every key, and
  `someKey(k => ..., witness?)` for "some key where", proven through a witness the prover finds or the one given.
- **There exists** (`exists(kind?, f, witness?)`, core/exists.ts): "some value of the kind (nat, int, bool, upTo(k))
  where f holds", anywhere in a law where it reads so (under no `not`, not before `implies`), after its `forall` key if
  it has one. The kernel never sees it: the law it proves is f with a witness term in place (a term of the state, for
  each bound value), or f over ghosts the machine gains (a value at the start, and after each step one over the
  witness before, the request and the state before), chosen by the kernel's counterexamples among what f's own atoms
  solve for, 0, the state, the params, the request's values and shifts of the witness before, per case of the step; a
  witness given, `exists(k => ..., lo)` or `{start, step: (k, env) => ...}`, is the only one tried. The verdict's
  `witnesses` says how each reads. In the assumption (`exists(int, k => amount.eq(k.times(5)))`) or a precondition, it
  is an input or a param the runtimes find (`encodeInput`, `encodeParams`: exact where it is one natural or integer
  read linearly); a request no witness fits is refused. A run refutes a false one where no value can be a witness,
  decided the same way.
- **Functions** (`.fns({perMinute: divBy(60)})`, or `fn(arity, js, {facts, lean})` for your own): read like params that
  take arguments, `perMinute(t)`; the kernel knows each only by its facts (`.facts(...)`, and a library function's
  own), and the Lean export takes them as the hypothesis they are, proving them where the function has a Lean
  definition. A function defined and proven in Lean is how a rule reaches past what the kernel decides: `examples/functions.ts`.
- **Recurrences and their lemmas** (`recur(name, {args, fns, zero, next}, lemmas, between)`): f(0, a..) = zero and
  f(x + 1, a..) = next(x, f(x, a..), a..), the further arguments `args` (up to four) fixed along the recursion, each term
  the kernel's own or a read of a function in `fns` (`modBy(7)`, another recurrence), the start's too. Each lemma is a law about every x
  and f(x), proven when the function is made, all of them together by induction (the recurrence run as a machine, each
  lemma a law of it, so one lemma may lean on another, and on the facts of the functions it reads); each law `between`
  is about every x <= y and f(x), f(y) ("never shrinks"), proven by induction on y from x, with the lemmas. One that
  isn't proven throws `Unproven` with the induction step it breaks at. The two equations, the lemmas and the laws
  between are the function's facts. The runtimes compute f by the recurrence, continuing from the last value computed at
  the same further arguments (a rule that reads f at a growing count takes one step a request); the Lean export defines
  `Recur.<name>` by it (a function of several arguments through an injective pairing, proven so in Lean) and checks the
  kernel's own proof of every lemma and law between: the machine it was proven by, with its trees, and the run of it that
  reaches x and f(x), so a lemma with a product (squares: f(x) = x·x) needs no tactic of Lean's (`examples/lemmas.ts`).
- **Liveness** (`rule.leadsTo(name, {from, to, rank, helpful})`, `proveLeadsTo`): whenever `from` holds, `to` holds later in
  every run that takes each helpful request infinitely often; proven by a rank no step raises while waiting and each
  helpful request lowers in its region. `rank` may return several terms (compared in order) and `helpful` may be a list
  of `{when, request}`; a request names only the inputs it fixes (`examples/liveness.ts`: batches, a history with a
  query, a machine with sets).
- **Pure functions** (`fun(name).inputs(...).returns(env => ({...}))`): each field of the result a term or a condition;
  `f.law(name, given, then)` is a decision about the terms it returns and `f.run(values)` runs those terms compiled. A
  decision assumes the functions' facts where it reads them.
- **Two runs** (`r.relate(name, (a, b) => given, (a, b) => then)`, or `f.relate(...)` with both results): a decision
  about two requests under the same params, for noninterference ("requests that differ only in a secret are decided
  alike"); the second request's inputs show as `b.<input>` in a counterexample.
- **Loops** (`loop(...)`): state, `while`, `body`, a `rank` (or a tuple of ranks) that must drop each turn. A loop is a
  machine (its body taken while `while` holds) and its halting a liveness of it, so Lean checks it with the machine twin.
- **Lean** (`gdp-wired/lean`): `toLean([{id, machine, laws, stepLaws}, ...])` writes the proofs as a Lean file, and
  `leanProject(file)` a Lake project with the twin, so `lake build` checks them. Each law comes as the twin's theorem and
  as a plain statement over named variables, e.g. `theorem budget.law0 (h : SReach budget_machine ρ μ) : ρ «s» ≤
  (ρ «b» + ρ «m»)`, for a Lean development to cite.
- **Composition** (`gdp-wired/compose`): `product(a, b)`, `interleave(a, b)`, `refinement(impl, spec, {relation, witness, stutter})`,
  `steps(spec, k)` (k spec steps as one, each skippable) and `ghost(m, {name: ever(...) | count(...) | total(m, map, name)})`
  build plain machines from machines (each side's state named `a_x`, `b_x`). A refinement's laws are the relation, proven
  by induction, and its step law says the spec allows the request `witness` sends it at each of the implementation's:
  `examples/composition.ts` proves a meter that counts down refines one that counts up, and refuses two broken ones;
  a two-phase meter refines it with stuttering; an escrow never refunds after a release (at any distance); and the
  connection pool's in-use count is the total of every client's holdings.
- **Running it**: `rule.interpreter()` is persistent (searches branch from any state); `rule.compiled()` is what an app
  ships: maps and the log updated in place, so a step costs the same however long the history. Both refuse params and
  inputs that aren't naturals below 2^53 and any value past 2^53 − 1, where the proofs over the naturals stop describing
  the run, and a request that fails the rule's `assume` (no proof covers the step it would take). The GPU searches refuse a space whose values could pass 2^32 − 1.

## Numbers

On Modal CPUs (2 vCPU), generated JavaScript, the answers checked against the interpreter:

| Machine | 1k | 10k | 100k | 1M |
| --- | --- | --- | --- | --- |
| Per-key caps (`research/perf/grant-scale.ts`), requests | 0.3 ms | 2.5 ms | 29 ms | 267 ms |
| Window limit, pruned (`research/perf/window-scale.ts`), events | 0.8 ms | 3.1 ms | 16 ms | 136 ms |

Pruned, the window limit holds about 35 records whatever the event count; unpruned, each request scans every record kept
(76 ms at 10k events). The interpreter copies its maps each step (it's the reference, and searches branch from it):
1.6 s for 10k requests of the caps rule.

Measured against Bend and Lean on the same three rules ([`compare/`](compare/README.md)), gdp-wired's proofs are one
or two lines and check in 25–44 ms, against 74–117 lines of hand proof and 137–161 ms in Bend and 8–30 lines and
488–571 ms in Lean. Running each tool's proved code over 100,000 requests (whole command, Modal, 2 CPUs):

| | budget | caps | window |
| --- | --- | --- | --- |
| gdp-wired | 44 ms | 59 ms | 2.6 s |
| Bend | 92 s | 75 s | over 300 s |
| Lean | 8 ms | 205 ms | 8.7 s |

The proved Bend and Lean rules keep lists and scan them; gdp-wired runs maps and a log (unpruned in this window rule).
Lean, compiled natively, wins where the state stays small. Details in [`docs/comparison.md`](docs/comparison.md).

Proving and checking: a law over 64 steps proves in about 5 s, and Lean checks its theorem in 47 s (6 s by
`native_decide`); a law over 32 steps proves in about a second. What changed since the first release, and by how much:
[`CHANGELOG.md`](CHANGELOG.md).

## Layout

| Path | What |
| --- | --- |
| `core/` | Machines, the interpreter and JS compiler, the builders, composition (`compose.ts`), the linear solver and its checker, Houdini invariants, models, the first Lean export |
| `kernel/` | The trusted kernel and the untrusted prover, with soundness fuzz (`kernel.test.ts`, `history.test.ts`) |
| `lean-kernel/` | The kernel's Lean twin, its soundness proofs, and the exported trees |
| `examples/` | The builders at work: `domains/` (187 rules across 21 domains, each with laws and broken variants), `harness.ts` (the triple check), `readme.ts`, `guide.ts` (the guide's code), `groups.ts` (two groups decided at every pair), `budget.ts`, `gdp.ts` (gdp-ts's example, its checks proven), `exists.ts` (laws with "there exists"), `datatypes.ts` (records and variants), `lemmas.ts` (recurrences and their lemmas), `invoices.ts` (lists a request carries), `folds.ts` (folds over trees), `trees.ts` (trees and lists of lists in the state), `composition.ts`, `sets.ts`, `quantifiers.ts`, `functions.ts`, `arith.ts` (division and remainder by a constant, integers in rules and datatypes), `lists.ts`, `sizes.ts`, `liveness.ts`, `steps.ts` (laws over up to 64 steps), and `jev-fabric/` (a Bend project's 59 proven laws, ported) |
| `docs/` | The comparison with Bend and Lean, and the full scope |
| `compare/` | The same three rules in gdp-wired, Bend and plain Lean, checked and measured |
| `research/` | Everything around the library ([`research/README.md`](research/README.md)): the GPU searches (`search/`, `hw/`, `modal-gpu/`), invariant and rank synthesis (`synth/`), relational laws and guard synthesis (`next/`), bit-vector laws (`sat/`), the enumeration and benchmarks (`enum/`, `gpu/`, `perf/`), the first Lean checker (`lean/`) and the first prototype, the audit path (`audit/`) |
| `modal/` | Everything above as Modal jobs: `suite.json` is the regression suite |
| `scripts/` | The package build, the smoke test of the packed tarball, the Lean library generator, the diagram |
| `vendor/handwired` | [monotykamary/handwired](https://github.com/monotykamary/handwired), branch `u32-words`: Cheng Lou's Handwired with exact u32 word circuits and word stages in loop programs |
| `vendor/gdp-ts` | [rauchg/gdp-ts](https://github.com/rauchg/gdp-ts) |

The npm package is built from `core/`, `kernel/` and `lean-kernel/` alone; nothing in it imports `research/`.

## Running

The npm package is the library: the builders (`gdp-wired`), the runtimes (`gdp-wired/machine`), composition
(`gdp-wired/compose`), XState machines as charts (`gdp-wired/xstate`), rules read from the code (`gdp-wired/extract`, with
`typescript` installed), lemmas nobody stated (`gdp-wired/discover`), invariant
inference (`gdp-wired/infer`), the
Lean export (`gdp-wired/lean`), the kernel (`gdp-wired/kernel`), the prover (`gdp-wired/prove`), the derivation checker
and solver (`gdp-wired/check`, `gdp-wired/solver`). Everything else here (examples, comparisons, the Lean twin, the GPU
searches) runs from a clone and needs [Bun](https://bun.sh); Lean 4.34.0 for `lean/` and `lean-kernel/`; a WebGPU
runtime (Chrome, or Dawn's node bindings) for the GPU parts. Releases: bump `version` in `package.json` and push to
main; `.github/workflows/publish.yml` publishes it with npm provenance.

```sh
git clone --recursive https://github.com/monotykamary/gdp-wired && cd gdp-wired
bun examples/budget.ts
bun test core/compile.test.ts core/runtime.test.ts kernel/history.test.ts
cd kernel && bun run-kernel.ts && bun test kernel.test.ts
```

The whole suite (163 jobs, about 10 minutes of wall time and 46 minutes of job time) runs on [Modal](https://modal.com):

```sh
modal run modal/run.py --jobs modal/suite.json --out runs/modal/suite && sh modal/reap.sh
```

Each directory's README has its own runs and results.

## The skill

`npx skills add monotykamary/gdp-wired` installs a skill that guides coding agents (and people) through writing a rule
the way the code does it, stating its laws, reading a refused proof and handing a claim to Lean:

- [**Workflow**](skills/gdp-wired/SKILL.md#workflow): the checklist for adding or changing a rule whose invariants matter.
- [**Writing rules**](skills/gdp-wired/references/writing-rules.md): kinds, maps, step and k-step laws, histories,
  liveness, decisions, two-run laws, loops.
- [**Reading verdicts**](skills/gdp-wired/references/reading-verdicts.md): a bug or a missing invariant, and what to
  change.
- [**Shipping**](skills/gdp-wired/references/shipping.md): running the proven rule, and holding existing code to it.
- [**The Lean handoff**](skills/gdp-wired/references/lean-handoff.md): exporting the proofs, and functions proven in Lean.
- [**Where it fits**](skills/gdp-wired/references/where-it-fits.md): gdp-wired, Lean or Bend.

## Credits

[gdp-ts](https://github.com/rauchg/gdp-ts) by Guillermo Rauch (Ghosts of Departed Proofs for TypeScript) is where the
audit path starts, and what `gdp-wired/gdp` mints proofs for; [Handwired](https://github.com/chenglou/handwired) by Cheng Lou is the circuit and GPU runtime this
builds on, through a fork; [Bend](https://github.com/bendlang/bend) is the language the laws were first written in,
and the yardstick for the benchmarks.

## License

MIT
