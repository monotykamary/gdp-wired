# Writing laws

The builders, kind by kind. The [README](../README.md#writing-laws) has the short version; the snippets below are kept
type-checked and proven by `examples/readme.ts`.

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
  −4, −7 mod 2 is 1, as SMT-LIB and Lean's `Int` read them); on a tick, `floorTo(k)`, `ceilTo(k)`, `roundTo(k, mode)`
  (a half to the even one, up, down or away from 0) and `onTick(k)`, from those two. Each is two naturals underneath,
  so the kernel twin sees nothing new; the Lean export states each law about integers again over `Int` (`law0_int`,
  proven from the law over the naturals by `omega`), and `rule.decode(state)` reads them back as numbers. A natural's
  `minus` stays truncated: an integer is a kind of its own, chosen where a value may go below 0 (`examples/arith.ts`).
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
- **Retained proof lifting** (`gdp-wired/lift`): `gdp-wired lift capsule source.json --out proof` generates a fresh
  Lean project from a data-only proof capsule and source model, without invariant search. The default command checks
  the source laws in Lean; `--emit-only` does not claim acceptance. See [the lift guide](lift.md) for supported
  transports, hash-bound receipts, and the boundary between an encoded source theorem and an external specification.
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
