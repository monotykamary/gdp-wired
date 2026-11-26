# What it proves

Everything gdp-wired proves automatically, each with the example that runs it. Every proof here is also a Lean
theorem. The [README](../README.md#what-it-proves) has the short list.

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
  laws prove like any rule's (`examples/charts.ts`). Not yet: parallel regions inside a state (XState's entry and exit
  actions, eventless and delayed transitions are read by `fromXState`, below).
- **With XState and `@xstate/graph`** (`gdp-wired/xstate`, [`docs/xstate.md`](xstate.md)): prove a rule or chart
  and present it as XState v5 `ActorLogic` with `toLogic(ruleOrChart, {params, maxValue})` (copied states via
  `rule.interpreter()`, canonical `serializeState` over maps and logs, small-edge default `events`) so `@xstate/graph`'s
  `TestModel` generates shortest paths against your real app, and `runToEvents(ruleOrChart, run)` turns prover
  counterexamples into `getPathsFromEvents` regression paths (`examples/xstate-mbt.ts`). For an existing XState v5/v4
  machine, `fromXState(machine, {guards, actions})` translates it into a provable chart (nesting, parallel roots, deep
  history, `invoke`/`after`, `always` and `entry`/`exit` macrosteps; unsupported keys refused) and `conforms(chart,
  machine, createActor)` checks it against XState's own actor (`examples/xstate.ts`). The proof covers the logic;
  model-based tests cover the app around it.
- **Rules read from the code** (`gdp-wired/extract`): `extract('./bucket.ts')` reads a reducer, `useReducer`'s, functions
  over one record, a class whose methods write its fields (with the classes it extends), or the object of functions a
  factory returns, and returns the rule that steps the same way, as a builder value and as source to keep
  (`toSource`); `extractXState('./machine.ts')` reads an XState machine, or a function that makes one, its guards and
  actions named or inline, into a chart and its rule (xstate the one the file's project has). The extractor is untrusted: each rule is run beside the code it was read from (requests
  from the start, steps from drawn states and from the prover's counterexamples, every state, cell, list, result and
  refusal compared, the code's branches counted), and a difference refuses it. Its subset (integers, booleans, strings
  and string-literal unions, values that may be null, records, Map and Record keyed state, arrays as lists, Dates as
  their time, branches and early returns, throws as refusals, `Date.now()` as an input) and what it refuses, each with
  the place and the reason, are in `core/extract.ts`.
- **Effect services** (`gdp-wired/effect`, `effect` 3.x or 4.x): `extractEffect('./limiter.ts')` reads a service
  whose make effect creates Refs (Ref, SynchronizedRef, SubscriptionRef, 4.x's TxRef) and returns an object of methods
  (`Effect.fn` bodies, arrows returning an effect), with typed failures as its refusals and `Clock.currentTimeMillis` as
  an input; the rule is checked by running the service on Effect's runtime (the `effect` the file's project has,
  `Effect.runSyncExit`, the clock fixed at each request's time), every Ref, result and failure compared. Transactions
  (3.x STM's TRef, 4.x `Effect.tx` over TxRefs) are atomic steps, waits (`STM.check`, `Effect.txRetry`) their guards,
  and a method of several transactions is every fiber's steps (core/system.ts's `lift`), so a lost update comes back as
  a run of two fibers; `Effect.retry` and `Effect.repeat` inside a method are part of its step. A `Schedule` is a rule of
  its decisions (attempt, retries, delay, elapsed, done; exponential a `recur` function, jitter an input within its
  range), every combinator a fragment of one machine, checked by stepping Effect's own schedule
  (`examples/effect-retry.ts`, `examples/effect-stm.ts`). A `Queue` (bounded, dropping, sliding, unbounded) or a
  `Semaphore` the service makes is modelled once, its own laws proven (bounded, nothing lost, FIFO, the permits) and
  run beside Effect's own on random operations and fibers, so a law states only the service's own
  (`examples/effect-queue.ts`: a worker pool, a release without its acquire refuted by a run). `conforms(rule, service)` runs a rule written by hand
  beside a running service (Effect's own Semaphore, a store). `fromSchema(schema)` provides typed symbolic
  [Schema kinds](effect-schema.md): exact on declared closed decoded values by default, with checked integer
  bounds and inspectable, opt-in approximation losses
  (`examples/effect.ts`; what is read and refused, with what Effect projects write, in `research/effect/README.md`).
- **What nobody stated, looked for when the prover alone stops**: where `proveRule` or `proveSteps` doesn't prove the laws
  and no run breaks them, it looks for lemmas about the rule's recurrences and lists (`discover`), lemmas about the
  functions it knows by their facts (`cycleLemmas`, each proven by a cyclic proof) and then invariants (`inferLaws`),
  under a configurable search allowance (`{search: {ms: 10000}}` by default; `{search: false}`, the prover alone);
  the verdict's `found` holds what proved them, as laws and lemmas with the source to paste. Callers who pass several
  laws on the same rule (`proveRule(rule, [law1, law2])` or `proveSteps(rule, laws, [step1, step2])`) already get joint
  proof — the search and kernel check all of them together as one family, rather than proving one law at a time.
  [Explicit counted work and stop causes](search-budgets.md) separate the search allowance from an optional
  real-time safety watchdog; legacy `ms` is not a promise of machine-independent completion. Each invariant found holds in the states reachable from the
  start, so a proof that needs one holds there and the verdict says so (`assumes: {states: 'reachable', laws}`). Code that
  steps the rule from states it is handed proves with `{from: 'any'}`: every step law then holds from every state the
  laws allow, reachable or not, and the search never adds an invariant.
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
- **Rules over the rationals** (`gdp-wired/rationals`): `ratRule` with `rat` and `nonneg` params, inputs and state,
  each value an exact rational (0.1 is 1/10, a third is 1/3: nothing scaled to cents or encoded as naturals), terms
  linear (+, −, × and ÷ by a constant, min, max, when). Linear arithmetic over ℚ is decidable: a law is proven by
  trees whose leaves are Farkas certificates with strict rows, or refuted by an exact run from the start. A fee split,
  a rate limiter with fractional tokens and a ledger in decimals, and 12 laws true over one of ℕ and ℚ and false over
  the other, each decided both ways (`examples/rationals.ts`); the proofs again in Lean (`Rationals.lean`'s
  `Q.machine_sound`). Products of unknowns and transcendental functions stay outside.
- **Recursive datatypes as values** (`gdp-wired/data`): lists, trees, rose trees and their forests, declared by their
  constructors; functions over them by structural recursion, or by any recursion whose termination is proven first (a
  merge of two lists, a quicksort: the measure found, (size xs, size ys) or a sum of sizes, and each call's decrease
  proven by the kernel before the function's equation is used; one that doesn't terminate is refused with the reason);
  `proveData` finds the induction (structural, mutual, or the function's own call graph ranked by its measure) and the
  lemmas, each proof checked in Lean against the `inductive` and the functions as declared (`examples/data.ts`).
  An abstract sort (`opaque('Elem')`: values compared by equality alone, any other read refused) makes a law hold at
  every element type, not only the naturals; `unknownFn('f', [Elem], List)` is any function between sorts (a law about
  every f, every default, every callback); `closures(...)` is a datatype of functions with its `apply`, for fields that
  hold functions (`examples/abstract.ts`; Lean's twin doesn't yet close two shapes of its export there: a datatype of
  two constructors with fields, and two constructor values compared inside a disjunction).
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
- **Laws about two runs of a stateful rule** (`gdp-wired/relational`): noninterference (`noninterference(rule, {secret,
  visible})`: what a party sees never depends on the secret, nor which requests fail), tenant isolation (`isolation(rule,
  {owner})`: what tenant B sees is the same whatever the others do) and migration agreement (`agreement(old, next)`),
  on rules read from code as on written ones; `proveTwoRuns` proves the law of the two runs side by side as one rule, a
  refutation the two runs (`research/regulated/`).

When a law is false, the prover or GPU search finds a real run that breaks it, and `minimizeRun(rule, law, run)`
([`docs/minimize.md`](minimize.md)) shrinks a refuting run on the original rule until no single request can be
removed. When a law needs an invariant nobody wrote, `proveRule` proposes checked covering sums for item-against-total
laws and `inferLaws` finds invariants on the CPU (and the GPU synthesizer, at scale, in `research/synth/`) and the kernel proves it.

**What it leaves to Lean or Bend.** Two things, and neither is a gap the next feature closes: proofs the prover would
have to invent (induction over a recursive structure whose proof needs a lemma nobody stated and `discover` doesn't find, and arithmetic with
products of unknowns beyond what products of facts and sums of squares give; integer arithmetic with induction or
with products is undecidable; a lemma you state about a recurrence is proven, and `proveData` finds the induction and lemmas for a recursive datatype as a value, up to six symbols a lemma, for
functions structural or whose termination it proves, its values naturals, integers (`integer`, Lean's `Int`, beside
`natural`) and datatypes), and shipping an arbitrary algorithm as its proved source (gdp-wired ships the rule as JavaScript; Bend
compiles the proved source itself). The full list of what is and isn't in scope is in
[`docs/comparison.md`](comparison.md#gdp-wireds-scope-in-detail).
