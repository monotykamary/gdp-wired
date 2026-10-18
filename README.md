<img src="https://raw.githubusercontent.com/monotykamary/gdp-wired/main/static/banner-ink.svg" alt="gdp-wired" width="100%" />

# gdp-wired

An automatic prover for stateful rules: budgets, caps, rate limits, workflows, access policies. You write the rule and
the laws it must keep. gdp-wired proves them with no proof to write, shows a real run that breaks a law when it's false
(found by searching on the GPU), has every proof checked again by Lean, and ships the rule as JavaScript.

```sh
npm install gdp-wired   # or bun add gdp-wired; plain JavaScript with types, Node 20+, Bun or a browser
```

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
and `examples/domains/` holds 92 rules from nine domains (finance, access control, public services, operations,
protocols, commerce, supply chains, games, education), each checked three ways.

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
  about every key, lists kept in order (`examples/sets.ts`, `examples/lists.ts`).
- **Step laws**: what one step does ("a balance only goes down", "a grant adds one"), and laws over several steps in a
  row.
- **Histories**: sums and queries over a log of requests, like a sliding-window rate limit.
- **Orderings at any distance**: "a refund never follows a release", through ghost state that watches the rule.
- **Liveness**: "every ticket issued is served", in every run that keeps sending the requests that help, including under
  weak fairness (`examples/liveness.ts`).
- **Refinement**: an implementation behaves like a simpler spec, step for step (`examples/composition.ts`).
- **Functions**: division, remainder, and your own functions, known by their facts; a function defined in Lean brings
  facts proven there (`examples/functions.ts`).
- **Pure functions and two-run laws**: laws about what a function returns, and laws comparing two calls, like "the
  secret never changes the answer". `examples/jev-fabric/` ports a Bend project's policy core and proves all 59 laws its
  Bend proofs state.

When a law is false, the GPU search finds a real run that breaks it. When a law needs an invariant nobody wrote, the GPU
synthesizer finds one and the kernel proves it.

**What it leaves to Lean or Bend.** Two things, and neither is a gap the next feature closes: proofs the prover would
have to invent (induction over a recursive structure whose proof needs a lemma nobody stated, and arithmetic with
products of unknowns beyond multiplying two known facts; integer arithmetic with induction or with products is
undecidable), and shipping an arbitrary algorithm as its proved source (gdp-wired ships the rule as JavaScript; Bend
compiles the proved source itself). The full list of what is and isn't in scope is in
[`docs/comparison.md`](docs/comparison.md#gdp-wireds-scope-in-detail).

## Why you can trust a proof

A small kernel checks every proof; the prover that finds them is untrusted, and the kernel's twin in Lean is proven
sound.

| Part | Trusted? | What it does |
| --- | --- | --- |
| `kernel/kernel.ts`, `core/check.ts` | **Yes** | Turns a rule and its laws into goals, and checks a proof tree for each: case splits on linear facts, then a linear refutation at each leaf |
| `kernel/prove.ts` | No | Finds the proof trees. If it's wrong, the kernel rejects the tree |
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

## Writing laws

The builders (`core/dsl.ts`) hand out typed values for every name you declare; everything compiles to the plain machine
the kernel checks, so nothing in them is trusted.

```ts
import {bool, count, forall, maybe, nat, oneOf, proveSteps, relation, rule, yes} from 'gdp-wired'

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
```


- **Kinds**: `nat`, `upTo(k)`, `bool`, `oneOf(...)`, `maybe(kind)`, `int`, `decimal(places)`, `str({like, maxLength})`;
  their assumptions (a bit is 0 or 1, a choice is in range) go to the kernel by themselves, and
  `encodeInput`/`encodeParams` turn runtime values into the numbers the machine reads.
- **State of any kind**: `.state({open: bool.from(true), status: oneOf('new', 'done').from('new'), owner: str().from(''), note: maybe(nat).from(null)})`;
  a step writes each kind's own values, `when(c, a, b)` chooses between any two values of a kind, and `rule.decode(state)`
  reads them back as runtime values.
- **Integers and decimals**: `int` and `decimal(places)` inputs, `.ints({...})` and `.decimals(places, {...})` state;
  `plus`, `minus`, `negate`, `times(k)` (k may be negative), `min`, `max`, `abs`, `isNegative`, comparisons with numbers
  (a decimal's literals are scaled: `price.atMost(19.99)`). Each is two naturals underneath, so the kernel and the Lean
  twin see nothing new; `rule.decode(state)` reads them back as numbers.
- **Strings**: `str({like: ['*.internal'], maxLength: 64})`. A string is its interned name, its length and a bit per
  declared pattern (Cedar's glob), all computed from the string itself when the input is encoded. `s.like(pattern)`,
  `s.eq('admin')` (which carries the literal's length and pattern bits, so laws reason from either), `s.isEmpty`,
  `s.length`; sets of strings are carried maps keyed by `s.id`.
- **Arithmetic** over the naturals: `plus`, `minus` (truncated), `times(k)`, `mul` (a product of two terms), `min`,
  `max`, `when(cond, a, b)`, `count(cond)`; conditions `lt`, `atMost`, `eq`, `and`, `or`, `not`, `implies`.
- **Sets and quantifiers**: `.carries(...)` for sets a request brings, `everyKey(k => ...)` (and `has`, `subsetOf`,
  `disjointFrom`, `sameAs`) anywhere in a step or inside a law, `M.each(k => ...)` to write every key, and
  `someKey(k => ..., witness?)` for "some key where", proven through a witness the prover finds or the one given.
- **Functions** (`.fns({perMinute: divBy(60)})`, or `fn(arity, js, {facts, lean})` for your own): read like params that
  take arguments, `perMinute(t)`; the kernel knows each only by its facts (`.facts(...)`, and a library function's
  own), and the Lean export takes them as the hypothesis they are, proving them where the function has a Lean
  definition. A function defined and proven in Lean is how a rule reaches past what the kernel decides: `examples/functions.ts`.
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
- **Loops** (`loop(...)`): state, `while`, `body`, a `rank` (or a tuple of ranks) that must drop each turn.
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
  the run. The GPU searches refuse a space whose values could pass 2^32 − 1.

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

## Layout

| Path | What |
| --- | --- |
| `core/` | Machines, the interpreter and JS compiler, the builders, composition (`compose.ts`), the linear solver and its checker, Houdini invariants, models, the first Lean export |
| `kernel/` | The trusted kernel and the untrusted prover, with soundness fuzz (`kernel.test.ts`, `history.test.ts`) |
| `lean-kernel/` | The kernel's Lean twin, its soundness proofs, and the exported trees |
| `examples/` | The builders at work: `domains/` (92 rules across nine domains, each with laws and broken variants), `harness.ts` (the triple check), `readme.ts`, `budget.ts`, `composition.ts`, `sets.ts`, `quantifiers.ts`, `functions.ts`, `lists.ts`, `sizes.ts`, `liveness.ts`, `steps.ts` (laws over up to 16 steps), and `jev-fabric/` (a Bend project's 59 proven laws, ported) |
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
(`gdp-wired/compose`), the Lean export (`gdp-wired/lean`), the kernel
(`gdp-wired/kernel`), the prover (`gdp-wired/prove`), the derivation checker and solver (`gdp-wired/check`,
`gdp-wired/solver`). Everything else here (examples, comparisons, the Lean twin, the GPU searches) runs from a clone and
needs [Bun](https://bun.sh); Lean 4.34.0 for `lean/` and `lean-kernel/`; a WebGPU runtime (Chrome, or Dawn's node
bindings) for the GPU parts. Releases: bump `version` in `package.json` and push to main;
`.github/workflows/publish.yml` publishes it with npm provenance.

```sh
git clone --recursive https://github.com/monotykamary/gdp-wired && cd gdp-wired
bun examples/budget.ts
bun test core/compile.test.ts core/runtime.test.ts kernel/history.test.ts
cd kernel && bun run-kernel.ts && bun test kernel.test.ts
```

The whole suite (122 jobs, about 20 minutes of wall time) runs on [Modal](https://modal.com):

```sh
modal run modal/run.py --jobs modal/suite.json --out runs/modal/suite && sh modal/reap.sh
```

Each directory's README has its own runs and results.

## Credits

[gdp-ts](https://github.com/rauchg/gdp-ts) by Guillermo Rauch (Ghosts of Departed Proofs for TypeScript) is where the
audit path starts; [Handwired](https://github.com/chenglou/handwired) by Cheng Lou is the circuit and GPU runtime this
builds on, through a fork; [Bend](https://github.com/bendlang/bend) is the language the laws were first written in,
and the yardstick for the benchmarks.

## License

MIT
