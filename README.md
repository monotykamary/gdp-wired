<img src="https://raw.githubusercontent.com/monotykamary/gdp-wired/main/static/banner-ink.svg" alt="gdp-wired" width="100%" />

# gdp-wired

An automatic prover for stateful rules: budgets, caps, rate limits, workflows, access policies. Write the rule and the
laws it must keep; gdp-wired proves them with no proof to write, shows a real run that breaks them when they're false
(searched on the GPU), checks every proof again in Lean, and ships the rule as JavaScript.

Proofs are checked by a small trusted kernel; the prover that writes them is untrusted, and the kernel's Lean twin is
proven sound. On the three rules in [`compare/`](compare/README.md), the proof is a one- or two-line call and checks in
25–44 ms, against 74–117 lines of hand proof and 137–161 ms in Bend, and 8–30 lines and 488–571 ms in Lean.

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

## Scope: what it proves by itself, and where the wall is

gdp-wired is an automatic prover, not a language: laws about **stateful rules** (counters, totals, maps, sets and lists
of names, logs summed over time, steps in a row, runs that go on forever), proven without a proof to write, with the
rule shipped as code. With Lean beside it, it says what Bend says; where a proof needs more than its kernel decides, the
proof is Lean's, as a fact about a function the rule reads:

| It expresses and proves | It does not (today) |
| --- | --- |
| Step machines over naturals: scalars, maps from naturals to naturals (a write at one key, or at every key, per map per step), named step conditions, preconditions on params, assumptions per request | Strings, and lists as values (a list in a map's cell, lists of lists) |
| Lists of names (`.lists(...)`): positions and a length, `push`, `pop`, `set`, and `insertAt`/`removeAt` that keep the order (positions shift: a write at every key reading its key at k ∸ 1 or k + 1, which the runtimes decide on breakpoints); laws about every two positions or more (`forall((i, j) => ...)`: "strictly increasing", so no name twice; `forall((i, j, k) => ...)`: "any three cells repeat a value"), and step laws that an insert puts its name in, keeps every name, and a removal takes it out (`examples/lists.ts`, a scope kept in normal form) | |
| Sets of names, as maps of 0/1 cells over names interned to numbers: a request carrying whole sets (`.carries`), conditions about every key (`everyKey`, `has`, `subsetOf`, `disjointFrom`, `sameAs`) anywhere in a step (each named as a flag of its own) and inside laws (pulled out as the law's key), the key read alone or plus or less a term and compared (`k < n`, `M[k + 1]`), writes at every key in one step (`each`); laws, step laws and k-step laws over them, each also a Lean theorem; a set's size over a universe of names (`within(n)`, `sizeBelow(n)`: the sum of its cells, exact for names interned below n; `examples/sizes.ts`) | A set's size over unbounded names (Lean's maps have no finite support, so no sum over every key) |
| Some key (`someKey`): "something was added, so some name is in", proven through a witness, a term naming the key, that the prover finds among the state, the params, the law's key and the request (or the one the law names) | A witness no term of the state names (which a ghost can keep: the last key added, say) |
| Functions from outside the rule (`fn`, and `divBy`, `modBy` for division and remainder by a constant): read like maps, known to the kernel only by their facts, which every goal may assume; the Lean export states the facts as the hypothesis they are, and proves them in Lean where the function has a Lean definition (`divBy` and `modBy` by `omega`); the GPU search and the GPU invariant synthesis tabulate each function over the keys they can read it at | Facts proven by gdp-wired (they are Lean's to prove) |
| Invariants of the state and params, laws about every key of a map; step laws relating one step's before and after (`s'`, `M'[k]`: "only increases", "stays retired"), and k-step laws about k steps in a row ("two grants on one day add two", up to 16 steps); orderings at any distance through ghost state ("a refund never follows a release": `ghost` with `ever`, `count`); liveness under fairness (`leadsTo`: "every ticket issued is served", in every run that sends each helpful request infinitely often, by a rank that drops: one natural or several compared in order; several helpful requests, each in the region where it helps; a request naming some inputs and leaving the rest, and the sets it carries, free), for machines with maps, with sets, and with a history (its queries free, within its relations); a Lean theorem over runs, and under weak fairness too (each helpful request taken whenever it stays allowed, proven allowed in its region: its free inputs at any value, or at a witness the exporter finds among 0, the state and the params, a history's query among them; the sets it carries empty) | |
| Composition: rules side by side (`product`), taking turns (`interleave`), and one rule refining another (`refinement`: a forward simulation, the spec allowing every request it is sent, steps the spec doesn't see as `stutter`, and `steps(spec, k)` where the spec takes several steps for one of the implementation's: a transfer at once refines a withdrawal then a deposit), each built as a plain machine so every law above applies; what a refinement means is a Lean theorem (`refines`: every reachable state of the implementation beside a reachable state of the spec, related by every law), for machines with maps and flags and for machines with sets (`srefines`: the sets a request carries shared by name, writes at every key, flags at every key) | Refinement where the number of spec steps depends on the state (beyond a bound k with skips) |
| Laws about one key of a map at a time, or about scalars; totals across a map's keys through a ghost total ("in use equals what the clients hold") | Sums across a map's keys other than through a ghost total |
| Histories: sums and queries over a log of requests, relations between them proven one record at a time, pruning | Quantifiers over sequences other than a machine's own history |
| Decisions over facts: flags, one-of choices, optional facts, bounded naturals (`match` covers every case) | Datatypes beyond those encodings (except as a function's arguments: a list as a number a Lean function decodes); reals |
| Loops that halt by a rank or a tuple of ranks; folds over binary trees; progress laws ("some request makes this happen"); recursion defined in Lean, entered as a function with its facts | Induction the prover would have to invent (the wall below) |
| Arithmetic: `+`, truncated `−`, `×` by a constant, `min`, `max`, `if`, products of two terms (proven by the kernel, less well by the prover), division and remainder by a constant (`divBy`, `modBy`) | Generated code for decisions alone (`compileJs` emits machines; a predicate emitter is planned) |

**The wall.** What stays outside is one of two things, and neither is a gap the next construct closes:

- **Induction the prover would have to invent.** A property of a recursive structure you define (a tree, every prefix
  of a list of lists) whose proof needs a lemma nobody stated. No automatic prover proves all of these: arithmetic with
  induction is undecidable. Here the proof is written in Lean, and gdp-wired uses it: define the function in Lean,
  prove its facts there, and give the rule `fn(arity, js, {facts, lean})`. The steps, the state, the maps and the laws
  around it stay automatic, and the Lean export takes the facts as the hypothesis they are.
- **An arbitrary algorithm shipped as its proved source.** gdp-wired ships the rule as JavaScript and runs a function's
  own JavaScript beside its Lean definition (held to it by tests, not by a compiler). Bend compiles the proved source
  itself.

The engineering list is closed. Each other "does not" above has a route already: a ghost (a witness no term names, a
sum across a map's keys), a bound with skips (spec steps that vary), an encoding (strings, datatypes as numbers a Lean
function decodes), or Lean itself (a function you define and prove there). Use gdp-wired where the rule is a budget, a cap, a
window, a workflow, a policy decision, an authority over sets of names or a list kept in normal form
(`examples/sets.ts`, `examples/lists.ts`): it proves those without proof files, finds counterexample runs when they're
false, and checks its own kernel in Lean. Keep Bend (or Lean) where the proof is the induction above.

For a sense of the split: in one real codebase with 98 Bend laws and about 1,600 lines of hand proofs, the policy
decisions, the compare-and-swap storage plans and the state/provider plans fit gdp-wired as it is (with names interned
to numbers), and gdp-wired can prove more about storage than its Bend proofs state (no revision reuse across keys); the
lifecycle machine's before/after laws are step laws (as in `release lifecycle` in `examples/`); the authority checks,
built on lists of names used as sets, fit as sets of names (all ten of its authority laws proven automatically, and the
rule agrees with the compiled Bend on all 7,654 outcomes over four names); the resource checks, which normalize scopes
that are lists of paths (lists of lists of names) and compare their prefixes, are induction over nested lists: the wall,
so they stay in Bend, or go to Lean as functions with proven facts. `compare/` puts three rules side by side in gdp-wired, Bend and plain Lean, with line counts and
check times.

## What's trusted

| Part | Trusted? | What it does |
| --- | --- | --- |
| `kernel/kernel.ts`, `core/check.ts` | **Yes** | Turns a machine and its laws into goals and checks a proof tree for each: splits on linear atoms, a Fourier–Motzkin derivation at each leaf. Every rule (step machines with maps and flags, step laws and k-step laws, loops with ranks, progress, folds over trees) is a few moves of one small algebra of runs: conditions holding where a run is, a step taken from there, a conclusion read at the end or across the run. Histories become plain machines first. Refuses names a machine doesn't declare |
| `kernel/prove.ts` | No | Grows the trees. If it's wrong, the kernel rejects the tree |
| `lean-kernel/` | Optional | The kernel's twin in Lean 4.34.0, each rule proven sound (`Kern.sound`, `machine_sound`, `mmachine_sound`, `fmmachine_sound`, `loop_sound`, `fold_sound`, `progress_sound`, `steplaw_sound`, `kstep_sound`, `hmachine_sound`, `smachine_sound` with functions' facts and laws about several keys, `skstep_sound`, `leads_sound`, `leads_wf_sound` and `sleads_sound` for liveness over runs), what a ghost means (`ghost_laws`, `ghost_run`, `ever_meaning`) and what a refinement means (`refines`, `srefines`), axioms `propext`, `Classical.choice`, `Quot.sound` only. The exporter sends the kernel's real trees; tampered ones compute to false |
| `search/`, `synth/`, `hw/` | No | GPU work: counterexample search over every short history (for laws, step laws and k-step laws, machines with a log of requests too), and invariant/rank synthesis. Every hit is replayed by the interpreter or proven by the kernel before it counts |
| `core/dsl.ts`, `core/compose.ts`, the runtimes | No | The builders and combinators compile to the kernel's plain values; the interpreter and generated JavaScript are held to the reference evaluator by the conformance test, and the combinators to runs of their parts |

How the untrusted parts are held to the trusted ones, automatically:

- **Types**: the whole repo type-checks strictly (`noImplicitReturns`, `noFallthroughCasesInSwitch`,
  `noUncheckedIndexedAccess`), and a type-aware lint denies warnings; every switch over term and condition operations is
  exhaustive and ends in `unreachable()`, so a new operation fails to compile wherever it's missing.
- **Conformance** (`core/conformance.test.ts`): random terms over every operation through every consumer (interpreter,
  generated JS, the kernel on fixed values, the GPU search's u32 twin, the old symbolic prover) against the reference
  evaluator, and the same cases through Lean's own `evalE` (`lean-kernel/conformance.ts`).
- **Examples** (`examples/`): every law proven by the kernel and re-checked by Lean, every rule run at random through
  both runtimes, and every broken variant broken by a real run (a refused proof alone could be the prover's weakness).
- **One description, three readings**: a law or step law is proven by the kernel, read on one run by `core/watch.ts` (the
  examples' runs, every replay), and searched for a breaking run by the Handwired search; `hw/check-steps.ts` holds the
  search to the watcher on whole spaces, and all three to each other on random machines and laws.
- **Tampering and mutation** (`kernel/tamper.test.ts`, `kernel/refusals.test.ts`, `kernel/mutants.ts`): real proofs
  broken structurally or offered for weakened goals that have a model must be rejected, every refusal the kernel makes is
  exercised, and every one-operator mutation of `kernel.ts` and `check.ts` is run against the tests to find what they
  don't notice: 239 of 261 mutants are caught, and the 22 left are equivalent (`kernel/MUTANTS.md`).
- **Fuzz**: the kernel never accepts a refutation of something with a model (`kernel/kernel.test.ts`), and laws proven
  over histories hold on every run (`kernel/history.test.ts`).

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

- **Kinds**: `nat`, `upTo(k)`, `bool`, `oneOf(...)`, `maybe(kind)`; their assumptions (a bit is 0 or 1, a choice is in
  range) go to the kernel by themselves, and `encodeInput`/`encodeParams` turn runtime values into the numbers the
  machine reads.
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
- **Loops** (`loop(...)`): state, `while`, `body`, a `rank` (or a tuple of ranks) that must drop each turn.
- **Lean** (`gdp-wired/lean`): `toLean([{id, machine, laws, stepLaws}, ...])` writes the proofs as a Lean file, and
  `leanProject(file)` a Lake project with the twin, so `lake build` checks them. Each law comes as the twin's theorem and
  as a plain statement over named variables, e.g. `theorem budget.law0 (h : FMReach budget_machine ρ μ) : ρ «s» ≤
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
| Per-key caps (`perf/grant-scale.ts`), requests | 0.3 ms | 2.5 ms | 29 ms | 267 ms |
| Window limit, pruned (`perf/window-scale.ts`), events | 0.8 ms | 3.1 ms | 16 ms | 136 ms |

Pruned, the window limit holds about 35 records whatever the event count; unpruned, each request scans every record kept
(76 ms at 10k events). The interpreter copies its maps each step (it's the reference, and searches branch from it):
1.6 s for 10k requests of the caps rule.

A brute-force enumeration of 2^31 worlds (`enum/`, `perf/bend-enum/`), the same predicate as Bend programs and as a
Handwired word program: on an M2, Bend takes 985 ms sequential, 221 ms parallel and 153 ms on Metal (whole process,
about 130 ms of it device setup); ours takes 33 ms warm on WebGPU, with about 115 ms of device setup first. On an NVIDIA
L4 ours takes 5 ms warm; Bend's CUDA build compiled, but its GPU runs hung in our tests (its CPU builds ran: 109 ms
parallel).

## Compared with Bend and Lean

`compare/` writes three rules (a budget, per-key caps, a sliding-window limit) in gdp-wired, in Bend 2 and in plain Lean
4, each checked by its own tool on Modal, each also handed the same bug to reject. From `compare/README.md`:

| | Rule lines | Law lines | Proof lines | Check (median, whole command) |
| --- | --- | --- | --- | --- |
| gdp-wired | 5–7 | 1–4 | 1–2 (`proveRule`) | 25–44 ms |
| Bend 2 | 39–98 (25–50 of them proof evidence in the rule) | 5–26 | 74–117 | 137–161 ms (`--verdict` 167–178 ms) |
| Lean 4 (by hand) | 4–15 | 1–4 | 8–30 | 488–571 ms |

Most of each time is the tool's startup (17, 134 and 453 ms). gdp-wired's kernel trees for the same rules re-check in
its Lean twin in 1.35 s. What each proves, what each ships at runtime, and where each is the better tool are in
`compare/README.md`.

## Layout

| Path | What |
| --- | --- |
| `core/` | Machines, the interpreter and JS compiler, the builders, composition (`compose.ts`), the linear solver and its checker, Houdini invariants, models, the first Lean export |
| `kernel/` | The trusted kernel and the untrusted prover, with soundness fuzz (`kernel.test.ts`, `history.test.ts`) |
| `lean/`, `lean-kernel/` | Lean: the derivation checker `Cert.lean`, and the kernel's twin with its exported trees |
| `search/`, `hw/`, `modal-gpu/` | Counterexample search on the GPU: a hand-written WGSL kernel, and the same through the Handwired fork's word stages |
| `synth/` | Invariants and ranks found on the GPU, proven by the kernel |
| `next/` | Guards synthesized from laws, relational laws (migrations, tenant isolation, through `core/compose.ts`), a ReBAC audit |
| `sat/` | Bit-vector laws: bit-blasted, solved, LRAT-checked in TypeScript, optionally by Lean |
| `enum/`, `perf/` | The enumeration, and the benchmarks |
| `examples/` | The builders at work: `domains/` (92 rules across nine domains, each with laws and broken variants), `harness.ts` (the triple check), `readme.ts`, `budget.ts`, `composition.ts`, `sets.ts`, `quantifiers.ts`, `functions.ts`, `lists.ts`, `sizes.ts`, `liveness.ts` |
| `compare/` | The same three rules in gdp-wired, Bend and plain Lean, checked and measured |
| `spec.ts`, `gdp.ts`, `circuit.ts`, `laws.ts` | The audit path: gdp-ts predicates written once, as trusted provers per request and as a Handwired circuit that decides every (user, project) pair at once |
| `modal/` | Everything above as Modal jobs: `suite.json` is the regression suite |
| `vendor/handwired` | [monotykamary/handwired](https://github.com/monotykamary/handwired), branch `u32-words`: Cheng Lou's Handwired with exact u32 word circuits and word stages in loop programs |
| `vendor/gdp-ts` | [rauchg/gdp-ts](https://github.com/rauchg/gdp-ts) |

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
