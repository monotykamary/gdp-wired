<img src="https://raw.githubusercontent.com/monotykamary/gdp-wired/main/static/banner-ink.svg" alt="gdp-wired" width="100%" />

# gdp-wired

Laws about stateful rules (budgets, caps, rate limits, access policies), proven in TypeScript by a small trusted
kernel, with an untrusted prover that writes the proofs, an optional Lean twin that checks the kernel itself, and GPU
searches that find counterexamples or the invariants a proof needs.

You write the rule once with typed builders and state what must always hold. The library proves it by induction (or
shows a real run that breaks it), and the same rule runs as an interpreter or ships as generated JavaScript.

```ts
import {min, nat, proveRule, rule, when} from './core/dsl.ts'

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

## Scope: where it replaces Bend, and where it doesn't

gdp-wired is meant to replace Bend where it matters in practice, not to be a language: laws about **stateful rules whose
state is counters, totals, maps of counters and logs summed over time**, proven automatically, with the rule shipped as
code. If the checker side finds new frontiers the scope may grow; until then:

| It expresses and proves | It does not (today) |
| --- | --- |
| Step machines over naturals: scalars, maps from naturals to naturals (one write per map per step), named step conditions, preconditions on params, assumptions per request | Lists, sets or strings as values: membership, subsets, equality of lists of names |
| Invariants of the state and params, laws about every key of a map; step laws relating one step's before and after (`s'`, `M'[k]`: "only increases", "stays retired") | Laws about runs of two or more steps ("a refund never follows a release" needs a state flag), or orderings beyond progress |
| Laws about one key of a map at a time, or about scalars | Totals across a map's keys ("the sum of every client's holdings equals in-use") |
| Histories: sums and queries over a log of requests, relations between them proven one record at a time, pruning | Unbounded recursion over data, quantifiers over sequences other than a machine's own history |
| Decisions over facts: flags, one-of choices, optional facts, bounded naturals (`match` covers every case) | Datatypes beyond those encodings; division, modulo, reals |
| Loops that halt by a rank or a tuple of ranks; folds over binary trees; progress laws ("some request makes this happen") | Arbitrary algorithms: there is no general recursion to prove things about |
| Arithmetic: `+`, truncated `−`, `×` by a constant, `min`, `max`, `if`, products of two terms (proven by the kernel, less well by the prover) | Generated code for decisions alone (`compileJs` emits machines; a predicate emitter is planned) |

Keep Bend where the specification is about **lists or sets of names** (resource scopes, capability subsets, normalization
that must refine its input), where a proof needs **induction over data structures**, or where the shipped code must be
the compiled proved source of an arbitrary algorithm. Use gdp-wired where the rule is a budget, a cap, a window, a
workflow or a policy decision: it proves those without proof files, finds counterexample runs when they're false, and
checks its own kernel in Lean.

For a sense of the split: in one real codebase with 98 Bend laws and about 1,600 lines of hand proofs, the policy
decisions, the compare-and-swap storage plans and the state/provider plans fit gdp-wired as it is (with names interned
to numbers), and gdp-wired can prove more about storage than its Bend proofs state (no revision reuse across keys); the
lifecycle machine's before/after laws are step laws (as in `release lifecycle` in `examples/`); the resource and authority checks, built on lists of names as
sets, stay in Bend. `compare/` puts three rules side by side in gdp-wired, Bend and plain Lean, with line counts and
check times.

## What's trusted

| Part | Trusted? | What it does |
| --- | --- | --- |
| `kernel/kernel.ts`, `core/check.ts` | **Yes** | Turns a machine and its laws into goals (the induction rules: step machines with maps and flags, step laws, loops with ranks, progress, folds over trees, histories) and checks a proof tree for each: splits on linear atoms, a Fourier–Motzkin derivation at each leaf. Refuses names a machine doesn't declare |
| `kernel/prove.ts` | No | Grows the trees. If it's wrong, the kernel rejects the tree |
| `lean-kernel/` | Optional | The kernel's twin in Lean 4.34.0, each rule proven sound (`Kern.sound`, `machine_sound`, `mmachine_sound`, `fmmachine_sound`, `loop_sound`, `fold_sound`, `progress_sound`, `steplaw_sound`, `hmachine_sound`), axioms `propext`, `Classical.choice`, `Quot.sound` only. The exporter sends the kernel's real trees; tampered ones compute to false |
| `search/`, `synth/`, `hw/` | No | GPU work: counterexample search over every short history, and invariant/rank synthesis. Every hit is replayed by the interpreter or proven by the kernel before it counts |
| `core/dsl.ts`, the runtimes | No | The builders compile to the kernel's plain values; the interpreter and generated JavaScript are held to the reference evaluator by the conformance test |

How the untrusted parts are held to the trusted ones, automatically:

- **Types**: the whole repo type-checks strictly (`noImplicitReturns`, `noFallthroughCasesInSwitch`,
  `noUncheckedIndexedAccess`), and a type-aware lint denies warnings; every switch over term and condition operations is
  exhaustive and ends in `unreachable()`, so a new operation fails to compile wherever it's missing.
- **Conformance** (`core/conformance.test.ts`): random terms over every operation through every consumer (interpreter,
  generated JS, the kernel on fixed values, the GPU search's u32 twin, the old symbolic prover) against the reference
  evaluator, and the same cases through Lean's own `evalE` (`lean-kernel/conformance.ts`).
- **Examples** (`examples/`): every law proven by the kernel and re-checked by Lean, every rule run at random through
  both runtimes, and every broken variant broken by a real run (a refused proof alone could be the prover's weakness).
- **Tampering and mutation** (`kernel/tamper.test.ts`, `kernel/refusals.test.ts`, `kernel/mutants.ts`): real proofs
  broken structurally or offered for weakened goals that have a model must be rejected, every refusal the kernel makes is
  exercised, and every one-operator mutation of `kernel.ts` and `check.ts` is run against the tests to find what they
  don't notice: 222 of 241 mutants are caught, and the 19 left are equivalent (`kernel/MUTANTS.md`).
- **Fuzz**: the kernel never accepts a refutation of something with a model (`kernel/kernel.test.ts`), and laws proven
  over histories hold on every run (`kernel/history.test.ts`).

## Writing laws

The builders (`core/dsl.ts`) hand out typed values for every name you declare; everything compiles to the plain machine
the kernel checks, so nothing in them is trusted.

```ts
import {bool, count, forall, maybe, nat, oneOf, proveSteps, relation, rule, yes} from './core/dsl.ts'

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
proveSteps(caps, [dayCap], [onlyUp, once]) // {proven: true, checked: true}

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
- **Loops** (`loop(...)`): state, `while`, `body`, a `rank` (or a tuple of ranks) that must drop each turn.
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
| `core/` | Machines, the interpreter and JS compiler, the linear solver and its checker, Houdini invariants, models, the first Lean export |
| `kernel/` | The trusted kernel and the untrusted prover, with soundness fuzz (`kernel.test.ts`, `history.test.ts`) |
| `lean/`, `lean-kernel/` | Lean: the derivation checker `Cert.lean`, and the kernel's twin with its exported trees |
| `search/`, `hw/`, `modal-gpu/` | Counterexample search on the GPU: a hand-written WGSL kernel, and the same through the Handwired fork's word stages |
| `synth/` | Invariants and ranks found on the GPU, proven by the kernel |
| `next/` | Guards synthesized from laws, relational laws (migrations, tenant isolation), a ReBAC audit |
| `sat/` | Bit-vector laws: bit-blasted, solved, LRAT-checked in TypeScript, optionally by Lean |
| `enum/`, `perf/` | The enumeration, and the benchmarks |
| `examples/` | The builders at work: `domains/` (92 rules across nine domains, each with laws and broken variants), `harness.ts` (the triple check), `readme.ts`, `budget.ts` |
| `compare/` | The same three rules in gdp-wired, Bend and plain Lean, checked and measured |
| `spec.ts`, `gdp.ts`, `circuit.ts`, `laws.ts` | The audit path: gdp-ts predicates written once, as trusted provers per request and as a Handwired circuit that decides every (user, project) pair at once |
| `modal/` | Everything above as Modal jobs: `suite.json` is the regression suite |
| `vendor/handwired` | [monotykamary/handwired](https://github.com/monotykamary/handwired), branch `u32-words`: Cheng Lou's Handwired with exact u32 word circuits and word stages in loop programs |
| `vendor/gdp-ts` | [rauchg/gdp-ts](https://github.com/rauchg/gdp-ts) |

## Running

Needs [Bun](https://bun.sh). Lean 4.34.0 for `lean/` and `lean-kernel/`; a WebGPU runtime (Chrome, or Dawn's node
bindings) for the GPU parts.

```sh
git clone --recursive https://github.com/monotykamary/gdp-wired && cd gdp-wired
bun examples/budget.ts
bun test core/compile.test.ts core/runtime.test.ts kernel/history.test.ts
cd kernel && bun run-kernel.ts && bun test kernel.test.ts
```

The whole suite (105 jobs, about 15 minutes of wall time) runs on [Modal](https://modal.com):

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
