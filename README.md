<img src="https://raw.githubusercontent.com/monotykamary/gdp-wired/main/static/banner-ink.svg" alt="gdp-wired" width="100%" />

# gdp-wired

Laws about stateful rules (budgets, caps, rate limits, access policies), proven in TypeScript by a small trusted
kernel, with an untrusted prover that writes the proofs, an optional Lean twin that checks the kernel itself, and GPU
searches that find counterexamples or the invariants a proof needs.

You write the rule once, as a step machine, and state what must always hold. The library proves it by induction (or
shows a real run that breaks it), and the same machine runs as an interpreter or ships as generated JavaScript.

```ts
import {type Law, type Machine, atMost, ite, less, min, n, plus, x} from './core/machine.ts'
import {proveLaws} from './kernel/prove.ts'

// A request of cost c is admitted while spend s is under budget b; each request is capped at m.
const budget: Machine = {
  name: 'budget', params: ['b', 'm'], inputs: ['c'], state: {s: n(0)},
  step: {state: {s: ite(less(x('s'), x('b')), plus(x('s'), min(x('c'), x('m'))), x('s'))}},
}
const boundedLoss: Law = {name: 'spend stays within b + m', holds: atMost(x('s'), plus(x('b'), x('m')))}

proveLaws(budget, [boundedLoss]) // {proven: true, checked: true, leaves: 4, ...}
```

Forget the cap (`plus(x('s'), x('c'))`) and the step goal has a model; `search` turns it into a run from the start:
`{params: {b: 1, m: 0}, trace: [{c: 2}]}`. `bun examples/budget.ts` runs all of it, including the generated
JavaScript.

## What's trusted

| Part | Trusted? | What it does |
| --- | --- | --- |
| `kernel/kernel.ts`, `core/check.ts` | **Yes** | Turns a machine and its laws into goals (the induction rules: step machines with maps and flags, loops with ranks, progress, folds over trees, histories) and checks a proof tree for each: splits on linear atoms, a Fourier–Motzkin derivation at each leaf. Refuses names a machine doesn't declare |
| `kernel/prove.ts` | No | Grows the trees. If it's wrong, the kernel rejects the tree |
| `lean-kernel/` | Optional | The kernel's twin in Lean 4.34.0, each rule proven sound (`Kern.sound`, `machine_sound`, `mmachine_sound`, `fmmachine_sound`, `loop_sound`, `fold_sound`, `progress_sound`, `hmachine_sound`), axioms `propext`, `Classical.choice`, `Quot.sound` only. The exporter sends the kernel's real trees; tampered ones compute to false |
| `search/`, `synth/`, `hw/` | No | GPU work: counterexample search over every short history, and invariant/rank synthesis. Every hit is replayed by the interpreter or proven by the kernel before it counts |

## Writing laws

- **Machines** (`core/machine.ts`): params, inputs, state, maps (naturals indexed by naturals), flags (conditions
  decided once per step), `pre` (about params alone) and `assume` (about each request). Arithmetic is over the
  naturals: `+`, `∸` (truncated), `×` by a constant, `min`, `max`, `if`, map reads; products of two terms for the
  kernel's nonlinear leaves.
- **Laws**: a condition on state and params; `forall` makes a map law hold at every key.
- **Histories**: a machine may keep a log of requests. A *sum* is state equal to Σ over the log of a term of the record;
  a *query* is an input equal to Σ over the log before the request (what code reads from a database at the request's
  time); a *relation* between them is proven one record at a time and then assumed. `prune` lets the runtimes drop
  records the kernel proves can't count any more. See `core/models.ts`'s `windowLimit`, a sliding-window limit whose
  ceiling is proven at every window end.
- **Running it**: `interpret(m)` is persistent (searches branch from any state); `compileJs(m)` is what an app ships:
  maps and the log updated in place, so a step costs the same however long the history. Both refuse params and inputs
  that aren't naturals below 2^53 and any value past 2^53 − 1, where the proofs over the naturals stop describing the
  run. The GPU searches refuse a space whose values could pass 2^32 − 1.

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

The whole suite (74 jobs, about 15 minutes of wall time) runs on [Modal](https://modal.com):

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
