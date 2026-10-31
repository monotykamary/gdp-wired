# research

Everything around the library: the GPU searches and synthesis, the experiments that led to the kernel, and the
benchmarks. The npm package is built from `../core/`, `../kernel/` and `../lean-kernel/` and imports nothing here; the
regression suite (`../supercomputer/suite.json`) runs the parts below that it lists.

| Path | What |
| --- | --- |
| [`ROADMAP.md`](ROADMAP.md) | The reach past the protocols: what 10/10 should leave behind, distributed apps, and the domains not yet reached, in order |
| [`search/`](search/) | Counterexample search on the GPU: a hand-written WGSL kernel over every run of a bounded space, its u32 JavaScript twin, the CPU search |
| [`hw/`](hw/) | The same searches, and synthesis's kernels, compiled to the Handwired fork's word stages ([`README-synth.md`](hw/README-synth.md)) |
| [`modal-gpu/`](modal-gpu/) | The Handwired searches on Modal GPUs, through Dawn on NVIDIA's Vulkan driver |
| [`realworld/`](realworld/) | The real-world corpus: 51 items of open-source budget, quota, rate-limit, ledger, payment, auth, access, workflow, queue, breaker, flag, inventory and approval code as rules, 311 laws, scored with nothing stated; its suspected bugs, each with a repro |
| [`synth/`](synth/) | Invariants and ranks found on the GPU, proven by the kernel |
| [`next/`](next/) | Guards synthesized from laws, relational laws (migrations, tenant isolation), a ReBAC audit |
| [`sat/`](sat/) | Bit-vector laws: bit-blasted, solved, LRAT-checked in TypeScript, optionally by Lean |
| `enum/` | The predicate enumeration in Bend (`make.ts` writes `k<K>.bend` for K atoms; `run.ts`, `time.ts` time it), with the JavaScript counts in `js.jsonl` that `hw/` and `perf/` check against |
| `gpu/` | The access audit's circuit on WebGPU in headless Chrome (`bun research/gpu/run.ts`) |
| `perf/` | Benchmarks: the prover over every example (`prover-bench.ts`: totals, the slowest items and goals) and on families that double in size until it stops (`prover-stress.ts`), the step and argument limits (`probe-limits.ts`), per-key caps and windows at scale (`grant-scale.ts`, `window-scale.ts`), the enumeration through the Handwired fork against Bend's (`enum-ours.ts`, `bend-enum/`, `enum_gpu.py` on Modal) |
| `lean/` | The first Lean checker: `Cert.lean` (Farkas derivations, `Cert.sound`), and the files `../core/export-lean.ts` and `../core/compile-lean.ts` write |
| `audit/` | The first prototype, before the kernel: an access spec written once (`spec.ts`) as gdp-ts provers (`gdp.ts`), a Handwired circuit (`circuit.ts`) and a plain JavaScript loop (`js-audit.ts`), compared on generated orgs (`check.ts`); its laws decided over a small model (`laws.ts`, `intent.ts`) and by the solver (`run-predicates.ts`); sequence laws by enumeration and by Farkas certificates (`steps.ts`, `arith-laws.ts`, `certificate.ts`, its own `solver.ts`) |

Each entry point runs from its own folder, e.g. `cd research/audit && bun check.ts 200 200 20 5`.

The GPU runners `hw/run_gpu.py`, `hw/run_synth_gpu.py` and `modal-gpu/run_gpu.py` take `--backend auto|runpod|modal`
(`../supercomputer/README.md`): `python3 research/hw/run_gpu.py --backend auto --out ... --args=--hand` runs on a RunPod pod,
and on Modal (its `--gpu`) when RunPod has none of the GPU types in the list or the pod fails; where it ran is in
`<out>.backend.json`. The search `--hand` and synthesis's bucket cases (`--both --only bucket`) gave the same results,
times aside, on a RunPod RTX 4090 as on a Modal L4 (`runs/backends/gpu/`, `runs/modal/backends/gpu/`);
`run_synth_gpu.py --both` stops at its fourth case on both ("synthesis kernels read no maps", `research/hw/synth.ts`).
