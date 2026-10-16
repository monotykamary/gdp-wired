# gdp-wired synth: invariants and ranks found on the GPU, proven by the kernel

A law that holds but isn't inductive needs an invariant nobody wrote; a loop that halts needs a rank nobody wrote.
Here the GPU guesses at scale and the kernel decides: thousands of linear candidates (Σ c·v ≤ d over the state and
params) are filtered on a box, and only the few that survive, and that the goal needs, go to `kernel/kernel.ts`.
Nothing before the kernel is trusted.

| File | What |
| --- | --- |
| `compile.ts` | The kernels, as WGSL for Handwired's runner and as JavaScript (the CPU twin). `history`: every request sequence from the start; a candidate a reachable state breaks dies. `region`: which box points satisfy every candidate alive (24 points a thread, a bit mask). `kill`: over the region's points, the candidates their step breaks (a block of 24 candidates a thread, a bit mask). Ranks: a candidate max(0, Σ c·v − d) dies where the loop runs but it doesn't drop |
| `synth.ts` | Templates (up to 3 terms, coefficients and constants per case), the GPU and CPU evaluators (dispatches sized by work, under the macOS GPU watchdog), Houdini rounds, `support` (the few survivors the goal needs: add the one ruling out the most counterexamples to induction until none is left), and the kernel loop (when the kernel gets stuck, its witness is a counterexample to induction: add the survivor that rules it out). `usedHyps` reads which laws a kernel tree's leaves use |
| `models.ts` | in-flight requests (needs s + 50p ≤ b + 150), a token bucket (needs tokens + spent − 3·ticks ≤ 10), a leaky bucket with its capacity a param (needs admitted ≤ level + 2·ticks); loops: carry (rank 4a + b), gcd (a + b), race (n + y − x + 1) |
| `run.ts` | End to end: `--gpu` (Dawn's navigator.gpu: Metal on a Mac, Vulkan on Linux) or `--cpu` (the JS twin), `--small` boxes, `--only` |
| `run_gpu.py` | The same on a Modal GPU (L4 or H100), app `hw-gpu-synth`, 15-minute timeout, cancelled if the client stops; `--script run-more.ts` for the cases below |
| `compile-more.ts` | More kernels, beside compile.ts's (unchanged): `nonincreasing` (ranks that never go up), `rankPair` (pairs compared in order), and for machines with maps `mapRegion` / `mapKill`. A map machine's box point tracks two cells per map, M at an arbitrary key k and M at the key the step writes, equal when the keys are; reads must be at the written key or at k; a candidate about a map must hold at both cells to be in the region, and dies when the step breaks it at k |
| `more.ts`, `models-more.ts`, `run-more.ts` | Rank pairs: first the ranks that never go up (one round), then every such r1 with every r2 (one round), the kernel's `loopObligations(l, laws, [r1, r2])` simplest first. Map invariants: templates about one map's cell at k (plus a scalar or param), the start (every cell holds the map's initial value), Houdini over tracked cells, then the kernel proves the strongest survivors as laws for every k, dropping any it can't |

Every case ends in a kernel proof (H100 run, `runs/modal/synth/h100-v2.json`):

| Case | Candidates | GPU work | Survive (needed) | Found | H100 | L4 | M2 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| in-flight: s ≤ b + 150 | 6,953 | 16.8M histories of 3, 16.8M points × 4 rounds | 1,041 (1) | s + 50p − b ≤ 150 | 8.0 s | 16.3 s | 42.2 s |
| token bucket: spent ≤ 10 + 3·ticks | 3,133 | 16.8M histories of 6, 2.1M points × 26 rounds | 78 (1) | tokens + spent − 3·ticks ≤ 10 | 5.7 s | 11.5 s | 41.7 s |
| leaky bucket: admitted ≤ B + 2·ticks | 5,131 | 8.4M histories of 20, 33.6M points × 5 rounds | 532 (1) | admitted − level − 2·ticks ≤ 0 | 8.9 s | 19.6 s | 183 s |
| carry halts | 1,215 ranks | 4,096 points | 10 | max(0, 4a + b) | 43 ms | 53 ms | 38 ms |
| gcd halts (A, B ≥ 1) | 395 ranks | 1M points | 35 | max(0, a + b) | 53 ms | 92 ms | 123 ms |
| race halts | 1,407 ranks | 4.2M points | 18 | max(0, n + y − x + 1) | 466 ms | 1.0 s | 1.2 s |

The kernel's part is 1–70 ms in every row. For comparison, `core/invariant.ts` (Houdini on the CPU with the symbolic
prover) takes 13.7 s for its 112 in-flight candidates, and its rank templates (`kernel/run-more.ts`) can't express
4a + b or n + y − x + 1. The first version of this folder, one killed candidate per thread per round, took 426 s for
the leaky bucket on the H100; bit masks per block of candidates, and the region pass before the kill pass, made it 8.9 s.

```sh
DAWN_MODULE=<webgpu>/index.js bun run.ts --gpu        # the Mac's GPU
bun run.ts --cpu --small                               # the JS twin
cd .. && modal run synth/run_gpu.py --out ../runs/modal/synth/h100.json --gpu H100
DAWN_MODULE=<webgpu>/index.js bun run-more.ts --gpu   # rank pairs and map invariants (--cpu --small: the JS twin)
cd .. && modal run synth/run_gpu.py --out ../runs/modal/synth/more-h100.json --gpu H100 --script run-more.ts
```

Rank pairs and map invariants (`run-more.ts`; H100 / L4 / M2 filter times, all from `runs/modal/synth/more-*.json` and
`runs/synth-more-m2.json`). No single linear rank survives any of the three loops; the pair is the first the kernel tries:

| Case | GPU work | Survive | Found (kernel) | H100 | L4 | M2 |
| --- | --- | --- | --- | --- | --- | --- |
| grid walk, inner bound m a param | 117 non-increasing → 37,440 pairs × 16,384 points | 49 pairs | (n − i, m − j), 6 leaves | 131 ms | 186 ms | 154 ms |
| triangle, inner bound i | 87 → 17,400 pairs × 16,384 points | 112 | (n − i, n − j), 7 leaves | 89 ms | 111 ms | 86 ms |
| rounds of w tries within R | 117 → 37,440 pairs × 16,384 points | 49 | (R − r, w − t), 6 leaves | 80 ms | 130 ms | 83 ms |
| caps rule, caps never written down | 84 candidates, 113M points × 2 rounds | 35 (16 strongest) | Acct[k] ≤ 1, Day[k] ≤ d, Hour[k] ≤ hr, Dom[k] ≤ dm, and Acct[k] ≤ d, hr, dm (a grant needs every cap open); the four caps of `core/models.ts` follow; 84 leaves | 271 ms | 246 ms | 305 ms |
| leaderboard: Score[u] += inc up to C, top = max | 80 candidates, 512k points × 1 round | 18 (6 strongest) | Score[k] ≤ top, top ≤ C (and weaker forms), 46 leaves | 91 ms | 212 ms | 65 ms |

The kernel's part for admit is 2.5–8 s: 9 survivors the box let through (its keys are 0..1) aren't inductive, and each
is dropped after a stuck proof of the whole set. The triangle's pair (n − i, n − j) works because its inner loop resets j
to 0 and j ≤ i < n inside the loop.

Limits: linear candidates; map candidates mention one map (at k) plus scalars and params, and the step may read a map
only at the key it writes; pairs, not longer tuples; and the box is a filter only: a survivor it lets through that isn't inductive is caught by the
kernel and dropped.
