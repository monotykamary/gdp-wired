# hw synthesis: synth/'s kernels on the Handwired u32-words fork

synth/'s three GPU kernels, written as Handwired loop programs of word stages (`../vendor/handwired`, branch
`u32-words`), run by Handwired's CPU loop runner and by its WGSL writer (loop-emit.ts) and program runner. They sit behind
synth/'s `Evaluator`, so its templates, Houdini rounds, `support` and kernel loop run unchanged on top.

| File | What |
| --- | --- |
| `synth.ts` | `compileKernel` (history, region, kill) and `hwEvaluator` (CPU: Handwired's loop runner; GPU: `createProgramRunner`). Candidates' coefficients (two's complement i32 bits) and alive bits are shared word tables; signed comparison flips the sign bit. history: document = 64 histories × a block of 24 candidates, positions walk (history, step), a history that ends moves on (`stop` after the last). region: document = 24 points, positions walk (point, alive candidate) through a next-alive table, stopping a point at its first broken candidate; the point's digits are registers (decoded once per document, then counted up), and every read is provably in range (`assumeAtMost` on the next-alive cells and the `j` register, one zero coefficient row for j = K), so none has a bounds check. kill: document = 64 points × a block of 8 candidates (invariants: from a shared list of region points; ranks: over the box, or over a once-built list of the points where the loop runs when the box has more than 2M points; a rank kill with points × candidates over 10^9 takes 24 a block). History and kill read their block's coefficients from registers a `once` stage fills, not from tables at every position |
| `check-synth.ts` | Every round's kill set against synth/compile.ts's JS twin, from the same alive sets, on the small boxes: `bun check-synth.ts` (Handwired's CPU runner), `--gpu` (Dawn) |
| `run-synth.ts` | synth/run.ts on these kernels; `--both` also runs synth/'s hand-written kernels on the same device and checks that every case ends the same way |
| `run_synth_gpu.py` | The same on Modal (`--gpu H100` or `L4`, app `hw-gpu-synth-words`, 15-minute timeout, cancelled with its client) |

Correctness: on the small boxes every round agrees with the JS twin, on the CPU loop runner and on the M2's GPU, for all
three invariant cases (history, then region + kill rounds to the fixpoint) and all three rank cases. On the full boxes
(`--both`, H100, L4 and M2), all 6 cases end the same way on both sets of kernels: the same survivors, the same strongest
set, the same kernel-proven invariant or rank.

Filter time (templates to survivors), Handwired kernels vs synth/'s hand-written ones on the same device. "Before" is the
first port; "after" is this round's (`runs/modal/hw/synth-{H100,L4}-final.json`; the v3–v5 runs beside them give the
spread: fresh containers move both columns by up to 2×, the L4 most):

| Case | H100 before | H100 after | L4 before | L4 after |
| --- | --- | --- | --- | --- |
| in-flight: s ≤ b + 150 | 4.9 s vs 7.5 s | 5.0–6.0 s vs 7.5–8.3 s | 12.1 s vs 16.7 s | 6.9–14.6 s vs 12.9–16.6 s |
| token bucket | 3.8 s vs 5.3 s | 3.3–4.2 s vs 5.2–5.8 s | 7.9 s vs 11.6 s | 4.9–9.8 s vs 9.3–11.5 s |
| leaky bucket | 6.7 s vs 8.3 s | 7.1–8.5 s vs 8.3–8.8 s | 14.0 s vs 19.5 s | 11.0–20.8 s vs 15.7–19.5 s |
| carry (rank) | 133 ms vs 69 ms | 44–61 ms vs 27–55 ms | 242 ms vs 53 ms | 40–74 ms vs 36–57 ms |
| gcd (rank) | 206 ms vs 41 ms | 74–86 ms vs 46–81 ms | 311 ms vs 81 ms | 91–163 ms vs 57–94 ms |
| race (rank) | 591 ms vs 425 ms | 488–625 ms vs 400–496 ms | 1.2 s vs 0.98 s | 1.17–1.23 s vs 0.98–1.05 s |

The invariant cases were already ahead (the history pass reads its block from registers). The rank cases were setup:
building the word circuits (the fork's `live` and `createWordStage` walked a load's whole table once per load; fixed in
src/handwired, now once per distinct table) and compiling shaders that unroll 24 candidates. A block of 8 compiles 2–3×
faster (`profile-setup.ts` measures build, WGSL and compile per kernel: build and WGSL are now a few ms; compile is
~20 ms plus ~3 ms per 1k characters on the M2), and region and kill runners are created together so their compiles
overlap. Race, where rounds dominate, gained from the guarded list. What's left on the rank cases is shader compile of
new shader text (the hand kernels loop over candidates, so their shaders are a few hundred lines).

## Rank pairs and map invariants (synth/compile-more.ts's kernels)

| File | What |
| --- | --- |
| `synth-more.ts` | `compileMoreKernel` (nonincreasing, rankPair, mapRegion, mapKill, and a `guards` pass) and `moreHwEvaluator`, with synth/more.ts's `moreEvaluator` arguments. mapRegion: document = 24 points walking the alive candidates through a next-alive table; a point is in the region when every alive candidate holds at k and at the swapped cell (M at the written key). Every kill runs over a list: map region points, or, for ranks, the points where the loop runs, from the `guards` pass (built once per evaluator). Without that list a straight-line word stage paid for its whole block of candidates at points the hand kernel returns from early: the pair round's GPU pass took 110 ms against the hand kernel's 53 |
| `check-synth-more.ts` | Every round against synth/compile-more.ts's JS twin on the small boxes: the nonincreasing round, the pair round (37,440, 17,400 and 37,440 pairs), and the map rounds from the start to the fixpoint (admit: 3.4M points). Agrees on Handwired's CPU loop runner and on the M2's GPU |
| `run-synth-more.ts` | synth/run-more.ts on these kernels (the single-rank pass on `synth.ts`'s); `--both` also runs the hand kernels on the same device and compares outcomes. Prints setup (building the word circuits and compiling the shaders) and rounds (the GPU work) separately |

`--both` on H100, L4 and M2: all 5 cases end the same way on both sets of kernels: the same survivors, the same pair
proven first ((n − i, m − j), (n − i, n − j), (R − r, w − t)), and the same map laws (the four caps of admit, plus
Acct[k] ≤ d, hr, dm; Score[k] ≤ top and top ≤ C). Filter time, Handwired vs hand, as setup + rounds; first the port as it
was (before), then after this round (`runs/modal/hw/synth-more-{H100,L4}-final.json`, v3 beside it):

| Case | H100 after | L4 after |
| --- | --- | --- |
| grid walk (pairs) | 181–207 ms (setup 148–167, rounds 29–32) vs 124–132 ms (setup 51–56, rounds 71–74) | 268–299 (207–231 + 56–62) vs 249–334 (77–151 + 170–179) |
| triangle (pairs) | 99–131 (84–111 + 13–18) vs 95–122 (52–58 + 37–69) | 167–199 (140–170 + 24–27) vs 165–176 (60–76 + 97–103) |
| rounds of w tries (pairs) | 68–95 (42–64 + 25–29) vs 93–248 (25–106 + 66–140) | 124–191 (72–134 + 50–55) vs 195–210 (32–43 + 161–165) |
| admit (maps, 113M points) | 202–248 (53–75 + 148–171) vs 211–286 (62–145 + 140–148) | 425–471 (92–104 + 331–365) vs 364–431 (81–84 + 282–345) |
| leaderboard (maps) | 54–84 (43–75 + 8–10) vs 84–289 (57–127 + 27–161) | 79–104 (57–79 + 20–24) vs 135–177 (70–94 + 65–82) |

Before:

| Case | H100 | L4 | M2 |
| --- | --- | --- | --- |
| grid walk (pairs) | 5,396 + 46 ms vs 55 + 63 ms | 9,240 + 143 vs 81 + 171 | 3,476 + 68 vs 9 + 107 |
| triangle (pairs) | 1,761 + 40 vs 42 + 33 | 3,136 + 90 vs 73 + 85 | 1,131 + 26 vs 5 + 36 |
| rounds of w tries (pairs) | 5,061 + 51 vs 30 + 63 | 8,673 + 144 vs 60 + 176 | 4,693 + 65 vs 11 + 79 |
| admit (maps, 113M points) | 221 + 238 vs 58 + 110 | 384 + 583 vs 85 + 329 | 36 + 454 vs 10 + 213 |
| leaderboard (maps) | 151 + 9 vs 46 + 29 | 254 + 22 vs 78 + 70 | 30 + 10 vs 9 + 16 |

Before this round the map rounds were about 2× slower and pair setup took seconds (the per-load table walks). The map
region was not the coefficient reads but the dispatches: sized for 64 positions a point, it ran ~17 dispatches a round,
each a sync, upload and readback, while a point stops within a candidate or two. Sized for ~2 positions a point (4.2M
documents a dispatch), with the point's digits in registers and no bounds checks, admit's region went from ~185 ms to
~85 ms a round on the M2, and its rounds now match the hand kernel's on the H100 (148–171 vs 140–148 ms). Tried and
dropped: a region over a once-built list of guarded points (20% of admit's box) — its 1M-entry list tables need ~22
dispatches a round, slower than the box; and the transposed region (a document = a block of candidates × points, no
loads in the loop), which gives up the early stop at a point's first broken candidate, where almost every point ends.
Pair setup is now shader compile only.

```sh
bun check-synth-more.ts && DAWN_MODULE=<webgpu>/index.js bun check-synth-more.ts --gpu
DAWN_MODULE=<webgpu>/index.js bun run-synth-more.ts --both
cd .. && modal run hw/run_synth_gpu.py --out ../runs/modal/hw/synth-more-h100.json --gpu H100 --script run-synth-more.ts --args "--both"
```

```sh
bun check-synth.ts && DAWN_MODULE=<webgpu>/index.js bun check-synth.ts --gpu
DAWN_MODULE=<webgpu>/index.js bun run-synth.ts --both
cd .. && modal run hw/run_synth_gpu.py --out ../runs/modal/hw/synth-h100.json --gpu H100 --args "--both"
```
