# gdp-wired hw: the search through the Handwired fork

The counterexample search compiled to a Handwired loop program instead of a hand-written shader. It uses the
`u32-words` fork of Handwired (`../vendor/handwired`, branch `u32-words`; `docs/words.md` there): a stage made of exact
u32 word operations, a binding for the document's index and the loop's position, and a `stop` write that ends a loop
early. Handwired's own loop runner runs it on the CPU, and its WGSL writer (`loop-emit.ts`) and program runner
(`createProgramRunner`) run it on a GPU. Nothing here is trusted: every counterexample is replayed by the interpreter.

| File | What |
| --- | --- |
| `compile.ts` | A machine and a law as one looped word stage. A document covers `chunk` candidates (params, then each step's request, as digits); registers carry the step, the candidate, its digits, params, state, map cells and the least failure so far; a candidate that fails, sends a disallowed request or passes its last step hands over to the next at once, and `stop` ends the loop after the document's last candidate. Spaces past 2^32 candidates run in slices: the later steps' requests come from a shared word |
| `check-cpu.ts` | Handwired's CPU loop runner (`executor` and `generated`) against search/'s per-candidate answers, on sampled documents of every search |
| `run.ts` | The suite on a GPU through Dawn (Metal on a Mac, Vulkan on Linux); `--hand` also runs search/compile.ts's hand-written shader on the same device; `--big`, `--huge` for depths 10–12; `--low n` forces slices, to test them on a small space |
| `run_gpu.py` | The same on a Modal GPU (H100, L4), app `hw-gpu-words`, 15-minute timeout, cancelled if the client stops |

| `step-searches.ts` | Step-law and k-step-law searches: the examples' own laws and broken variants (release lifecycle, auction) and the composition examples (the countdown refinement, the interleaved counters), each with whether a run must break it |
| `check-steps.ts` | Those searches on Handwired's CPU runner against `../core/watch.ts` reading every candidate's run on the interpreter (no code shared with the compiled program), whole spaces; then a fuzz of random machines and random 1-, 2- and 3-step laws where Handwired, the watcher and the kernel must agree: a law the kernel proves has no breaking run |

**Laws over steps.** A `Law` and a `StepLaw` are each one description read three ways: the kernel proves it about every
run (`kernel.ts`), `core/watch.ts` reads it on one run (the examples' random runs, every replay), and `compile.ts` searches
for a run that breaks it. For a step law over k steps, registers hold the last k − 1 steps' frames (state, cells and
request), shifted on each step; each step's `when` is read at its frame and `then` across the window, after every step
that completes k in a row. `check-steps.ts`: every document of the 11 searches agrees with the replay, and the fuzz agrees
on 2,760 of 2,760 documents (87,480 runs; 12 kernel-proven laws unbroken, 12 broken). On an L4 (`run.ts --steps --chunk
256`, medians of 9), each three steps deeper than its CPU check, every counterexample replayed:

| Search | Runs | L4 | Found |
| --- | --- | --- | --- |
| release, skips staging: two steps from built never retire (depth 8) | 65,536 | 0.24 ms | after 2 steps: promote, retire |
| release: two steps from built never retire; the step after a rollback never retires (depth 9) | 262,144 each | 0.25 ms | nothing |
| auction, reserve only: the high bid never falls (depth 6) | 268M | 36.4 ms | after 2 steps: a lower bid taken |
| auction: two refused bids change nothing (depth 6) | 268M | 13.7 ms | nothing |
| countdown, no clamp: the meter allows what it is sent (depth 6) | 65,536 | 0.16 ms | after 1 step: a spend over `most` |
| countdown, strict: left + used = cap (depth 6) | 65,536 | 0.19 ms | after 1 step |
| interleaved counters: two turns of anyone leave b's count (depth 6) | 1.6M | 0.36 ms | after 2 steps: b moves |
| interleaved counters: two a turns leave b's count; a.n <= cap (depth 6) | 1.6M each | 0.19 ms | nothing |

**Histories.** A machine with a log steps as kernel.ts's plain machine (sums as state); a candidate's digits are only
the requests' carried inputs. Registers hold the log (each step's recorded inputs and whether it was kept), each query
is its term summed over the records kept earlier in the candidate and not yet spent (pruning drops a record whose order
plus `after` is at most the request's), and a request whose order goes back ends the candidate, as the runtimes refuse
it. `check-steps.ts` runs every example rule with a log (30 variants across nine domains, pruned ones too) against the
replay; on an L4 (`run.ts --history`), each law over the deepest space within 2^28 runs takes 0.4–28 ms (43M runs in
3–10 ms), every broken variant's counterexample replays (pruning a tick early, a window a minute short, forgetting the
request), and no proven rule has one.

**Sets.** A map a request carries is K cells of the candidate's digits (keys past them read the map's default), a
map kept by the machine K registers plus its default, a flag over every key a conjunction over the K cells and the
default, and a write at every key a write to each. On an L4 (`run.ts --sets`), each law of the derived authority
(`../examples/sets.ts`) over every run of depth 3 with three names (68.7B runs, 4,096 slices) takes 1.7–2.8 s and finds
nothing; both broken variants are found (checking only the named grant at depth 2, keeping the child on a refused
derivation at depth 3), and both counterexamples replay.

Results. Every answer agrees with the hand-written shader, and every counterexample replays. Medians of 9 runs after a
warm-up (`--reps 9`), Handwired / hand-written on the same device; past 2^32 the hand times are modal-gpu/'s:

| Search | Histories | M2 | H100 | L4 |
| --- | --- | --- | --- | --- |
| admit, Day unguarded (depth 5, candidates die in 1–2 steps) | 268M | **116 / 151 ms** | 36.3 / 16.9 ms | 50.1 / 25.7 ms |
| in-flight b+4 (depth-6 counterexample) | 129M | **27 / 33 ms** | 4.4 / 2.7 ms | 6.7 / 4.6 ms |
| in-flight b+5 | 129M | **27 / 36 ms** | 4.3 / 2.5 ms | 6.7 / 4.2 ms |
| uncapped | 2.1M | 0.64 / 0.31 ms | 0.33 / 0.20 ms | 0.35 / 0.21 ms |
| in-flight b+5, depth 9 | 1.16B | **225 / 308 ms** | **17.9–20.2 / 20.3–21.6 ms** | **36.6 / 38.5 ms** |
| depth 10 (9 slices) | 10.5B | — | **171 ms** (hand ~200) | 376 ms |
| depth 11 (81 slices) | 94.1B | — | **1.58 s** (hand 1.80) | 4.23 s |
| bound 3, depth 8 (16 slices) | 17.2B | — | **222 ms** (hand 230) | 486 ms |
| depth 12 (729 slices) | 847B | — | **13.3 s** (hand 16.1) | — |

What got it there, in order: the fork's `stop` (a candidate that dies hands over at once: 2× on in-flight); 256
candidates per document; the fork's constant folding and identities (x + 0, x & 1 on a bit, select on a constant,
comparisons a maximum decides) and plain `/`, `%` by a nonzero literal; the fork's literal loop bound (Metal treats a
`let` bound as unknown); a `once` stage for the document's first candidate and count; the best failure as 0xffffffff
for none; the start law checked on the constant initial state (it mostly folds away); declared register maxima. The
in-flight loop went from 85 statements per position to 51.

Where Handwired is still slower: searches whose candidates die within a step or two, on NVIDIA (admit 2.2×, in-flight
depth 6 1.6×). A word stage has no branches, so every position evaluates both the start of a new candidate and a step;
a deep search amortizes the start, a shallow one pays it on most positions. On the M2 the same programs are faster than
the hand-written shader. Closing the gap on NVIDIA would need the WGSL writer to emit branches, which divergent warps
would partly undo.

```sh
bun check-cpu.ts
DAWN_MODULE=<webgpu>/index.js bun run.ts --hand
cd .. && modal run hw/run_gpu.py --out ../runs/modal/hw/h100.json --gpu H100 --args "--hand --big --chunk 256"
```

## The ReBAC audit and the predicate enumeration

The two other hand-written u32 shaders, next/rebac/page.ts and enum/kernel-page.ts, as Handwired word-stage programs.

| File | What |
| --- | --- |
| `rebac.ts` | A document is a user; its cells in Handwired's document store are its groups as two 16-bit halves and its two direct grants as object + 1, whole numbers an f32 cell holds exactly. Stage `closure` (once): the groups closed under nesting, as one round over a shared table of each group's closure (model.ts's closure is 5 rounds of R(G) = G ∪ ⋃ sub[g], and R distributes over union, so R⁵(G) = ⋃_{g∈G} R⁵({g}) exactly), the grants' Euler intervals (`load`), Finance membership. Stage `objects` (one position per object): one table read gives an object's Euler time and, in its top bit, whether it lies under /finance; a second its inherited groups. Optional `pack` stage: violations << 12 \| viewable in one output word |
| `enum.ts` | Generated from the laws, not hand-written: the laws are formulas over atoms per index (`laws(k)`: reachable, the policy's clauses, the proposal), and `lanes` compiles a family over an index set to word operations (a[i+c] is w >> c, the index set a mask, any/none a compare with 0). A document is a block of 2,048 worlds w = document << 11 \| position; two counters in registers, optionally packed |
| `check-more.ts` | Handwired's CPU loop runner: `lanes` against the laws evaluated atom by atom (84,000 random worlds, k = 11..31), the counts at k = 16 and 20 against brute force and js.jsonl, and ReBAC against fast.ts on 3,000 users (with and without the stray grant, packed and not) |
| `run-more.ts` | Both on a GPU through Dawn, against fast.ts and js.jsonl, and with `--hand` against the hand-written shaders (copied verbatim) on the same device; `run_gpu.py --script run-more.ts` on Modal |
| `probe-more.ts`, `probe-rebac.ts` | How the gaps were found: text variants of the emitted WGSL, timed on the M2 |

Every count agrees with fast.ts / js.jsonl and with the hand-written shader, at every size. Median of 9 back-to-back
runs including readback, packed outputs (one word per document, as the hand-written shaders' one f32); Handwired / hand
on the same device in the same run:

| Case | M2 | H100 | L4 |
| --- | --- | --- | --- |
| ReBAC, 10k users × 2,048 objects | 1.05 / 1.36 ms | 0.14 / 0.33 ms | 0.22 / 0.38 ms |
| ReBAC, 100k users | 3.55 / 3.15 ms | 0.31 / 0.40 ms | 0.77 / 0.94 ms |
| ReBAC, 1M users (2.05B user × object pairs; JS 6.5 s) | 22.5 / 28.7 ms | 10.3 / 12.0 ms | 6.68 / 6.62 ms |
| enumeration, k = 28 (268M worlds) | 3.62 / 3.54 ms | 0.40 / 0.33 ms | 0.72 / 0.89 ms |
| enumeration, k = 30 | 13.9 / 13.6 ms | 1.37 / 1.20 ms | 2.49 / 3.06 ms |
| enumeration, k = 31 (2.1B worlds) | 27.2 / 27.6 ms | 2.68 / 2.45 ms | 4.91 / 6.01 ms |

Before (same table, earlier runs): ReBAC 1M 38.8 / 29.1 ms on an idle M2 and 14.1 / 7.4 ms on an H100; enumeration
k = 31 41.2 / 26.8 ms on the idle M2 and 6.1 / 4.3 ms on an H100. What closed the gaps:
- **The loop bound.** loop-emit.ts wrote `let positions: u32 = 2048u` and looped to `positions`; Metal's compiler treats
  a `let` bound as unknown. Writing the fixed count into the loop header (a fork change, see the fork's loop-emit.ts)
  took the enumeration from 39.5 to 27.4 ms on the M2, level with the hand-written shader.
- **A table read per object.** ReBAC read three tables per object; the hand-written shader reads the third (under
  /finance) only for objects the user sees. Without branches the same saving comes from the data: the bit rides on top
  of the Euler time, so one read gives both (40.5 → 22.6 ms on the M2).
- **Bounds checks.** With the position declared at most 2,047 (`assumeAtMost`) and the grant index as plus ∸ 1 (the
  fork's range inference now takes ∸, ÷ and >> by a constant into account), no `load` keeps a bounds check. On its own
  this didn't move the timings; the loads were never the bottleneck.

H100 containers vary between runs (the hand-written enumeration took 4.3 ms on one, 2.45 ms on this one), so compare
the two columns of one run, not across runs. The fixed per-evaluation cost (H100 enumeration at k = 20: 0.28 / 0.09
ms) is Handwired's program runner against the kernel runner, and only shows on the smallest cases.

```sh
bun check-more.ts
DAWN_MODULE=<webgpu>/index.js bun run-more.ts --hand
cd .. && modal run hw/run_gpu.py --out ../runs/modal/hw/more-h100.json --gpu H100 --script run-more.ts --args "--hand"
```
