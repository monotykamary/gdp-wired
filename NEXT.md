# gen/chc-speed: checkpoint (2026-10-28)

## Done (committed on gen/chc-speed, from 3cdf37e)
- dc1e9b7 `perf(simp)`: core/nonterm.ts's simpC walks an and's (or's) nested parts in place, each part once. It used
  to copy each nested and of a chain anew (n² copies) and read a part shared along a DAG once per path to it, and IMC's
  interpolants are binary and-s and or-s over the refutation DAG. On metros_4_e1_917 (IMC alone, local), simpC's `and`
  was 32.6% of a 20 s profile. After the change the query sequence is identical (316 of 316 queries, same node counts)
  and the run gets 2 depths further in 20 s. Interpolant time at depth 20 fell from about 1.7 s to 0.15 s per depth.
- 4f7d7e6 `feat(bmc)`: boundedSearch's `clausal` option, so the unrolling's CDCL session runs in the clausal mode,
  falling back to the kernel's reading on `UNREAD` (exported from kernel/cdcl.ts). On metros_4 (local, bounded runs
  alone) the run reached depth 35 and found the cex in 25 s; the kernel reading stopped at depth 10 in 20 s.
- cf8b84d `feat(chc)`: solve.ts defaults `--bmc-depth 64 --imc-x 2`, so the bounded runs' k-step goals run on CPU 2
  and IMC's turn is twice theirs. compare/chc/README.md is updated.

## Quick bars (662-task CHC dev set, against 3cdf37e's shared baseline: 517, 518, 517; runs/bar/runs/chcspeed-*)
| run | commit | solved | notes |
| --- | --- | --- | --- |
| q1-simp | dc1e9b7 | 518 (+0.67) | gained 1, lost 2, all at the limit |
| q2-bmcx2 | e39794f (= cf8b84d's defaults) | 520 (+2.67) | metros_3_e3_1275_e1_1350 gained in every run (unsat at about 39 s); lost 2 at the limit |
| q2-bmcx4 | be8257a (IMC 4x) | 515 (-2.33) | metros_3 3/4; the 3 lost were flips at the limit |
| q3-bmcx1 | 90871af (equal turns) | 518 (+0.67) | unsat +4.33 (metros_3 at about 24 s; metros_4_e2_968_e4_801 3/4), sat -3.67 |

Wrong was 0 in every run. Read: the bounded runs' share trades unsat gains (metros) against IMC's late sat answers.
On the dev set the net effect is within noise (±3). At a third of CPU 2 on Modal, the bounded runs reach depths 25 to
32 on the metros tasks; their counterexamples need depths 34 to 35.

## In flight: nothing (stopped for the checkpoint)
- The full bar `chcspeed-full` (cf8b84d against 3cdf37e) was stopped by its PID about 13 min in, and modal/reap.sh
  ran. No group had finished. The 3cdf37e shared baseline: chc has 3 runs (kept), and f1 has 3 runs. f2 run2 and
  suite run2 were killed and not kept. Another track (pid 70931) was building rw's baseline.
- `modal app list`: 0 live apps.

## Next
1. Rerun the claim: `bun bar --cand cf8b84d --base 3cdf37e --backend modal --name chcspeed-full`. It reuses whatever
   baseline runs are `.done`.
2. If CHC moves, run 4 side-by-side batches from this worktree: `modal run compare/chc/modal_chc.py --out
   <main>/runs/chcspeed/settle-rN --tools gdp,z3,golem` (about 485 s wall each, as runs/settle/r1..r4).
3. If the full bar shows the sat losses outweigh the metros gains, fall back to dc1e9b7's defaults (`--bmc-depth 0
   --imc-x 1`) and keep the clausal BMC option for later.
4. Write the CHANGELOG `## Unreleased` entry, and the report's size, reuse and spend sections. The size is 2,389,414
   bytes against 2,387,735 (+1,679, +28 lines). Spend so far: q1 $4.65 estimated, including 3 CHC baseline runs; each
   of q2, q2 and q3 about $1 to $1.5 (`bun gates/bar.ts spend <run dir>`).

## Tried and dropped (measured locally on metros_4, DRAGON_12, car_5)
- A simplex rebuild against the peak row count: fewer pivots, a slower search.
- Cleaning the tableau's free basic slack rows: no rebuild avoided.
- Seeding a rebuilt tableau from the old point: no fewer pivots.
- `GDP_CDCL_BASE`/`FILL` higher: fewer rebuilds, a different and slower search.
- Bound propagation over every open atom in the clausal mode: depth 21 against 23.
- DAG interpolants kept across IMC queries: an identical search with no measurable gain.
- IMC depth growing faster than k+1: worse.
- TPA on the clausal DAG: stuck at level 1. Its midpoints are full points with no generalization, so a fix needs MBP.
- Stuttered bounded runs with growing depth steps: not a win.

Local timings were noisy: the load average was 13 with other tracks running.
