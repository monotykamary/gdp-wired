// Two of the failure classes the termination benchmarks show, reproduced on loops written by hand in the library's own
// language (`bun compare/term/probes.ts`; on Modal through supercomputer/run.py with compare/term/probes.json):
//   - params the loop never reads: while i <= 100 and X >= 1, i := i + 1, beside k params nothing reads. The rank is
//     101 − i; with enough idle params the runs' LP fits one reading them, which the kernel refuses
//   - a reset to any value: while x > 0 and y > 0, either x := x − 1, or x := any v >= 1 and y := y − 1 (the inner loop
//     of an iterative Ackermann, AckR.jar-obl-8 in TPDB-ARI). The rank is (y, x) in order. Here the search finds it
//     (runs/modal/term/probes1): what stops AckR's translation is elsewhere (its runs fit the linear x + 2·y, which
//     the kernel refuses, and no tuple is tried after a linear fit the kernel refused)
import {loop, nat, proveLoop, when} from '../../core/dsl.ts'

for (const k of [0, 1, 2, 3, 4, 6, 8]) {
  const ps: Record<string, typeof nat> = {I: nat, X: nat}
  for (let j = 0; j < k; j++) ps[`P${j}`] = nat
  const l = loop(`up to 101, ${k} idle params`).params(ps as {I: typeof nat, X: typeof nat}).state({i: ({I}) => I})
    .while(({i, X}) => i.atMost(100).and(X.atLeast(1))).body(({i}) => ({i: i.plus(1)}))
  const t = performance.now(), v = proveLoop(l, [])
  console.log(JSON.stringify({probe: 'idle params', params: k, proven: v.proven && v.checked, rank: v.found?.rank, ms: Math.round(performance.now() - t)}))
}
const reset = loop('a reset to any value').params({X: nat, Y: nat}).inputs({c: nat, v: nat}).state({x: ({X}) => X, y: ({Y}) => Y})
  .assume(({c, v}) => c.atMost(1).and(v.atLeast(1)))
  .while(({x, y}) => x.gt(0).and(y.gt(0)))
  .body(({x, y, c, v}) => ({x: when(c.eq(0), x.minus(1), v), y: when(c.eq(0), y, y.minus(1))}))
{
  const t = performance.now(), v = proveLoop(reset, [])
  console.log(JSON.stringify({probe: 'reset', proven: v.proven && v.checked, rank: v.found?.rank, why: v.why, ms: Math.round(performance.now() - t)}))
  const stated = proveLoop(reset.rank(({x, y}) => [y, x]), [])
  console.log(JSON.stringify({probe: 'reset, rank (y, x) stated', proven: stated.proven && stated.checked}))
}
