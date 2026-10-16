// True nonlinear laws over naturals: which does the prover close? (and every false one must get a real counterexample)
import {type C, all, atMost, less, minus, n, not, plus, prod, same, times, x} from '../core/machine.ts'
import {type Goal, check} from './kernel.ts'
import {concretize, countLeaves, grow} from './prove.ts'
const P = prod, X = x
const laws: [string, C, C, boolean][] = [
  ['x <= y ⇒ x·z <= y·z', atMost(X('x'), X('y')), atMost(P(X('x'), X('z')), P(X('y'), X('z'))), true],
  ['x, y <= m ⇒ x·y <= m·m', all(atMost(X('x'), X('m')), atMost(X('y'), X('m'))), atMost(P(X('x'), X('y')), P(X('m'), X('m'))), true],
  ['x·y = y·x', all(), same(P(X('x'), X('y')), P(X('y'), X('x'))), true],
  ['(x+y)² >= 4xy', all(), atMost(times(4, P(X('x'), X('y'))), P(plus(X('x'), X('y')), plus(X('x'), X('y')))), true],
  ['x² + y² >= 2xy', all(), atMost(times(2, P(X('x'), X('y'))), plus(P(X('x'), X('x')), P(X('y'), X('y')))), true],
  ['x <= y ⇒ x³ <= y³', atMost(X('x'), X('y')), atMost(P(X('x'), P(X('x'), X('x'))), P(X('y'), P(X('y'), X('y')))), true],
  ['x <= y ⇒ x² <= y²', atMost(X('x'), X('y')), atMost(P(X('x'), X('x')), P(X('y'), X('y'))), true],
  ['x < y ⇒ x² < y²', less(X('x'), X('y')), less(P(X('x'), X('x')), P(X('y'), X('y'))), true],
  ['x² <= y² ⇒ x <= y', atMost(P(X('x'), X('x')), P(X('y'), X('y'))), atMost(X('x'), X('y')), true],
  ['p·q <= B, q >= 1 ⇒ p <= B', all(atMost(P(X('p'), X('q')), X('B')), atMost(n(1), X('q'))), atMost(X('p'), X('B')), true],
  ['x·y = 0 ⇒ x = 0 or y = 0', same(P(X('x'), X('y')), n(0)), {op: 'or', xs: [same(X('x'), n(0)), same(X('y'), n(0))]}, true],
  ['(a ∸ b)·c = a·c ∸ b·c', all(), same(P(minus(X('a'), X('b')), X('c')), minus(P(X('a'), X('c')), P(X('b'), X('c')))), true],
  ['x·y >= x (false at y = 0)', all(), atMost(X('x'), P(X('x'), X('y'))), false],
  ['x² <= 2x (false at x = 3)', all(), atMost(P(X('x'), X('x')), times(2, X('x'))), false],
]
for (const [what, hyp, concl, truth] of laws) {
  const goal: Goal = {name: what, hyps: [hyp, not(concl)]}
  const t0 = performance.now(), out = grow(goal), ms = Math.round(performance.now() - t0)
  const ok = 'tree' in out && check(goal, out.tree), real = ok ? undefined : concretize(goal)
  const verdict = ok ? `PROVEN   ${countLeaves((out as any).tree)} leaves` : real ? `REFUTED  ${JSON.stringify(real)}` : `OPEN     ${'stuck' in out ? out.stuck : 'kernel rejects'}`
  console.log(`  ${(truth ? '' : '') + what.padEnd(34)} ${verdict.padEnd(32)} ${truth === ok ? '' : truth ? '← true, not proven' : '← FALSE PROVEN'}  (${ms} ms)`)
}
