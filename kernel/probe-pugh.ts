import {add, k, le, nat, scale, solve, v} from '../core/solver.ts'
const X = v('x'), Y = v('y')
const t = (a: number, b: number) => add(scale(X, a), scale(Y, b))
// Pugh's example: real solutions, no integer ones.
const sys = [...le(k(27), t(11, 13)), ...le(t(11, 13), k(45)), ...le(k(-10), t(7, -9)), ...le(t(7, -9), k(4)), ...nat('x', 'y')]
console.log(solve(sys).kind)
import {grow} from './prove.ts'
import {check} from './kernel.ts'
import {atMost, less, plus, times, x as xv, n as nn, all} from '../core/machine.ts'
const T = (a: number, b: number) => plus(times(a, xv('x')), times(b, xv('y')))
// The same system as kernel hypotheses (−10 <= 7x − 9y becomes 9y <= 7x + 10 over naturals).
const goal = {name: 'pugh', hyps: [all(atMost(nn(27), T(11, 13)), atMost(T(11, 13), nn(45)), atMost(times(9, xv('y')), plus(times(7, xv('x')), nn(10))), atMost(times(7, xv('x')), plus(times(9, xv('y')), nn(4))))]}
const out = grow(goal)
console.log('tree' in out ? `refuted by splits: ${out.nodes} nodes, kernel ${check(goal, out.tree) ? 'accepts' : 'REJECTS'}` : out)
void less
