// The lemma search's hypothesis at other values of the variables an induction leaves (core/data.ts's attempt): the
// drop of a zip of two lists, where the step needs the hypothesis at both tails; Peano induction on a natural no call of
// the law recurs on (twice x is even); an implication whose instances come from the values its premise holds at. Each
// proven and checked by the kernel; each broken variant refuted.
import {expect, test} from 'bun:test'
import {type Bool, type Nat, type Val, data, define, law, natural, proveData, self, when} from './data.ts'
import {checkCyclic} from '../kernel/cyclic.ts'

const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat, B = (v: unknown) => v as Bool
const Ns = data('Ns', {nil: {}, cons: {head: natural, tail: self}})
const Ps = data('Ps', {nil: {}, cons: {a: natural, b: natural, tail: self}})
const zip = define('zipNs', {xs: Ns, ys: Ns}, Ps, ({xs, ys}) => L(xs).match({nil: () => Ps.nil, cons: ({head, tail}) => L(ys).match({nil: () => Ps.nil, cons: ({head: h2, tail: t2}) => Ps.cons(head, h2, zip(tail, t2))})}))
const dropN = define('dropNs', {n: natural, xs: Ns}, Ns, ({n, xs}) => N(n).match({zero: () => L(xs), succ: ({pred}) => L(xs).match({nil: () => Ns.nil, cons: ({tail}) => L(dropN(pred, tail))})}))
const dropP = define('dropPs', {n: natural, xs: Ps}, Ps, ({n, xs}) => N(n).match({zero: () => L(xs), succ: ({pred}) => L(xs).match({nil: () => Ps.nil, cons: ({tail}) => L(dropP(pred, tail))})}))
const even = define('evenN', {n: natural}, natural, ({n}) => N(n).match({zero: () => 1, succ: ({pred}) => N(pred).match({zero: () => 0, succ: ({pred: p2}) => N(even(p2))})}))
const elem = define('elemNs', {x: natural, xs: Ns}, natural, ({x, xs}) => L(xs).match({nil: () => 0, cons: ({head, tail}) => when(N(head).eq(x), N(1), N(elem(x, tail)))}))
const subset = define('subsetNs', {xs: Ns, ys: Ns}, natural, ({xs, ys}) => L(xs).match({nil: () => 1, cons: ({head, tail}) => when(N(elem(head, ys)).eq(1), N(subset(tail, ys)), N(0))}))
const inter = define('interNs', {xs: Ns, ys: Ns}, Ns, ({xs, ys}) => L(xs).match({nil: () => Ns.nil, cons: ({head, tail}) => when(N(elem(head, ys)).eq(1), Ns.cons(head, inter(tail, ys)), L(inter(tail, ys)))}))

const proven = (l: ReturnType<typeof law>) => { const v = proveData(l, {ms: 20_000}); expect(v.proven && v.checked).toBe(true); expect(v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true) }
test('the hypothesis at both tails: drop n (zip xs ys) = zip (drop n xs) (drop n ys)', () => {
  proven(law('dropZip', {n: natural, xs: Ns, ys: Ns}, ({n, xs, ys}) => L(dropP(n, zip(xs, ys))).eq(zip(dropN(n, xs), dropN(n, ys)))))
  expect(proveData(law('dropZipBroken', {n: natural, xs: Ns, ys: Ns}, ({n, xs, ys}) => L(dropP(n, zip(xs, ys))).eq(zip(dropN(n, xs), ys)))).counterexample).toBeDefined()
}, 30_000)
test('Peano induction on a natural no call recurs on: x + x is even', () => {
  proven(law('evenTwice', {x: natural}, ({x}) => N(even(N(x).plus(x))).eq(1)))
  expect(proveData(law('evenTwiceBroken', {x: natural}, ({x}) => N(even(N(x).plus(x).plus(1))).eq(1))).counterexample).toBeDefined()
}, 30_000)
test('an implication read where its premise holds: xs ⊆ ys makes xs ∩ ys = xs', () => {
  proven(law('subsetInter', {xs: Ns, ys: Ns}, ({xs, ys}) => B(N(subset(xs, ys)).eq(1)).implies(L(inter(xs, ys)).eq(xs))))
  expect(proveData(law('subsetInterBroken', {xs: Ns, ys: Ns}, ({xs, ys}) => B(N(subset(ys, xs)).eq(1)).implies(L(inter(xs, ys)).eq(xs)))).counterexample).toBeDefined()
}, 30_000)
