// The searches: a law that fails only deep in a history, the exact bound next to it, and a law with a product.
import {type Law, type Machine, all, atMost, bit, ite, less, min, minus, n, plus, prod, same, x} from '../core/machine.ts'
import {admit, capLaws} from '../core/models.ts'
import type {Space} from './compile.ts'

// The in-flight rule, scaled down: each request capped at 2, at most 3 in flight. The bound is b + 5
// (admitted while s < b, then three capped costs land); claiming b + 4 fails only after six requests.
export const inflight2: Machine = {
  name: 'in-flight, cap 2',
  params: ['b'], inputs: ['t', 'done'], state: {s: n(0), p: n(0)},
  step: {state: {
    s: ite(all(same(x('done'), n(1)), less(n(0), x('p'))), plus(x('s'), min(x('t'), n(2))), x('s')),
    p: ite(same(x('done'), n(1)), ite(less(n(0), x('p')), minus(x('p'), n(1)), x('p')), ite(all(less(x('s'), x('b')), less(x('p'), n(3))), plus(x('p'), n(1)), x('p'))),
  }},
  assume: bit('done'),
}
export const tooTight: Law = {name: 's <= b + 4', holds: atMost(x('s'), plus(x('b'), n(4)))}
export const exact: Law = {name: 's <= b + 5', holds: atMost(x('s'), plus(x('b'), n(5)))}

// A spend counter with the per-request cap forgotten, against s <= m × requests (a product).
export const uncapped: Machine = {name: 'counted spend, cap forgotten', params: ['m'], inputs: ['c'], state: {s: n(0), r: n(0)}, step: {state: {s: plus(x('s'), x('c')), r: plus(x('r'), n(1))}}}
export const perRequest: Law = {name: 's <= m × requests', holds: atMost(x('s'), prod(x('m'), x('r')))}

export const searches: {what: string, m: Machine, law: Law, space: Space}[] = [
  {what: 'admit, Day unguarded: day_cap', m: admit(['Acct', 'Hour', 'Dom']), law: capLaws[1]!, space: {depth: 5, bound: 1}},
  {what: 'in-flight cap 2: s <= b + 4', m: inflight2, law: tooTight, space: {depth: 8, bound: 2}},
  {what: 'in-flight cap 2: s <= b + 5', m: inflight2, law: exact, space: {depth: 8, bound: 2}},
  {what: 'uncapped: s <= m × requests', m: uncapped, law: perRequest, space: {depth: 6, bound: 7}},
]
void bit
