// The existential track's items: laws that hold because some value exists, a parity or a multiple nobody stated
// (core/exists.ts), with that existential taken out; inferLaws finds it as a congruence, ∃k. v = c·k + r, proven through
// a ghost witness the kernel's counterexamples choose. The broken variant breaks the parity: refused.
import {type Item} from './corpus.ts'
import {exists, int, oneOf, proveRule, rule, when} from '../../core/dsl.ts'
import {inferLaws} from '../../core/infer.ts'

// A counter that steps by two (and back, from 2 up), from 0: it is never 7, since it is even (∃k. x = 2k).
const stairs = (bug?: 'a step of 3') => {
  const r = rule(`stairs${bug ? ' (with a step of 3)' : ''}`).inputs({go: oneOf('up', 'down', 'skip', 'stay')}).state({x: 0})
    .step(({go, x}) => ({x: when(go.is('up'), x.plus(2), when(go.is('down').and(x.atLeast(2)), x.minus(2), when(go.is('skip'), x.plus(bug ? 3 : 4), x)))}))
  return {r, laws: [r.law('the counter is never 7', ({x}) => x.ne(7))]}
}
// A ledger whose transfers are whole multiples of 5 (an existential the request brings): the balance is never 3, since
// it is always 5j for an integer j.
const fives = () => {
  const r = rule('ledger of fives').inputs({amount: int}).ints({balance: 0})
    .assume(({amount}) => exists(int, k => amount.eq(k.times(5))))
    .step(({amount, balance}) => ({balance: balance.plus(amount)}))
  return {r, laws: [r.law('the balance is never 3', ({balance}) => balance.ne(3))]}
}
export const existsItems: Item[] = [
  {id: 'exists/stairs', track: 'exists', removed: 'the counter is even (∃k. x = 2k)', today: () => { const {r, laws} = stairs(); return proveRule(r, laws, {search: false}) }, frontier: () => { const {r, laws} = stairs(); return inferLaws(r, laws) }},
  {id: 'exists/ledger of fives', track: 'exists', removed: 'the balance is a multiple of 5 (∃j. balance = 5j)', today: () => { const {r, laws} = fives(); return proveRule(r, laws, {search: false}) }, frontier: () => { const {r, laws} = fives(); return inferLaws(r, laws) }},
  {id: 'exists/stairs (with a step of 3)', track: 'exists', removed: 'the counter is even', broken: 'exists/stairs', today: () => { const {r, laws} = stairs('a step of 3'); return proveRule(r, laws, {search: false}) }, frontier: () => { const {r, laws} = stairs('a step of 3'); return proveRule(r, laws) }},
]
