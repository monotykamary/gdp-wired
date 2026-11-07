// A concrete initialization trace, not a solver model: does the published
// equal-version/equal-term row agreement hold during the port's auxiliary phases?
import {mldr} from './phased-mldr.ts'
import {type Law, all, any, get, interpret, less, not, plus, same, times, x} from '../../core/machine.ts'
import {holdsAt} from '../../core/exists.ts'
const r = mldr(), m = r.machine
const a = x('audit$a'), b = x('audit$b'), k = x('audit$k'), size = x('size')
const law: Law = {name: 'equal configuration terms and versions imply equal configurations', forall: 'audit$a', keys: ['audit$b', 'audit$k'], holds: any(not(all(less(a, size), less(b, size), less(k, size), same(get('CV', a), get('CV', b)), same(get('CfgT', a), get('CfgT', b)))), same(get('Config', plus(times(64, a), k)), get('Config', plus(times(64, b), k))))}
const runtime = interpret(m), params = {size: 3}
const request = (op: number) => ({op, i: 0, j: 0, hx: 0, hy: 0, S: new Map([[0, 1]]), Q2: new Map<number, number>()})
let state = runtime.init(params)
console.log(JSON.stringify({phase: 'init', holds: holdsAt(m, law, params, state, 3)}))
for (const [phase, op] of [['pick', 0], ['copy server 0', 1]] as const) {
  state = runtime.step(params, state, request(op))
  console.log(JSON.stringify({phase, holds: holdsAt(m, law, params, state, 3), scalars: state.scalars, maps: Object.fromEntries(Object.entries(state.maps).map(([key, cells]) => [key, [...cells]]))}))
}
if (holdsAt(m, law, params, state, 3)) throw new Error('expected the concrete phase counterexample')
