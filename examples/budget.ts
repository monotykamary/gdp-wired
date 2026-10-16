// The README's example: a budget whose spend may overshoot by at most one capped request, proven, broken, searched and
// shipped.
//   bun examples/budget.ts
import {type Law, type Machine, atMost, compileJs, interpret, ite, less, min, n, plus, search, x} from '../core/machine.ts'
import {proveLaws} from '../kernel/prove.ts'

// A request of cost c is admitted while spend s is under budget b; each request is capped at m.
const budget = (capped = true): Machine => ({
  name: 'budget', params: ['b', 'm'], inputs: ['c'], state: {s: n(0)},
  step: {state: {s: ite(less(x('s'), x('b')), plus(x('s'), capped ? min(x('c'), x('m')) : x('c')), x('s'))}},
})
const boundedLoss: Law = {name: 'spend stays within b + m', holds: atMost(x('s'), plus(x('b'), x('m')))}

// Proven: the prover grows a tree of cases and the kernel checks it.
const ok = proveLaws(budget(), [boundedLoss])
console.log(`capped:   proven ${ok.proven}, kernel ${ok.checked ? 'accepts' : 'rejects'}, ${ok.leaves} leaves`)

// The cap forgotten: the step goal has a model, and a search from the start finds a real run that breaks the law.
const bad = proveLaws(budget(false), [boundedLoss])
console.log(`uncapped: proven ${bad.proven}, stuck at ${bad.failed?.goal} (${bad.failed?.stuck})`)
console.log(`          a run that breaks it: ${JSON.stringify(search(budget(false), boundedLoss))}`)

// Shipped: the same machine as JavaScript (or run by the interpreter); params and inputs are checked naturals.
const mod = new Function(`${compileJs(budget()).replace(/^export function/gm, 'function')}\nreturn {init, step}`)()
let st = mod.init({b: 100, m: 30})
for (const c of [50, 40, 70, 20]) st = mod.step({b: 100, m: 30}, st, {c})
console.log(`compiled: spend after 50, 40, 70, 20 with b = 100, m = 30: ${st.scalars.s}`)
const run = interpret(budget())
console.log(`checked:  ${(() => { try { run.step({b: 100, m: 30}, run.init({b: 100, m: 30}), {c: -5}); return 'accepted' } catch (e) { return (e as Error).message } })()}`)
