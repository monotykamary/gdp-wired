// The README's example: a budget whose spend may overshoot by at most one capped request, proven, broken, searched and
// shipped.
//   bun examples/budget.ts
import {min, nat, proveRule, rule, when} from '../core/dsl.ts'
import {search} from '../core/machine.ts'

// A request of cost c is admitted while spend s is under budget b; each request is capped at m.
const budget = rule('budget')
  .params({b: nat, m: nat})
  .inputs({c: nat})
  .state({s: 0})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))

// Proven: the prover grows a tree of cases and the kernel checks it.
const ok = proveRule(budget, [bounded])
console.log(`capped:   proven ${ok.proven}, kernel ${ok.checked ? 'accepts' : 'rejects'}`)

// The cap forgotten: the kernel refuses the proof, and a search from the start finds a real run that breaks the law.
const uncapped = budget.step(({b, c, s}) => ({s: when(s.lt(b), s.plus(c), s)}))
const bad = proveRule(uncapped, [bounded])
console.log(`uncapped: proven ${bad.proven}, stuck at ${bad.goal} (${bad.stuck})`)
console.log(`          a run that breaks it: ${JSON.stringify(search(uncapped.machine, bounded))}`)

// Shipped: the same rule as generated JavaScript (or run by the interpreter); params and inputs are checked naturals.
const shipped = budget.compiled()
let st = shipped.init(budget.encodeParams({b: 100, m: 30}))
for (const c of [50, 40, 70, 20]) st = shipped.step({b: 100, m: 30}, st, budget.encodeInput({c}))
console.log(`compiled: spend after 50, 40, 70, 20 with b = 100, m = 30: ${st.scalars.s}`)
const run = budget.interpreter()
console.log(`checked:  ${(() => { try { run.step({b: 100, m: 30}, run.init({b: 100, m: 30}), {c: -5}); return 'accepted' } catch (e) { return (e as Error).message } })()}`)
