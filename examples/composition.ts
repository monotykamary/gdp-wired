// Composition (core/compose.ts), proven by the kernel as it is. For the suite (`bun examples/composition.ts`),
// core/compose.test.ts and lean-kernel/export-kernel.ts (the Lean twin checks these machines like any other).
//   - refinement: a meter that counts down what is left refines the meter that counts up what is used
//   - interleaving: two capped counters, one moving per request; each keeps its cap, and two turns of one leave the other
import {type C, type Law, type Machine, plus, x} from '../core/machine.ts'
import {min, nat, rule, upTo, when} from '../core/dsl.ts'
import {interleave, refinement, side} from '../core/compose.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {proveStepLaws} from '../kernel/prove.ts'

// The spec only takes spends up to `most`; the implementation counts down what is left and clamps each spend to `most`
// first, so every request it takes is one the spec allows.
export const meter = rule('meter').params({cap: nat, most: nat}).inputs({amount: nat}).state({used: 0})
  .assume(({amount, most}) => amount.atMost(most))
  .flags(({amount, used, cap}) => ({fits: used.plus(amount).atMost(cap)}))
  .step(({used, amount, fits}) => ({used: when(fits, used.plus(amount), used)}))
export const countdown = (bug?: 'no clamp' | 'strict') => rule('meter, counting down').params({cap: nat, most: nat}).inputs({amount: nat}).state({left: ({cap}) => cap})
  .step(({left, amount, most}) => {
    const spend = bug === 'no clamp' ? amount : min(amount, most)
    return {left: when(bug === 'strict' ? spend.lt(left) : spend.atMost(left), left.minus(spend), left)}
  })
export const meterRelation: Law[] = [{name: 'left + used = cap', holds: {op: '=', a: plus(x('a_left'), x('b_used')), b: x('cap')}}]
export const meterRefinement = (bug?: 'no clamp' | 'strict') => refinement(countdown(bug).machine, meter.machine, {
  relation: meterRelation,
  witness: {amount: bug === 'no clamp' ? x('amount') : {op: 'min', a: x('amount'), b: x('most')}},
})

// Two capped counters, interleaved.
export const counter = rule('counter').params({cap: upTo(10)}).inputs({amount: nat}).state({n: 0})
  .step(({n, amount, cap}) => ({n: when(n.plus(amount).atMost(cap), n.plus(amount), n)}))
export const counters: Machine = interleave(counter.machine, counter.machine)
export const counterLaws: Law[] = (['a_', 'b_'] as const).map(p => ({name: `${p[0]}.n <= cap`, holds: side(counter.machine, p, {op: '<=', a: x('n'), b: x('cap')})}))
const aTurn: C = {op: '=', a: x('turn'), b: {op: 'const', value: 0}}
export const counterSteps: StepLaw[] = [
  {name: "an a turn leaves b's count", when: aTurn, then: {op: '=', a: x("b_n'"), b: x('b_n')}},
  {name: "two a turns leave b's count", steps: 2, when: [aTurn, aTurn], then: {op: '=', a: x("b_n'"), b: x('b_n')}},
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const ok = meterRefinement()
  const r = proveStepLaws(ok.machine, ok.laws, ok.stepLaws)
  results.push(['countdown refines meter', r.proven && r.checked, true])
  for (const bug of ['no clamp', 'strict'] as const) {
    const b = meterRefinement(bug)
    results.push([`countdown (${bug}) refines meter`, proveStepLaws(b.machine, b.laws, b.stepLaws).proven, false])
  }
  const c = proveStepLaws(counters, counterLaws, counterSteps)
  results.push(['interleaved counters', c.proven && c.checked, true])
  for (const [what, got, want] of results) console.log(`${what.padEnd(34)} ${got ? 'proven, kernel accepts' : 'not proven'}${got === want ? '' : '   UNEXPECTED'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
