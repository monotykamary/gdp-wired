// k-step laws proven and timed, each certificate's `cyclic:` line printed with GDP_CYCLIC_LOG=1 (GDP_CYCLIC_PROF=1:
// where its time went): `bun research/cyclic/ksteps.ts 2 4 8 16 32`, the budget rule's (examples/steps.ts) for each k;
// `bun research/cyclic/ksteps.ts normal`, the quantifier examples' normal form (examples/quantifiers.ts).
import {min, nat, proveSteps, rule, when} from '../../core/dsl.ts'
import {proveStepLaws} from '../../kernel/prove.ts'
import {normalForm, normalFormLaws, normalFormSteps} from '../../examples/quantifiers.ts'

const budget = () => rule('budget').params({b: nat, m: nat}).inputs({c: nat, big: nat}).state({s: 0})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
const args = process.argv.slice(2)
if (args[0] === 'normal') {
  const a = normalForm(), t0 = performance.now(), v = proveStepLaws(a.machine, normalFormLaws(a), normalFormSteps(undefined, a))
  console.log(`normal form: ${v.proven && v.checked ? 'proven' : 'NOT PROVEN'} in ${(performance.now() - t0).toFixed(0)} ms`)
} else for (const k of args.length ? args.map(Number) : [2, 4, 8, 16, 32]) {
  const r = budget(), t0 = performance.now()
  const v = proveSteps(r, [r.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))], [r.stepsLaw(`${k} requests spend at most ${k}m`, k, ({s, m}, last) => last.s.atMost(s.plus(m.times(k))))])
  console.log(`${k} steps: ${v.proven && v.checked ? 'proven' : 'NOT PROVEN'} in ${(performance.now() - t0).toFixed(0)} ms`)
}
