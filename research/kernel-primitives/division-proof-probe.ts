// Bounded meaningful proof probes for division, not proof by sampled execution.
import {fixedInt, proveRule, proveSteps, rule} from '../../core/dsl.ts'
import {performance} from 'node:perf_hooks'
const k = fixedInt(8, false)
for (const variable of process.argv.includes('--constant-only') ? [false] : [false, true]) {
  const r = rule(`division ${variable ? 'variable' : 'constant'}`).inputs({n: k, d: k}).state({q: k.from('0'), rem: k.from('0')})
    .step(({n, d}) => {const divisor = variable ? d : k.lift(2); return {q: n.div(divisor, 'FLOOR', 'TRAP'), rem: n.rem(divisor, 'FLOOR', 'TRAP')}})
  const bounded = r.law('quotient and remainder fit', ({q, rem}) => q.atMost(k.lift(255)).and(rem.atMost(k.lift(255))))
  const arithmetic = r.stepLaw('division identity on successful steps', (before, after) =>
    before.d.eq(k.lift(0)).not().implies(after.q.limbs[0]!.mul((variable ? before.d : k.lift(2)).limbs[0]!).plus(after.rem.limbs[0]!).eq(before.n.limbs[0]!)))
  for (const name of ['bounds', 'identity'] as const) {
    const start = performance.now()
    try {
      const verdict = name === 'bounds' ? proveRule(r, [bounded], {search: false, watchdogMs: 3000})
        : proveSteps(r, [], [arithmetic], {search: false, watchdogMs: 3000})
      console.log(JSON.stringify({variable, name, wallMs: performance.now() - start, proven: verdict.proven, checked: verdict.checked,
        stuck: verdict.stuck ?? null, termination: verdict.termination ?? null}))
    } catch (error) {console.log(JSON.stringify({variable, name, wallMs: performance.now() - start, error: String(error)}))}
  }
}
