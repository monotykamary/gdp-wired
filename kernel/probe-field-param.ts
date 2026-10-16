// Probe: a param named like a record field (r.t). kernel.ts's history rule reads `r.t` in the record goal as the field,
// while pre and `when` read it as the param.
import {type Machine, atMost, evalC, interpret, ite, less, n, plus, same, x} from '../core/machine.ts'
import {proveLaws} from './prove.ts'

const m: Machine = {
  name: 'field named like a param', params: ['r.t'], inputs: ['t', 's'], state: {z: n(0)},
  pre: same(x('r.t'), n(0)),
  step: {state: {z: plus(x('z'), ite(less(x('s'), x('u')), n(1), n(0)))}},
  history: {keep: same(n(0), n(0)), record: ['t'], sums: {u: x('r.t')}, queries: {s: n(0)},
    relations: [{when: same(x('r.t'), n(0)), holds: atMost(x('u'), x('s'))}]},
}
const law = {name: 'z = 0', holds: same(x('z'), n(0))}
// Before the r. prefix was reserved, the kernel proved z = 0 while a run (r.t = 0; t = 5, then t = 0) ended at z = 1.
try {
  const r = proveLaws(m, [law])
  console.log(`kernel: ${r.proven ? 'PROVEN' : 'not proven'}, checked ${r.checked}`)
  const run = interpret(m), params = {'r.t': 0}
  let st = run.init(params)
  for (const t of [5, 0]) st = run.step(params, st, {t})
  console.log(`run: u = ${st.scalars.u}, z = ${st.scalars.z}, law holds: ${evalC(law.holds, params, st, m)}`)
  process.exitCode = 1
} catch (e) {
  console.log(`refused, as it should be: ${(e as Error).message}`)
}
