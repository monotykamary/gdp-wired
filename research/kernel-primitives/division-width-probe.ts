import {fixedInt, proveRule, proveSteps, rule} from '../../core/dsl.ts'
import {performance} from 'node:perf_hooks'
const width = Number(process.argv[2])
const watchdogMs = Number(process.argv[3] ?? 5000)
if (width !== 8 && width !== 16 && width !== 32 && width !== 64) throw new Error('width required')
const k = fixedInt(width, false), max = (1n << BigInt(width)) - 1n
const r = rule(`u${width} variable division`).inputs({n: k, d: k}).state({q: k.from('0'), rem: k.from('0')})
 .step(({n, d}) => ({q: n.div(d, 'FLOOR', 'TRAP'), rem: n.rem(d, 'FLOOR', 'TRAP')}))
const bounds = r.law('quotient/remainder width', ({q, rem}) => q.atMost(k.lift(max)).and(rem.atMost(k.lift(max))))
const identity = r.stepLaw('word quotient/remainder identity', (before, after) => before.d.eq(k.lift(0n)).not().implies(
 after.q.mul(before.d, 'WRAP').plus(after.rem, 'WRAP').eq(before.n)))
const remainder = r.stepLaw('remainder less than divisor', (before, after) => before.d.eq(k.lift(0n)).not().implies(after.rem.lt(before.d)))
for (const name of ['bounds', 'identity', 'remainder'] as const) {
 const start = performance.now()
 try {
  const v = name === 'bounds' ? proveRule(r, [bounds], {search: false, watchdogMs})
   : proveSteps(r, [], [name === 'identity' ? identity : remainder], {search: false, watchdogMs})
  console.log(JSON.stringify({width, name, wallMs: performance.now() - start, proven: v.proven, checked: v.checked, admitted: v.proven && v.checked, stuck: v.stuck ?? null, why: v.why ?? null, termination: v.termination ?? null}))
 } catch (error) {console.log(JSON.stringify({width, name, wallMs: performance.now() - start, error: String(error)}))}
}
