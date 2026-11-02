// Steps of a relation port, timed: core/infer.ts's domainStep against the interpreter (a probe; not a gate).
//   bun research/protocols/relations/stepbench.ts [id] [steps] [size]   (ONLY=1: domainStep alone; CHECK=n: n steps compared)
import {protocols} from '../../../research/protocols/ic3syn/models.ts'
import {interpret, seeded} from '../../../core/machine.ts'
import {allowed} from '../../../core/watch.ts'
import {domainStep} from '../../../core/infer.ts'
const id = process.argv[2] ?? 'learning_switch', steps = Number(process.argv[3] ?? 2000), size = Number(process.argv[4] ?? 4)
const r: any = protocols.find(p => p.id === id)!.make(), m = r.machine, run = interpret(m), fast = domainStep(m)!, rand = seeded(7)
const params = {...r.randomParams(rand, size), size, ...(m.params.includes('packets') ? {packets: 2} : {})}
const slow = (p: any, s: any, i: any) => (allowed(m, run, p, s, i) ? run.step(p, s, i) : undefined)
for (const [name, f] of [['domain', fast], ...(process.env.ONLY ? [] : [['interp', slow]])] as [string, any][]) {
  const rnd = seeded(3)
  let st = run.init(params), t = performance.now(), moved = 0
  for (let k = 0; k < steps; k++) { const inp = r.randomInput(rnd, size - 1, params); let n2; try { n2 = (f as any)(params, st, inp) } catch { n2 = undefined } if (n2) { st = n2; moved++ } if (k % 200 === 199) st = run.init(params) }
  console.log(name, JSON.stringify(params), 'steps', steps, 'moved', moved, 'ms', Math.round(performance.now() - t))
}
// (CHECK=n: n steps, each from the same state by both, their states compared)
if (process.env.CHECK) {
  const rnd = seeded(5), canon = (s: any) => s && JSON.stringify([s.scalars, Object.entries(s.maps).map(([k, c]: any) => [k, [...c].filter(([, v]: any) => v !== (s.defaults?.[k] ?? 0)).sort((p: any, q: any) => p[0] - q[0])])])
  let st = run.init(params), bad = 0, live = 0
  for (let k = 0; k < Number(process.env.CHECK); k++) {
    const inp = r.randomInput(rnd, size - 1, params)
    let a, b
    try { a = fast(params, st, inp) } catch { a = undefined }
    try { b = slow(params, st, inp) } catch { b = undefined }
    if (canon(a) !== canon(b)) { bad++; if (bad < 3) console.log('differ', JSON.stringify(inp), canon(a)?.slice(0, 300), canon(b)?.slice(0, 300)) }
    if (b) st = b
    if (Object.values(st.scalars).some((v: any) => v > 0)) live++
    if (k % 400 === 399) st = run.init(params)
  }
  console.log('check', process.env.CHECK, 'differ', bad, 'from a state with a scalar past 0', live)
}
