// The sliding-window limit (core/models.ts's windowLimit) as shipped, compileJs keeping the log and computing `seen`
// itself, at growing event counts: pruned (events in time order), it holds only the records of the last w, so its time
// grows with the events; unpruned, every request scans every record kept.
//   bun window-scale.ts
import {type Machine, interpret, loadJs} from '../../core/machine.ts'
import {windowLimit} from '../../core/models.ts'

const load = (m: Machine) => loadJs(m)
let s = 7
const lcg = () => ((s = (Math.imul(s, 1103515245) + 12345) >>> 0), s >>> 8)
const P = {w: 3600, c: 35}
const events = (count: number) => { let t = 0; return Array.from({length: count}, (_, i) => ({forced: i % 7 === 0 ? 1 : 0, t: (t += lcg() % 120)})) }
const median = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)]!
function time(run: any, evs: {forced: number, t: number}[], reps: number) {
  const params = {...P, now: evs.at(-1)!.t}
  let ours = 0, held = 0
  const ts: number[] = []
  for (let i = 0; i <= reps; i++) {
    const t0 = performance.now()
    let st = run.init(params)
    for (const e of evs) st = run.step(params, st, e)
    if (i) ts.push(performance.now() - t0)
    ours = st.scalars.ours, held = st.history.length - (st.head ?? 0)
  }
  return {ms: Math.round(median(ts) * 10) / 10, ours, recordsHeld: held}
}
const pruned = load(windowLimit(true)), full = load(windowLimit()), interpreted = interpret(windowLimit(true))
for (const count of [1000, 10_000, 100_000, 1_000_000]) {
  const evs = events(count)
  const row: Record<string, unknown> = {events: count, compiledPruned: time(pruned, evs, 3)}
  if (count <= 10_000) row.compiledUnpruned = time(full, evs, 3)
  if (count <= 10_000) row.interpretedPruned = time(interpreted, evs, 1)
  row.agree = new Set(Object.values(row).filter(v => typeof v === 'object').map((v: any) => v.ours)).size === 1
  console.log(JSON.stringify(row))
}
