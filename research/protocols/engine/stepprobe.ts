// wo's small instance: the cost of a step (interpreter, compiled JS), of allowed(), and of a state's key, per call.
//   bun research/protocols/engine/stepprobe.ts
import {interpret} from '../../../core/machine.ts'
import {allowed} from '../../../core/watch.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === 'consensus_wo_decide')!, r: any = p.make(), m = r.machine, run = interpret(m), js = r.compiled()
const K = [0, 1, 2], subsets = Array.from({length: 8}, (_, b) => new Map(K.filter((_, j) => b >> j & 1).map(k => [k, 1] as [number, number])))
const combos: any[] = []
for (const op of [0, 1, 2, 3, 4, 5]) for (const src of K) for (const dst of K) for (const nondet of [0, 1]) for (const w of K) for (const Q of subsets) combos.push({op, src, dst, nondet, w, Q})
const keyOf = (st: any) => JSON.stringify([st.scalars, Object.entries(st.maps).map(([k, v]: any) => [k, [...v]])])
// a few states along a run
let st = run.init({}); const states = [st]
for (let i = 0; i < 400; i++) { const c = combos[(i * 7919) % combos.length]; try { if (allowed(m, run, {}, st, c)) { st = run.step({}, st, c); states.push(st) } } catch {} }
const time = (name: string, f: (s: any, c: any) => unknown) => { const t = performance.now(); let n = 0; for (const s of states.slice(0, 40)) for (const c of combos) { try { f(s, c) } catch {} n++ } console.log(name, ((performance.now() - t) * 1000 / n).toFixed(2), 'µs a call', n) }
time('allowed', (s, c) => allowed(m, run, {}, s, c))
time('interpret step', (s, c) => run.step({}, s, c))
time('compiled step', (s, c) => js.step({}, js.fork(s), c))
time('key', (s) => keyOf(s))
console.log('states', states.length, 'combos', combos.length, 'cells', [...Object.values(st.maps)].map((v: any) => v.size).join(','))
