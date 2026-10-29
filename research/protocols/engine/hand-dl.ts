// A hand BFS of distributed_lock's small instance (params first 0, e1 1; nodes 0..1, epochs 0..3), every distinct state.

import {interpret, loadJs} from '../../../core/machine.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === 'distributed_lock')!, r: any = p.make(), m = r.machine, run = interpret(m), js = loadJs(m)
const params = {first: 0, e1: 1}, combos: any[] = []
for (const op of [0, 1, 2]) for (const n1 of [0, 1]) for (const n2 of [0, 1]) for (const e of [0, 1, 2, 3]) combos.push({op, n1, n2, e})
const key2 = (st: any) => JSON.stringify([st.scalars, Object.entries(st.maps).map(([mp, cells]: any) => { const d = st.defaults?.[mp] ?? m.maps?.[mp] ?? 0; return [mp, [...cells].filter(([, v]: any) => v !== d).sort((a: any, b: any) => a[0] - b[0])] }), st.defaults ?? null])
const st0 = run.init(params), seen = new Map([[key2(st0), st0]]), q = [st0]
while (q.length) { const s = q.shift(); for (const c of combos) { let n2: any; try { n2 = js.step(params, js.fork(s), c) } catch { continue } const k = key2(n2); if (!seen.has(k)) { seen.set(k, n2); q.push(n2) } } }
console.log('states', seen.size, 'inputs', m.inputs, 'maps', Object.keys(m.maps))
for (const k of [...seen.keys()].slice(0, 40)) console.log(k.slice(0, 220))
