// A hand BFS of ring_leader_election's small instance (size 3, ids 5, 4, 7): its states and how many have a leader.

import {interpret, loadJs} from '../../../core/machine.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === 'ring_leader_election')!, r: any = p.make(), m = r.machine, js = loadJs(m), run = interpret(m)
const params = {size: 3}, combos: any[] = []
for (const op of [0, 1, 2]) for (const n of [0, 1, 2]) for (const n1 of [0, 1, 2]) for (const mm of [5, 4, 7]) combos.push({op, n, n1, m: mm})
const key2 = (st: any) => JSON.stringify([st.scalars, Object.entries(st.maps).map(([mp, cells]: any) => [mp, [...cells].filter(([, v]: any) => v !== 0).sort((a: any, b: any) => a[0] - b[0])])])
const st0 = run.init(params), seen = new Map([[key2(st0), st0]]), q = [st0]
while (q.length && seen.size < 5000) { const s = q.shift()!; for (const c of combos) { let n2: any; try { n2 = js.step(params, js.fork(s), c) } catch { continue } const k = key2(n2); if (!seen.has(k)) { seen.set(k, n2); q.push(n2) } } }
const leaders = [...seen.values()].filter((s: any) => [...s.maps.Leader.values()].some((v: number) => v > 0))
console.log('states', seen.size, 'with a leader', leaders.length, 'm values', [0, 1, 2].map(k => k ^ 5))
console.log([...seen.keys()].slice(-3).join('\n').slice(0, 600))
