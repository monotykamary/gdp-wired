// wo's small instance (3 nodes): BFS until a state with a leader, its depth and the states before it, within 25 s.
//   bun research/protocols/engine/bfsprobe.ts
import {interpret} from '../../../core/machine.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === 'consensus_wo_decide')!, r: any = p.make(), m = r.machine, run = interpret(m)
const K = [0, 1, 2], ops = [0, 1, 2, 3, 4, 5], subsets = Array.from({length: 8}, (_, b) => new Map(K.filter((_, j) => b >> j & 1).map(k => [k, 1] as [number, number])))
const combos: any[] = []
for (const op of ops) for (const src of K) for (const dst of K) for (const nondet of [0, 1]) for (const w of K) for (const Q of subsets) combos.push({op, src, dst, nondet, w, Q})
const keyOf = (st: any) => JSON.stringify([st.scalars, Object.entries(st.maps).map(([k, v]: any) => [k, [...v].filter(([, x]: any) => x).sort((a: any, b: any) => a[0] - b[0])])])
const t0 = performance.now(), st0 = run.init({}), seen = new Set([keyOf(st0)])
let frontier = [st0], depth = 0, steps = 0
while (frontier.length && performance.now() - t0 < 25_000) {
  const next: any[] = []
  for (const st of frontier) for (const c of combos) {
    let s2: any; steps++
    try { s2 = run.step({}, st, c) } catch { continue }
    const k = keyOf(s2); if (seen.has(k)) continue
    seen.add(k); next.push(s2)
    if ([...s2.maps.Leader.values()].some((v: number) => v > 0)) { console.log('leader at depth', depth + 1, 'states', seen.size, 'steps', steps, Math.round(performance.now() - t0), 'ms'); process.exit(0) }
  }
  depth++; frontier = next; console.log('depth', depth, 'states', seen.size, Math.round(performance.now() - t0), 'ms')
}
console.log('no leader', seen.size, 'states')
