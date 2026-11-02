import {interpret, seeded} from '../../../core/machine.ts'
import {protocols, tk} from '../../../research/protocols/ic3syn/models.ts'
const p = protocols.find(q => q.id === 'learning_switch')!
const r: any = p.make(), m = r.machine, run = interpret(m), n = 3, rand = seeded(7)
const R = [0, 1, 2]
const lawsHold = (st: any) => {
  const T = (t: number, x: number, y: number) => x === y || st.maps.T.get(tk(t, x, y)) === 1
  const P = (a: number, b: number, c: number, d: number) => st.maps.P.get(tk(a, b, c, d)) === 1
  for (const t of R) for (const x of R) for (const y of R) {
    if (T(t, x, y) && T(t, y, x) && x !== y) return 'anti'
    if (T(t, x, y) && t !== y && x !== y && !T(t, y, t)) return 'help4'
    for (const z of R) { if (T(t, x, y) && T(t, y, z) && !T(t, x, z)) return 'trans'; if (T(t, x, y) && T(t, x, z) && !T(t, y, z) && !T(t, z, y)) return 'chain' }
  }
  for (const a of R) for (const b of R) for (const c of R) for (const d of R) if (P(a, b, c, d) && a !== c && !T(a, c, a)) return 'help3'
  return undefined
}
let tried = 0, good = 0, broken = 0
for (let i = 0; i < 20000 && good < 400; i++) {
  const T = new Map<number, number>(), P = new Map<number, number>()
  for (const t of R) for (const x of R) for (const y of R) if (x !== y && rand(3) === 0) T.set(tk(t, x, y), 1)
  for (let j = rand(4); j > 0; j--) P.set(tk(rand(n), rand(n), rand(n), rand(n)), 1)
  const st = {scalars: {}, maps: {T, P}}
  tried++
  if (lawsHold(st)) continue
  good++
  for (const op of [0, 1]) for (const ps of R) for (const pd of R) for (const sw0 of R) for (const sw1 of R) for (const nondet of R) {
    const s2 = run.step({size: n}, st as any, {op, ps, pd, sw0, sw1, nondet})
    const why = lawsHold(s2)
    if (why) { broken++; if (broken < 4) console.log('CTI', why, JSON.stringify({op, ps, pd, sw0, sw1, nondet}), JSON.stringify([...T]), JSON.stringify([...P])) }
  }
}
console.log({tried, good, broken})
