// The native ports (relations) against the phased ones (radix keys, a phase of row steps): on random requests, after each
// action (the phased port's rows run to the phase's end), the spec's variables read from both are the same.
//   bun research/protocols/relations/agree.ts [sequences] [length]
import {interpret, seeded} from '../../../core/machine.ts'
import {phased, protocols, tk} from '../ic3syn/models.ts'
import {N} from '../ic3syn/common.ts'

const seqs = Number(process.argv[2] ?? 300), len = Number(process.argv[3] ?? 40), R = (n: number) => [...Array(n).keys()]
const cases: {id: string, make: () => unknown, params: Record<string, number>, ops: number, row: number, names: string[], n: number, native: (s: any, n: number) => unknown, old: (s: any, n: number) => unknown}[] = [
  {id: 'learning_switch', make: phased.learningSwitch, params: {size: 3}, ops: 2, row: 2, names: ['ps', 'pd', 'sw0', 'sw1', 'nondet'], n: 3,
    native: (s: any, n: number) => [R(n).flatMap(t => R(n).flatMap(x => R(n).map(y => (x === y ? 1 : s.maps.T.get(tk(t, x, y)) ?? 0)))),
      R(n).flatMap(a => R(n).flatMap(b => R(n).flatMap(c => R(n).map(d => s.maps.P.get(tk(a, b, c, d)) ?? 0))))],
    old: (s: any, n: number) => [R(n).flatMap(t => R(n).flatMap(x => R(n).map(y => (x === y ? 1 : s.maps.T.get(t * N * N + x * N + y) ?? 0)))),
      R(n).flatMap(a => R(n).flatMap(b => R(n).flatMap(c => R(n).map(d => s.maps.P.get(((a * N + b) * N + c) * N + d) ?? 0))))]},
  {id: 'learning_switch_i4', make: phased.learningSwitchI4, params: {size: 4, packets: 1}, ops: 7, row: 7, names: ['p', 'sw0', 'sw1', 'sw2'], n: 4,
    native: (s: any, n: number) => [s.scalars.started, s.maps.SrcSet.get(0) ? (s.maps.Src.get(0) ?? 0) + 1 : 0, s.maps.DstSet.get(0) ? (s.maps.Dst.get(0) ?? 0) + 1 : 0,
      R(n).map(x => ((s.maps.LinkSet.get(x) ?? s.defaults?.LinkSet ?? 0) ? (s.maps.Link.get(x) ?? s.defaults?.Link ?? 0) + 1 : 0)),
      R(n).flatMap(x => R(n).map(y => s.maps.Dom.get(tk(x, y)) ?? 0)), R(n).flatMap(x => R(n).map(y => s.maps.Pend.get(tk(0, x, y)) ?? 0)),
      R(n).flatMap(t => R(n).flatMap(x => R(n).map(y => (x === y ? 1 : s.maps.T.get(tk(t, x, y)) ?? 0))))],
    old: (s: any, n: number) => [s.scalars.started, s.maps.Src.get(0) ?? 0, s.maps.Dst.get(0) ?? 0, R(n).map(x => s.maps.Link.get(x) ?? s.defaults?.Link ?? 0),
      R(n).flatMap(x => R(n).map(y => s.maps.Dom.get(x * N + y) ?? 0)), R(n).flatMap(x => R(n).map(y => s.maps.Pend.get(x * N + y) ?? 0)),
      R(n).flatMap(t => R(n).flatMap(x => R(n).map(y => (x === y ? 1 : s.maps.T.get(t * N * N + x * N + y) ?? 0))))]},
]
let bad = 0
for (const c of cases) {
  const nat = interpret((protocols.find(p => p.id === c.id)!.make() as any).machine), old = interpret((c.make() as any).machine), rnd = seeded(11)
  let steps = 0, changed = 0
  for (let q = 0; q < seqs; q++) {
    let a = nat.init(c.params), b = old.init(c.params)
    for (let i = 0; i < len; i++) {
      const req: Record<string, number> = {op: rnd(c.ops)}
      for (const name of c.names) req[name] = name === 'p' ? 0 : rnd(c.n)
      const a2 = nat.step(c.params, a, req)
      let b2 = old.step(c.params, b, req)
      while (b2.scalars.busy === 1) b2 = old.step(c.params, b2, {...req, op: c.row})
      const x = JSON.stringify(c.native(a2, c.n)), y = JSON.stringify(c.old(b2, c.n))
      if (x !== y) { if (++bad < 4) console.log('DIFFER', c.id, q, i, JSON.stringify(req), '\n native', x, '\n phased', y); break }
      if (x !== JSON.stringify(c.native(a, c.n))) changed++
      a = a2; b = b2; steps++
    }
  }
  console.log(JSON.stringify({id: c.id, steps, changed}))
}
console.log(bad ? `FAIL ${bad}` : 'agree')
process.exit(bad ? 1 : 0)
