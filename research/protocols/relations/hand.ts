import {forall, proveRule} from '../../../core/dsl.ts'
import {withWall} from '../../../kernel/prove.ts'
import {protocols, tabR} from '../../../research/protocols/ic3syn/models.ts'
import {below} from '../../../research/protocols/ic3syn/common.ts'
const wall = Number(process.argv[2] ?? 60000), id = process.argv[3] ?? 'learning_switch', drop = new Set((process.argv[4] ?? '').split(','))
const p = protocols.find(q => q.id === id)!
const r: any = p.make()
const hand = id === 'learning_switch' ? [
  r.law('pending: the source routes back', ({size, T, P}: any) => forall((ps, pd, s, d) => below(size, ps, pd, s, d).and(P.has(ps, pd, s, d), ps.eq(s).not()).implies(tabR(T, ps, s, ps)))),
  r.law('a route leads back to the root', ({size, T}: any) => forall((t, x, y) => below(size, t, x, y).and(tabR(T, t, x, y), t.eq(y).not(), x.eq(y).not()).implies(tabR(T, t, y, t)))),
] : [
  r.law('the root has no successor', ({size, T, started}: any) => forall((a, b) => started.eq(1).and(below(size, a, b), tabR(T, b, b, a)).implies(a.eq(b)))),
  r.law('no route without a domain', ({size, T, Dom, started}: any) => forall((c, a, b) => started.eq(1).and(below(size, a, b, c), tabR(T, c, a, b), Dom.has(c, a).not()).implies(a.eq(b)))),
  r.law('a pending packet routes back to its source or is in its domain', ({size, packets, T, Dom, Src, Pend, started}: any) => forall((q, c, a) => started.eq(1).and(q.lt(packets), below(size, c, a), Pend.has(q, c, a))
    .implies(tabR(T, Src.at(q), c, Src.at(q)).or(Dom.has(Src.at(q), c))))),
  // (one law a sort: a key that is a node in T's first place and a packet in Pend's makes the two sorts one)
  r.law('nothing before the start', ({T, Dom, started}: any) => forall((t, a, b) => started.eq(0).implies(T.has(t, a, b).not().and(Dom.has(a, b).not())))),
  r.law('nothing pending before the start', ({Pend, started}: any) => forall((q, a, b) => started.eq(0).implies(Pend.has(q, a, b).not()))),
  r.law('a domain routes to its root', ({size, T, Dom, started}: any) => forall((b, c) => started.eq(1).and(below(size, b, c), Dom.has(b, c)).implies(tabR(T, b, c, b)))),
  // (the rest of I4's set as gen/laneSW's handsw.ts writes it for the phased port)
  r.law('a pending hop is two nodes or the source twice', ({size, packets, started, Src, Pend}: any) => forall((q, a) => q.lt(packets).and(a.lt(size), started.eq(1), Pend.has(q, a, a)).implies(a.eq(Src.at(q))))),
  // (a link, src or dst set before the start already one the start keeps: the start reads only that they are set)
  r.law('link has no loop', ({size, started, Link, LinkSet}: any) => forall(x => x.lt(size).and(started.eq(1).or(LinkSet.has(x))).implies(LinkSet.has(x).and(Link.at(x).eq(x).not(), Link.at(x).lt(size))))),
  r.law('ends in range', ({size, packets, SrcSet, DstSet, Src, Dst}: any) => forall(q => q.lt(packets).implies(SrcSet.has(q).implies(Src.at(q).lt(size)).and(DstSet.has(q).implies(Dst.at(q).lt(size)))))),
  r.law('src total', ({packets, started, SrcSet, DstSet}: any) => forall(q => q.lt(packets).and(started.eq(1)).implies(SrcSet.has(q).and(DstSet.has(q))))),
].filter((l: any) => !drop.has(l.name))
const laws = [...p.laws(r), ...hand]
// (CTI=n, i4: n random states at size SIZE (4), one packet, where every law holds (trees per root perturbed, random
// pending, setup states too), each stepped by every request; a law broken after is a counterexample to induction)
if (process.env.CTI && id === 'learning_switch_i4') {
  const {interpret, evalC, seeded} = await import('../../../core/machine.ts')
  const {tk} = await import('../../../research/protocols/ic3syn/models.ts')
  const m = r.machine, run = interpret(m), rnd = seeded(Number(process.env.SEED ?? 7)), size = Number(process.env.SIZE ?? 4), params = {size, packets: 1}
  const ls = laws.map((l: any) => l.law ?? l), R = [...Array(size).keys()], pick = (xs: number[]) => xs[rnd(xs.length)]!
  const broken = (st: any) => { for (const l of ls) { const ks = [l.forall, ...(l.keys ?? [])].filter(Boolean); const go = (i: number, env: any): boolean => i === ks.length ? !evalC(l.holds, {...params, ...env}, st, m) : R.some(v => go(i + 1, {...env, [ks[i]]: v})); if (go(0, {})) return l.name } return undefined }
  const reqs: any[] = []
  for (let op = 0; op < 7; op++) for (const a of R) for (const b of R) for (const c of R) reqs.push({op, p: 0, sw0: a, sw1: b, sw2: c})
  let good = 0, cti = 0
  const seen = new Map<string, number>()
  for (let i = 0; i < Number(process.env.CTI) * 50 && good < Number(process.env.CTI); i++) {
    const started = rnd(5) ? 1 : 0, T = new Map<number, number>(), Dom = new Map<number, number>(), Pend = new Map<number, number>()
    const Src = new Map<number, number>(), Dst = new Map<number, number>(), Link = new Map<number, number>(), SS = new Map<number, number>(), DS = new Map<number, number>(), LS = new Map<number, number>()
    // (any value, in range or not, a loop or not, the laws reject what they don't allow)
    const V = [...R, size, size + 1]
    if (started || rnd(2)) { Src.set(0, pick(V)); SS.set(0, 1) } else if (rnd(2)) Src.set(0, pick(V))
    if (started || rnd(2)) { Dst.set(0, pick(V)); DS.set(0, 1) } else if (rnd(2)) Dst.set(0, pick(V))
    for (const x of R) if (started || rnd(2)) { Link.set(x, pick(V)); LS.set(x, 1) } else if (rnd(2)) Link.set(x, pick(V))
    if (started) {
      for (const a of R) {
        const up = new Map<number, number>([[a, -1]])
        for (const x of [...R].sort(() => rnd(2) - 0.5)) if (x !== a && rnd(3)) up.set(x, pick([...up.keys()]))
        for (const [x] of up) { if (x === a) continue; if (rnd(4)) Dom.set(tk(a, x), 1); for (let y = up.get(x)!; y >= 0; y = up.get(y)!) T.set(tk(a, x, y), 1) }
        for (let j = rnd(3); j > 0; j--) { const k = tk(a, pick(R), pick(R)); if (T.has(k)) T.delete(k); else T.set(k, 1) }
        for (let j = rnd(2); j > 0; j--) Dom.set(tk(a, pick(R)), 1)
      }
      for (let j = rnd(5); j > 0; j--) Pend.set(tk(0, pick(R), pick(R)), 1)
    }
    const st = {scalars: {started}, maps: {Src, Dst, Link, SrcSet: SS, DstSet: DS, LinkSet: LS, Pend, Dom, T}}
    if (broken(st)) continue
    good++
    for (const q of reqs) {
      const why = broken(run.step(params, st as any, q))
      if (why) { cti++; const n = (seen.get(why) ?? 0) + 1; seen.set(why, n); if (n <= 2) console.log('CTI', why, JSON.stringify(q), JSON.stringify(Object.fromEntries(Object.entries(st.maps).map(([k, v]) => [k, [...v]]))), started) }
    }
  }
  console.log(JSON.stringify({good, cti, by: Object.fromEntries(seen)}))
  process.exit(0)
}
const t0 = performance.now()
const v: any = withWall(performance.now() + wall, () => proveRule(r, laws, {search: false, ...(process.env.FAST ? {fast: true} : {})}))
console.log(JSON.stringify({id, proven: v.proven, checked: v.checked, goal: v.goal, why: String(v.why ?? '').slice(0, 200), ms: Math.round(performance.now() - t0)}))
if (process.env.FAIL) {
  const {proveLaws} = await import('../../../kernel/prove.ts')
  const o: any = proveLaws(r.machine, laws.map((l: any) => l.law ?? l))
  const w = o.failed?.witness ?? {}
  console.log(o.proven, o.failed?.goal, JSON.stringify(Object.fromEntries(Object.entries(w).filter(([k, x]) => !k.includes('[') || x))))
}
// (FAIL=2: the failing model read as a concrete state, every law checked at every tuple below size, before and after
// the model's step: a real counterexample to induction, or a model only of the instances the proof chose)
if (process.env.FAIL === '2') {
  const {proveLaws} = await import('../../../kernel/prove.ts')
  const {cellParts} = await import('../../../kernel/kernel.ts')
  const {interpret, evalC, cpair} = await import('../../../core/machine.ts')
  const m = r.machine, ls = laws.map((l: any) => l.law ?? l), o: any = proveLaws(m, ls), w = o.failed?.witness ?? {}
  const val = (lin: Record<string, number>) => Object.entries(lin).reduce((s2, [k, c]) => s2 + c * (k === '1' ? 1 : (w[k] ?? 0)), 0)
  const maps: Record<string, Map<number, number>> = Object.fromEntries(Object.keys(m.maps).map(k => [k, new Map()]))
  for (const [n, x] of Object.entries(w)) if (n.includes('[') && !n.startsWith('⟦')) { const cp = cellParts(n); if (!maps[cp.map]) continue; const key = cp.keys ? cp.keys.map(val).slice(0, -1).reduceRight((b: number, a) => cpair(a, b), val(cp.keys.at(-1)!)) : val(cp.key!); maps[cp.map]!.set(key, x as number) }
  const params = Object.fromEntries(m.params.map((q: string) => [q, w[q] ?? 0])), size = params.size
  const st = {scalars: Object.fromEntries(Object.keys(m.state).map(q => [q, w[q] ?? 0])), maps}
  const req = Object.fromEntries(m.inputs.map((q: string) => [q, w[q] ?? 0]))
  const broken = (s2: any) => { for (const l of ls) { const ks = [l.forall, ...(l.keys ?? [])].filter(Boolean); const go = (i: number, env: any): boolean => i === ks.length ? !evalC(l.holds, {...params, ...env}, s2, m) : [...Array(size).keys()].some(v => go(i + 1, {...env, [ks[i]]: v})); if (go(0, {})) return l.name } return undefined }
  console.log('goal', o.failed?.goal, 'before:', broken(st) ?? 'all hold', 'after:', broken(interpret(m).step(params, st as any, req)) ?? 'all hold', JSON.stringify(req))
}
