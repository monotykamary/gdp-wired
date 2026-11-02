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
  r.law('nothing before the start', ({size, packets, T, Dom, Pend, started}: any) => forall((q, a, b) => started.eq(0).implies(T.has(q, a, b).not().and(Dom.has(a, b).not(), Pend.has(q, a, b).not())))),
  r.law('a domain routes to its root', ({size, T, Dom, started}: any) => forall((b, c) => started.eq(1).and(below(size, b, c), Dom.has(b, c)).implies(tabR(T, b, c, b)))),
  // (the rest of I4's set as gen/laneSW's handsw.ts writes it for the phased port)
  r.law('a pending hop is two nodes or the source twice', ({size, packets, started, Src, Pend}: any) => forall((q, a) => q.lt(packets).and(a.lt(size), started.eq(1), Pend.has(q, a, a)).implies(a.eq(Src.at(q))))),
  r.law('link has no loop', ({size, started, Link, LinkSet}: any) => forall(x => x.lt(size).and(started.eq(1)).implies(LinkSet.has(x).and(Link.at(x).eq(x).not(), Link.at(x).lt(size))))),
  r.law('ends in range', ({size, packets, started, Src, Dst}: any) => forall(q => q.lt(packets).and(started.eq(1)).implies(Src.at(q).lt(size).and(Dst.at(q).lt(size))))),
  r.law('src total', ({packets, started, SrcSet, DstSet}: any) => forall(q => q.lt(packets).and(started.eq(1)).implies(SrcSet.has(q).and(DstSet.has(q))))),
].filter((l: any) => !drop.has(l.name))
const laws = [...p.laws(r), ...hand]
const t0 = performance.now()
const v: any = withWall(performance.now() + wall, () => proveRule(r, laws, {search: false}))
console.log(JSON.stringify({id, proven: v.proven, goal: v.goal, why: String(v.why ?? '').slice(0, 200), ms: Math.round(performance.now() - t0)}))
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
