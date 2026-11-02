import {proveLaws} from '../../../kernel/prove.ts'
import {forall} from '../../../core/dsl.ts'
import {protocols, tabR} from '../../../research/protocols/ic3syn/models.ts'
import {below} from '../../../research/protocols/ic3syn/common.ts'
const p = protocols.find(q => q.id === 'learning_switch')!
const r: any = p.make()
const hand = [
  r.law('pending: the source routes back', ({size, T, P}: any) => forall((ps, pd, s, d) => below(size, ps, pd, s, d).and(P.has(ps, pd, s, d), ps.eq(s).not()).implies(tabR(T, ps, s, ps)))),
  r.law('a route leads back to the root', ({size, T}: any) => forall((t, x, y) => below(size, t, x, y).and(tabR(T, t, x, y), t.eq(y).not(), x.eq(y).not()).implies(tabR(T, t, y, t)))),
]
const laws = [...p.laws(r), ...hand].map((l: any) => l.law ?? l)
console.log(laws.map((l: any) => l.name + ' ' + l.forall + ' ' + JSON.stringify(l.keys)).join('\n'))
const m = r.machine
const t0 = performance.now(), out: any = proveLaws(m, laws)
console.log(out.proven, Math.round(performance.now() - t0), JSON.stringify(out.failed).slice(0, 2500))
import {cellParts} from '../../../kernel/kernel.ts'
import {cpair} from '../../../core/machine.ts'
const w = out.failed?.witness ?? {}
const val = (lin: Record<string, number>) => Object.entries(lin).reduce((s, [k, c]) => s + c * (k === '1' ? 1 : (w[k] ?? 0)), 0)
const cells = new Map<string, number>()
for (const [n, x] of Object.entries(w)) if (n.includes('[')) {
  const cp = cellParts(n), key = cp.keys ? cp.keys.map(val).slice(0, -1).reduceRight((b, a) => cpair(a, b), val(cp.keys.at(-1)!)) : val(cp.key!)
  const id = `${cp.map}@${key}`
  if (cells.has(id) && cells.get(id) !== x) console.log('CONFLICT', n, id, cells.get(id), x)
  cells.set(id, x as number)
}
console.log('cells', cells.size, 'conflicts checked')
