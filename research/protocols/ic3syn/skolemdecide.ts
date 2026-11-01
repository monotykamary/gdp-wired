// The EPR path (kernel/prove.ts's decideLaw) on a plain-made law with given laws: bun skolemdecide.ts <id>
import {protocols} from './models.ts'
import {skolemOf} from '../../../core/exists.ts'
import {decideLaw, withDeadline, clock, counted, fullRate} from '../../../kernel/prove.ts'
import {type Law, type C, type E} from '../../../core/machine.ts'
import {decideHook} from '../../../kernel/epr.ts'
if (process.env.HOOK) decideHook.on = (g, d, ms) => console.log('  epr', g.name, g.hyps.length, 'unknown' in d ? d.unknown : d.sat ? 'sat' : 'unsat', Math.round(ms))
const id = process.argv[2] ?? 'firewall'
const p = protocols.find(q => q.id === id)!, r: any = p.make(), laws: Law[] = p.laws(r), kinds: Law[] = r.kindLaws()
const sk = skolemOf(r.machine, laws)!, m = sk.ghost(r.machine)
const v = (n: string): E => ({op: 'var', name: n}), get = (mp: string, k: E): E => ({op: 'get', map: mp, key: k}), c = (x: number): E => ({op: 'const', value: x})
const ge1 = (e: E): C => ({op: '<=', a: c(1), b: e}), eq0 = (e: E): C => ({op: '=', a: e, b: c(0)}), never = (...xs: C[]): C => ({op: 'not', x: {op: 'and', xs}})
const sent = (a: E, b: E) => get('Sent', {op: 'add', a: {op: 'mul', k: 64, a}, b})
const more: Law[] = [
  {name: 'nothing sent before start', forall: 'x', keys: ['y'], holds: never(ge1(sent(v('x'), v('y'))), eq0(v('started')))},
  {name: 'nothing allowed before start', forall: 'x', holds: never(ge1(get('AllowedIn', v('x'))), eq0(v('started')))},
  {name: 'none to itself', forall: 'x', holds: never(ge1(sent(v('x'), v('x'))))},
]
const all = [...kinds, ...sk.laws, ...more]
for (let i = kinds.length; i < all.length; i++) {
  const t = performance.now(), d = withDeadline(clock() + 20000, () => counted(fullRate, () => decideLaw(m, all, i), true))
  console.log(JSON.stringify({law: all[i]!.name.slice(0, 50), d: d ? (d.proven ? 'proven' : `model ${d.goal}`) : 'none', ms: Math.round(performance.now() - t)}))
}
