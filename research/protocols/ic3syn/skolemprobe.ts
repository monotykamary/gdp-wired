// A law with "there exists" made plain (core/exists.ts's skolemOf) proven with given laws, the search off: where the
// ∀ search over its ghost map spends its time. bun research/protocols/ic3syn/skolemprobe.ts <id> [ms] [law texts as JSON file]
import {protocols} from './models.ts'
import {skolemOf, proveSome} from '../../../core/exists.ts'
import {proveLaws, proveLaw, proveSetFast, withDeadline, clock} from '../../../kernel/prove.ts'
import {type Law, type C, type E} from '../../../core/machine.ts'
const [id, ms0, extra] = process.argv.slice(2)
const p = protocols.find(q => q.id === id)!, r: any = p.make(), laws: Law[] = p.laws(r), kinds: Law[] = r.kindLaws()
const sk = skolemOf(r.machine, laws)!
const m = sk.ghost(r.machine)
const v = (n: string): E => ({op: 'var', name: n}), get = (mp: string, k: E): E => ({op: 'get', map: mp, key: k}), c = (x: number): E => ({op: 'const', value: x})
const ge1 = (e: E): C => ({op: '<=', a: c(1), b: e}), eq0 = (e: E): C => ({op: '=', a: e, b: c(0)})
const never = (...xs: C[]): C => ({op: 'not', x: {op: 'and', xs}})
const more: Law[] = extra === 'fw' ? [
  {name: 'nothing sent before start', forall: 'x', keys: ['y'], holds: never(ge1(get('Sent', {op: 'add', a: {op: 'mul', k: 64, a: v('x')}, b: v('y')})), eq0(v('started')))},
  {name: 'nothing allowed before start', forall: 'x', holds: never(ge1(get('AllowedIn', v('x'))), eq0(v('started')))},
  ...(process.env.MORE ? [{name: 'none to itself', forall: 'x', holds: never(ge1(get('Sent', {op: 'add', a: {op: 'mul', k: 64, a: v('x')}, b: v('x')})))},
    {name: 'internal not allowed', forall: 'x', holds: never(ge1(get('Internal', v('x'))), ge1(get('AllowedIn', v('x'))))}] as Law[] : []),
] : []
for (const l of [...sk.laws, ...more]) console.error('LAW', l.name, JSON.stringify(l).slice(0, 300))
const all = [...kinds, ...sk.laws, ...more]
for (let i = kinds.length; i < all.length; i++) { const t1 = performance.now(), o = withDeadline(clock() + 60000, () => proveLaw(m, all, i)); console.log(JSON.stringify({law: all[i]!.name.slice(0, 60), proven: o.proven, goal: o.goal, stuck: o.stuck, ms: Math.round(performance.now() - t1)})) }
const t = performance.now()
const out = withDeadline(clock() + Number(ms0 ?? 60000), () => proveLaws(m, [...kinds, ...sk.laws, ...more]))
console.log(JSON.stringify({id, proven: out.proven, failed: out.failed?.goal, stuck: out.failed?.stuck, ms: Math.round(performance.now() - t)}))
if (out.proven) { const t2 = performance.now(); const b = proveSome(r.machine, [...kinds, ...laws, ...more], process.env.FAST ? {whole: proveSetFast, mapMs: 20000} : {mapMs: 20000}); console.log(JSON.stringify({back: b.proven, failed: b.failed?.goal, stuck: b.failed?.stuck, why: b.failed?.why, ms: Math.round(performance.now() - t2)})) }
