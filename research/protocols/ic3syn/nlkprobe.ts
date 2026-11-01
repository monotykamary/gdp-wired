// probe: no_lost_keys's plain law with hand-written supports over skolemOf's ghosts, proven of the ghosted machine?
import {protocols} from './models.ts'
import {skolemOf} from '../../../core/exists.ts'
import {type C, type E, type Law, all, any, atMost, get, less, n, not, plus, same, times, x} from '../../../core/machine.ts'
import {type Ghosted, ghostedMachine} from '../../../kernel/kernel.ts'
import {proveLaws} from '../../../kernel/prove.ts'
const p = protocols.find(q => q.id === 'sharded_kv_no_lost_keys')!, r: any = p.make(), m = r.machine, stated: Law[] = p.laws(r)
const sk = skolemOf(m, stated)!
console.log(Object.keys(sk.maps), JSON.stringify(sk.plains[stated[0]!.name]!.sub))
const G: Ghosted = {orig: m, vars: {}, maps: sk.maps}, gm = ghostedMachine(G)
const [On, Tn, Tv] = Object.keys(sk.maps).sort((a, b) => (a.startsWith('Owner') ? -1 : b.startsWith('Owner') ? 1 : a.includes('$n') ? -1 : 1)) as [string, string, string]
console.log(On, Tn, Tv)
const k = x('kk'), one = n(1), N = 64
const S: Law[] = [
  {name: 'b1', forall: 'kk', holds: less(get(On, k), n(N))},
  {name: 'b2', forall: 'kk', holds: less(get(Tn, k), n(N))},
  {name: 'b3', forall: 'kk', holds: less(get(Tv, k), n(N))},
  {name: 'own before start', forall: 'kk', holds: any(not(all(same(x('started'), n(0)), same(get('Owned', k), one))), same(get('Owner', plus(times(N, k), get(On, k))), one))},
  {name: 'no transfer before start', forall: 'kk', holds: any(not(same(x('started'), n(0))), same(get('TransferMsg', k), n(0)))},
]
const want = process.argv[2] === 'all' ? S : S.slice(0, Number(process.argv[2] ?? 5))
const t = performance.now(), out = proveLaws(gm, [...r.kindLaws(), ...sk.laws, ...want])
console.log(JSON.stringify({ms: Math.round(performance.now() - t), proven: out.proven, checked: out.checked, failed: out.failed}).slice(0, 800))
{
  const a = r.withGhosts(sk.ghost).machine, b = ghostedMachine(G)
  for (const k of new Set([...Object.keys(a), ...Object.keys(b)])) if (JSON.stringify((a as any)[k]) !== JSON.stringify((b as any)[k])) {
    console.log('differs', k)
    const x = (a as any)[k], y = (b as any)[k]
    if (x && typeof x === 'object') for (const k2 of new Set([...Object.keys(x), ...Object.keys(y ?? {})])) if (JSON.stringify(x[k2]) !== JSON.stringify(y?.[k2])) console.log('  ', k2, JSON.stringify(x[k2]).slice(0, 200), '|', JSON.stringify(y?.[k2]).slice(0, 200))
  }
}
