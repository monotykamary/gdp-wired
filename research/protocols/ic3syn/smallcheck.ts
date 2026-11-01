// The small instances (core/exists.ts's smallOf) of each port, against core/exists-base.ts's: states, a digest, ms.
//   bun research/protocols/ic3syn/smallcheck.ts [ids]
import {protocols} from './models.ts'
import {smallOf} from '../../../core/exists.ts'
import {smallOf as smallOfBase} from '../../../core/exists-base.ts'
import {createHash} from 'node:crypto'
const only = process.argv[2]?.split(',')
const dig = (xs: {p: unknown, sts: {scalars: unknown, maps: Record<string, Map<number, number>>}[]}[]) => createHash('sha1').update(JSON.stringify(xs.map(x => [x.p, x.sts.map(s => [s.scalars, Object.entries(s.maps).map(([n, c]) => [n, [...c].sort((a, b) => a[0] - b[0])])])]))).digest('hex').slice(0, 12)
for (const p of protocols.filter(q => !only || only.includes(q.id))) {
  const m = p.make().machine
  let t = performance.now(); const a = smallOf(m); const ta = performance.now() - t
  const m2 = p.make().machine
  t = performance.now(); const b = smallOfBase(m2); const tb = performance.now() - t
  console.log(JSON.stringify({id: p.id, states: a.map(x => x.sts.length), same: dig(a) === dig(b), ms: Math.round(ta), base: Math.round(tb)}))
}
