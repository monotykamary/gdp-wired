// Leave-one-out over a protocol's written laws (models.ts's `human`): the caller's law proven with the whole written
// set, then with each written law left out, by the fast set proof; the laws whose absence fails it are the essential ones.
//   bun research/protocols/engine/looprobe.ts <id>
import {proveRule} from '../../../core/dsl.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === process.argv[2])!
const ask = (what: string, pick: (hs: any[]) => any[]) => {
  const r: any = p.make(), hs = p.human(r), t = performance.now(), v = proveRule(r, [...pick(hs), ...p.laws(r)], {search: false, fast: true})
  console.log(what, '→', v.proven && v.checked ? 'proven' : `${v.stuck} at ${String(v.goal ?? '').slice(0, 110)}`, Math.round(performance.now() - t), 'ms')
}
ask('all written', hs => hs)
const names = p.human(p.make() as any).map((h: any) => h.name)
for (const nm of names) ask(`  without "${nm}"`, hs => hs.filter((h: any) => h.name !== nm))
