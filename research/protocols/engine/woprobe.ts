// wo's caller law against the stage's set (its cubes and its ∃ law, dumped by GDP_ENGINE_DUMP), outside the search, as
// the stage asks it: the ∃ law's witness a ghost of the machine, its law plain over it; then with each written law added.
//   GDP_ENGINE_DUMP=/tmp/wo.json bun research/protocols/run.ts --ms 60000 --only consensus_wo_decide --skip given,broken
//   bun research/protocols/engine/woprobe.ts /tmp/wo.json
import {readFileSync} from 'node:fs'
import {proveLaw, withWall} from '../../../kernel/prove.ts'
import {protocols} from '../models.ts'
const p = protocols.find(q => q.id === 'consensus_wo_decide')!, r: any = p.make(), human = p.human(r), kinds = r.kindLaws()
const {laws: set} = JSON.parse(readFileSync(process.argv[2]!, 'utf8'))
const ex = set.find((l: any) => l.some?.length), y = ex.some[0], g = ex.witness.ghost[y]
const m = r.machine, mg = {...m, state: {...m.state, [y]: g.start}, step: {...m.step, state: {...m.step.state, [y]: g.step}}}
const plain = set.map((l: any) => (l === ex ? {name: l.name, holds: l.holds} : l))
console.log('set', set.length, 'laws; the ∃ law:', ex.name.slice(0, 120))
const ask = (what: string, ls: any[], i: number, ms: number) => {
  const t = performance.now(), v: any = withWall(performance.now() + ms, () => { try { return proveLaw(mg, ls, i) } catch (e) { return {proven: false, stuck: String(e).slice(0, 100)} } })
  console.log(what, '→', v.proven ? 'proven' : `${v.stuck} at ${String(v.goal ?? '').slice(0, 100)}`, Math.round(performance.now() - t), 'ms')
  if (!v.proven && v.witness) console.log('  model:', Object.entries(v.witness).filter(([k, x]: any) => x && !k.startsWith('?') && !k.startsWith('k:')).map(([k, x]) => `${k}=${String(x)}`).slice(0, 60).join(' '))
  return v
}
const base = [...kinds, ...plain], ci = kinds.length, foralls = human.filter((h: any) => !h.some?.length && !JSON.stringify(h.holds).includes('"ex"'))
if (process.argv[3] === 'list') {
  for (const l of plain) console.log('  cube', l.name.replace(/every [^:]*: /, '').slice(0, 150))
  ask('caller from the set and every written ∀ law', [...base, ...foralls], ci, 120_000)
  process.exit(0)
}
ask('caller from the set', base, ci, 120_000)
for (const h of foralls) {
  ask(`  caller with written ${JSON.stringify(h.name)}`, [...base, h], ci, 60_000)
  ask(`  written ${JSON.stringify(h.name)}'s step from the set`, [...base, h], base.length, 30_000)
}
