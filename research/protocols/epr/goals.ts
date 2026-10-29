import {writeFileSync} from 'node:fs'
import {lawInstances} from '../../../kernel/prove.ts'
import {obligations} from '../../../kernel/kernel.ts'
import {protocols} from '../../../research/protocols/models.ts'
const [id, dir] = process.argv.slice(2), p = protocols.find(q => q.id === id)!, r = p.make()
const laws = [...r.kindLaws(), ...p.human(r), ...p.laws(r)], m = r.machine
laws.forEach((l, i) => {
  if (l.name.startsWith('every ') && l.name.endsWith('of its kind')) return
  const g = obligations(m, laws, {[l.name]: lawInstances(m, laws, i)}, i).find(x => x.name.endsWith('@step'))!
  const f = `${dir}/${id}-${i}.json`; writeFileSync(f, JSON.stringify(g)); console.log(f, g.name, g.hyps.length)
})
