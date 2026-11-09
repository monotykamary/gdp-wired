// Which of the census protocols run their generation on the compiled step, and why the rest fall back to the interpreter
// (compileJs's refusal, or a history). Reads only the protocol table; proves nothing.
import {protocols} from '../protocols/ic3syn/models.ts'
import {guardLaws} from '../../core/counts.ts'
import {compileJs, fastStep} from '../../core/machine.ts'
const only = process.argv[2]?.split(',')
for (const p of protocols.filter(p => !only || only.includes(p.id))) {
  const r = p.make(), g = guardLaws(r.machine), m = {...r.machine, counts: {...r.machine.counts, ...g.counts}}
  let why = ''
  try { compileJs({...m, counts: undefined}) } catch (e) { why = (e as Error).message.replace(`${m.name}: `, '') }
  const every = Object.entries(m.step.maps ?? {}).filter(([, w]) => 'each' in w).map(([n]) => n)
  console.log(JSON.stringify({id: p.id, fast: !!fastStep(m), history: !!m.history, counts: Object.keys(m.counts ?? {}).length, everyWrites: every, why}))
}
