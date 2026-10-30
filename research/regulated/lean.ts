// The pilot's certificates (pilot.ts --out <dir>: <dir>/certs/<id>/*.json, interchange documents) as one Lean file
// for the Lean twin (lean-kernel/emit.ts's toLean: each machine's laws and step laws, its trees checked by Lean's own
// kernel through the twin's soundness theorems). The clauses in each document's meta go in as comments only.
//   bun research/regulated/lean.ts <dir>/certs <out.lean>
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type Document, fromInterchange} from '../../interchange/format.ts'
import {type LeanItem, toLean} from '../../lean-kernel/emit.ts'

const [dir, out] = process.argv.slice(2)
if (!dir || !out) throw new Error('bun research/regulated/lean.ts <certs dir> <out.lean>')
const items: LeanItem[] = [], notes: string[] = []
for (const sub of readdirSync(dir).sort()) for (const f of readdirSync(join(dir, sub)).filter(f => f.endsWith('.json')).sort()) {
  const doc = JSON.parse(readFileSync(join(dir, sub, f), 'utf8')) as Document, c = fromInterchange(doc)
  if (c.kind !== 'laws' && c.kind !== 'stepLaws') continue
  const id = `${sub}_${f.replace(/\.json$/, '')}`, meta = doc.meta as {law?: string, cites?: string[]}
  notes.push(`-- ${id}: ${meta.law ?? ''}`, ...(meta.cites ?? []).map(t => `--   cites ${t}`))
  items.push({id, machine: c.machine, laws: c.laws, ...(c.kind === 'stepLaws' ? {stepLaws: c.stepLaws} : {})})
}
writeFileSync(out, `${notes.join('\n')}\n${toLean(items, {title: 'the regulated pilot\'s proven laws'})}`)
console.log(`${items.length} certificates as Lean: ${out}`)
