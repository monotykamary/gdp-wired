// The conjectures the search makes for a law of examples/data.ts: bun research/data/conj.ts <law>
import {laws} from '../../examples/data.ts'
import {conjectures, programOf, type DataLaw} from '../../core/data.ts'
const l = (laws as Record<string, () => DataLaw>)[process.argv[2]!]!()
const t = performance.now(), cs = conjectures(programOf([l]), l)
console.log(`${cs.length} conjectures, ${Math.round(performance.now() - t)} ms`)
for (const c of cs) console.log(' ', c.name)
