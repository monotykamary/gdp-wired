// Debugging: print the goals matching DUMP while proving a lemma of research/data/lemma.ts as a law.
import {sC} from './show.ts'
import {setProveDump} from '../../kernel/prove.ts'
const re = new RegExp(process.env.DUMP!)
let n = 0
setProveDump(g => { if (re.test(g.name) && n++ < Number(process.env.N ?? 1)) { console.log(`== ${g.name}`); g.hyps.forEach((h, i) => console.log(i, sC(h))) } })
await import('./lemma.ts')
