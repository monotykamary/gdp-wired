// Debugging: print the goals matching DUMP of a law of examples/data.ts proven with lemmas given.
import {sC} from './show.ts'
import {setProveDump} from '../../kernel/prove.ts'
const re = new RegExp(process.env.DUMP!)
let n = 0
const skip = Number(process.env.SKIP ?? 0)
setProveDump(g => { if (re.test(g.name) && n++ < Number(process.env.N ?? 1) + skip && n > skip) { console.log(`== ${g.name}`); g.hyps.forEach((h, i) => console.log(i, sC(h))) } })
await import('./withlemma.ts')
