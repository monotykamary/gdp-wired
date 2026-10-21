// Debugging: save the first goal matching DUMP (of a law proven with lemmas given) to SAVE as JSON.
import {writeFileSync} from 'node:fs'
import {setProveDump} from '../../kernel/prove.ts'
const re = new RegExp(process.env.DUMP!)
let done = false
setProveDump(g => { if (!done && re.test(g.name)) { done = true; writeFileSync(process.env.SAVE!, JSON.stringify(g)) } })
await import('./withlemma.ts')
