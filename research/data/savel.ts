// Debugging: save the first goal matching DUMP of a law of examples/data.ts (lemmas off, depth argv[3]) to SAVE.
import {writeFileSync} from 'node:fs'
import {setProveDump} from '../../kernel/prove.ts'
import {laws} from '../../examples/data.ts'
import {proveData, type DataLaw} from '../../core/data.ts'
const re = new RegExp(process.env.DUMP!)
let done = false
setProveDump(g => { if (!done && re.test(g.name)) { done = true; writeFileSync(process.env.SAVE!, JSON.stringify(g)) } })
proveData((laws as Record<string, () => DataLaw>)[process.argv[2]!]!(), {lemmas: false, depth: Number(process.argv[3] ?? 2), ms: 30000})
