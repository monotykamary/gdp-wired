// Print the first goal of a law of examples/data.ts and its outcome: bun research/data/dump.ts <law> [depth] [scheme#]
import {sC} from './show.ts'
import {setProveDump} from '../../kernel/prove.ts'
import {laws} from '../../examples/data.ts'
import {proveData, type DataLaw} from '../../core/data.ts'
let n = 0
const which = Number(process.argv[4] ?? 0)
setProveDump(g => { if (n++ === which) { console.log(`== ${g.name}`); g.hyps.forEach((h, i) => console.log(i, sC(h))) } })
const l = (laws as Record<string, () => DataLaw>)[process.argv[2]!]!()
const v = proveData(l, {depth: Number(process.argv[3] ?? 1), lemmas: false, ms: 15000})
console.log(JSON.stringify({proven: v.proven, ms: v.ms, goal: v.goal, stuck: v.stuck, scheme: v.scheme}))
