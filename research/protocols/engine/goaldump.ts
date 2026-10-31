// Goals for goalbench.ts: a script run with the prover's root goals of GDP_DUMP_MIN hypotheses or more (kernel/prove.ts's
// setProveDump, the first GDP_DUMP_N) and core/counts.ts's step goals left unknown or with a model (countsDump), each
// a JSON line in $GDP_DUMP_TO. Research only (gen/laneG's profile).
//   GDP_DUMP_TO=/tmp/g.jsonl bun research/protocols/engine/goaldump.ts research/protocols/ic3syn/run.ts --ms 60000 --only firewall
import {appendFileSync} from 'node:fs'
import {setProveDump} from '../../../kernel/prove.ts'
import {countsDump} from '../../../core/counts.ts'

const to = process.env.GDP_DUMP_TO ?? '/tmp/goals.jsonl', min = Number(process.env.GDP_DUMP_MIN ?? 100), most = Number(process.env.GDP_DUMP_N ?? 8)
let n = 0
countsDump.on = goal => appendFileSync(to, `${JSON.stringify(goal)}\n`)
setProveDump(goal => { if (goal.hyps.length >= min && n++ < most) appendFileSync(to, `${JSON.stringify({goal: goal.name, hyps: goal.hyps})}\n`) })
process.argv.splice(1, 1)
await import(new URL(`../../../${process.argv[1]}`, import.meta.url).href)
