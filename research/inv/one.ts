// One CHC task through inferLaws alone, as the second corpus runs it (a counted budget, no samples given), each phase's
// progress on a line: `bun research/inv/one.ts <task.smt2> [ms]`.
import {readFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import {inferLaws} from '../../core/infer.ts'

const [file, msArg] = process.argv.slice(2) as [string, string | undefined]
const b = build(parseChc(readFileSync(file, 'utf8'))), t0 = performance.now()
const v = inferLaws(b.rule, [b.law], [], {ms: Number(msArg ?? 60000), timed: !!process.env.TIMED, progress: (phase, info) => console.log(JSON.stringify({ms: Math.round(performance.now() - t0), phase, ...info}))})
console.log(JSON.stringify({ms: Math.round(performance.now() - t0), proven: v.proven && v.checked, found: v.found.map(f => f.text), ...(v.proven ? {} : {goal: v.goal, stuck: v.stuck}), stats: v.stats}))
