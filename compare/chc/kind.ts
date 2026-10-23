// k-induction beside solve.ts's other stages, on the container's second CPU: `bun compare/chc/kind.ts <task.smt2>
// --ms <budget> --parent <pid>`, started by solve.ts once the task is read. core/kind.ts's search, the law over
// k = 2, 3, ... steps in a row with the rule's kinds assumed, within --ms, counted and in wall time. Proven, and the
// kernel's checkKInduction passed, it stops solve.ts (whose answer would come later, if at all) and prints the answer
// as solve.ts would; else it prints its stage and ends, and solve.ts goes on.
import {readFileSync} from 'node:fs'
import {parseChc} from './chc.ts'
import {build} from './translate.ts'
import {proveKInduction} from '../../core/kind.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const t0 = performance.now(), budget = opt('--ms', 50_000), parent = opt('--parent', 0)
const say = (o: object) => console.log(JSON.stringify({task: file, ms: Math.round(performance.now() - t0), ...o}))
const b = build(parseChc(readFileSync(file, 'utf8')))
const kd = proveKInduction(b.rule.machine, b.rule.kindLaws(), b.law, {ms: budget, wall: t0 + budget})
if (kd.proven && kd.checked && parent) { try { process.kill(parent, 'SIGKILL') } catch { /* gone */ } }
say({stage: 'kind', proven: kd.proven, checked: kd.checked, ...(kd.k ? {k: kd.k} : {}), depths: kd.depths, ...(kd.why ? {why: kd.why.slice(0, 120)} : {})})
if (kd.proven && kd.checked) say({stage: 'answer', answer: 'sat', by: 'kind', k: kd.k})
