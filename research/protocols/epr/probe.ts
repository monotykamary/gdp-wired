// The EPR path on goals.ts' step goals: kernel/epr.ts's decision (against Z3's answer, given as sat/unsat), and for a
// refutation its core proven by the kernel's search, widened to the whole goal and checked.
//   bun research/protocols/epr/probe.ts <goal.json> [z3: sat|unsat] [--ms 20000]
import {readFileSync} from 'node:fs'
import {decide} from '../../../kernel/epr.ts'
import {clock, countLeaves, grow, widen} from '../../../kernel/prove.ts'
import {check} from '../../../kernel/kernel.ts'
const g = JSON.parse(readFileSync(process.argv[2]!, 'utf8')), z3 = process.argv[3], i = process.argv.indexOf('--ms'), ms = i < 0 ? 20_000 : Number(process.argv[i + 1])
const goal = {name: g.name, hyps: g.hyps}, t0 = performance.now(), d = decide(goal, g.patterns), td = performance.now() - t0
const line: Record<string, unknown> = {goal: g.name, hyps: goal.hyps.length, decideMs: Math.round(td)}
if ('unknown' in d) line.answer = `unknown (${d.unknown})`
else if (d.sat) line.answer = 'sat'
else {
  line.answer = 'unsat'; line.core = d.core.length
  const part = {name: g.name, hyps: d.core.includes(goal.hyps.length - 1) ? d.core.map(k => goal.hyps[k]!) : [...d.core.map(k => goal.hyps[k]!), goal.hyps.at(-1)!]}
  const t1 = performance.now(), out: any = grow(part, new Map(), {nodes: 0, until: clock() + ms})
  line.growMs = Math.round(performance.now() - t1)
  if ('tree' in out) { const t2 = performance.now(), tree = widen(part, goal, out.tree); line.widenMs = Math.round(performance.now() - t2); if (tree) { line.leaves = countLeaves(tree); line.checked = check(goal, tree) } else line.widen = 'failed' }
  else line.core_proof = `${out.stuck} ${(out.why ?? '').slice(0, 50)}`
}
if (z3) line.agrees = z3 === line.answer || String(line.answer).startsWith('unknown') ? (String(line.answer).startsWith('unknown') ? 'no answer' : true) : false
console.log(JSON.stringify(line))
