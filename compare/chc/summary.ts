// The run's table: `bun compare/chc/summary.ts runs/modal/chc/<name>`. Per tool, the tasks answered sat and unsat, the
// wrong answers (against the task's expected verdict, where some tool decided it at CHC-COMP'26), the rest; for
// gdp-wired, the stage each answer came from, why tasks were refused and the stage the unanswered ones reached. A task
// whose label a checked derivation refutes (compare/chc/disputed.json: the label from one vote or a placeholder, the
// derivation confirmed by checkDerivation and by a simulation of the clauses) is counted neither right nor wrong where
// a tool answers it as the derivation does: `disputed`, listed with the label's source.
import {readFileSync} from 'node:fs'

type Row = {tool: string, task: string, answer: string, seconds: number, expected: string, stages?: Record<string, unknown>[], err?: string}
const dir = process.argv[2]!
const rows: Row[] = readFileSync(`${dir}/results.jsonl`, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l))
const votes = new Map<string, string | null>((JSON.parse(readFileSync(`${dir}/tasks.json`, 'utf8')) as {task: string, vote: string | null}[]).map(t => [t.task, t.vote]))
const disputes = JSON.parse(readFileSync(new URL('./disputed.json', import.meta.url), 'utf8')) as Record<string, {label: string, vote: string, from: string, answer: string, steps: number, derivation: string}>
const disputed = (r: Row) => disputes[r.task]?.answer === r.answer
const decided = (r: Row) => votes.get(r.task) != null
const tools = [...new Set(rows.map(r => r.tool))]
const count = <T>(xs: T[], f: (x: T) => string) => { const m = new Map<string, number>(); for (const x of xs) m.set(f(x), (m.get(f(x)) ?? 0) + 1); return [...m].sort((a, b) => b[1] - a[1]) }

console.log(`| tool | tasks | sat | unsat | wrong | disputed | unknown | timeout | unsupported | error | median s (answered) |`)
console.log(`| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |`)
for (const tool of tools) {
  const rs = rows.filter(r => r.tool === tool), n = (a: string) => rs.filter(r => r.answer === a).length
  const answered = rs.filter(r => r.answer === 'sat' || r.answer === 'unsat'), open = answered.filter(disputed)
  const right = answered.filter(r => !disputed(r) && (!decided(r) || r.answer === r.expected))
  const wrong = answered.filter(r => !disputed(r) && decided(r) && r.answer !== r.expected)
  const secs = right.map(r => r.seconds).sort((a, b) => a - b)
  console.log(`| ${tool} | ${rs.length} | ${right.filter(r => r.answer === 'sat').length} | ${right.filter(r => r.answer === 'unsat').length} | ${wrong.length} | ${open.length} | ${n('unknown')} | ${n('timeout')} | ${n('unsupported')} | ${n('error')} | ${secs.length ? secs[Math.floor(secs.length / 2)] : '-'} |`)
  for (const w of wrong) console.log(`  WRONG ${tool} ${w.task}: answered ${w.answer}, expected ${w.expected} (${votes.get(w.task)})`)
  for (const d of open) { const x = disputes[d.task]!; console.log(`  DISPUTED ${tool} ${d.task}: answered ${d.answer}, labelled ${x.label} (vote: ${x.vote}); disputed (label from ${x.from}, our derivation checked) (${x.steps} steps, ${x.derivation})`) }
}
const gdp = rows.filter(r => r.tool === 'gdp')
if (gdp.length) {
  const last = (r: Row, k: string) => r.stages?.findLast(s => s.stage === k)
  console.log('\ngdp-wired, answered by:', count(gdp.filter(r => r.answer === 'sat' || r.answer === 'unsat'), r => `${r.answer} by ${String(last(r, 'answer')?.by)}`))
  console.log('refused:', count(gdp.filter(r => r.answer === 'unsupported'), r => String(last(r, 'answer')?.why).replace(/: .*/, '').replace(/\d+/g, 'N')))
  console.log('unanswered, last stage:', count(gdp.filter(r => r.answer === 'unknown' || r.answer === 'timeout' || r.answer === 'error'), r => `${r.answer} after ${(r.stages?.filter(s => s.stage !== 'answer').at(-1)?.stage as string | undefined) ?? 'nothing'}`))
  console.log('houdini:', count(gdp.filter(r => last(r, 'houdini')), r => `${last(r, 'houdini')!.proven ? 'proven' : String(last(r, 'houdini')!.why)}`))
  const others = tools.filter(t => t !== 'gdp')
  const solved = (tool: string) => new Set(rows.filter(r => r.tool === tool && (r.answer === 'sat' || r.answer === 'unsat') && (!decided(r) || r.answer === r.expected)).map(r => r.task))
  const mine = solved('gdp'), anyOther = new Set(others.flatMap(t => [...solved(t)]))
  console.log(`solved by gdp-wired and no other tool here: ${[...mine].filter(t => !anyOther.has(t)).length}; by some other tool and not gdp-wired: ${[...anyOther].filter(t => !mine.has(t)).length}`)
  for (const r of gdp.filter(r => r.answer === 'error').slice(0, 5)) console.log(`  error ${r.task}: ${r.err?.slice(-300)}`)
}
