// The run's table: `bun compare/term/summary.ts runs/modal/term/<name> [more run dirs, later rows replacing earlier]`.
// Per tool: the tasks answered terminates and nonterminating, the wrong ones, solved of all, the median seconds of those
// solved. No task here comes with a verdict, so an answer is wrong where another tool's opposite answer is certified:
// gdp-wired's terminates is a kernel-checked proof, its nonterminating a lasso ari.ts's evaluator replayed; LoAT's and
// KoAT2's answers carry no certificate this harness checks, so two of them disagreeing is listed as a conflict, not
// counted against either. For gdp-wired: why tasks were refused, the features of those translated, and where the
// unanswered ones stopped.
import {readFileSync} from 'node:fs'

type Stage = Record<string, unknown>
type Row = {tool: string, task: string, answer: string, seconds: number, stages?: Stage[], err?: string}
const dirs = process.argv.slice(2)
const byKey = new Map<string, Row>()
for (const d of dirs) for (const l of readFileSync(`${d}/results.jsonl`, 'utf8').split('\n').filter(Boolean)) { const r = JSON.parse(l) as Row; byKey.set(`${r.tool}\t${r.task}`, r) }
const rows = [...byKey.values()].filter(r => r.tool !== '?')
const tasks = (JSON.parse(readFileSync(`${dirs[0]}/tasks.json`, 'utf8')) as {task: string}[]).map(t => t.task)
const tools = [...new Set(rows.map(r => r.tool))]
const count = <T>(xs: T[], f: (x: T) => string) => { const m = new Map<string, number>(); for (const x of xs) m.set(f(x), (m.get(f(x)) ?? 0) + 1); return [...m].sort((a, b) => b[1] - a[1]) }
const decided = (a: string) => a === 'terminates' || a === 'nonterminating'
const certified = (r: Row) => r.tool === 'gdp' && decided(r.answer)
const perTask = new Map<string, Row[]>()
for (const r of rows) perTask.set(r.task, [...(perTask.get(r.task) ?? []), r])
const wrong = new Set<Row>(), conflicts: string[] = []
for (const [task, rs] of perTask) {
  const ds = rs.filter(r => decided(r.answer))
  if (new Set(ds.map(r => r.answer)).size < 2) continue
  const cert = ds.filter(certified)
  if (cert.length) { for (const r of ds) if (cert.some(c => c.answer !== r.answer)) wrong.add(r) } else conflicts.push(`${task}: ${ds.map(r => `${r.tool} ${r.answer}`).join(', ')}`)
}
const n = tasks.length
console.log(`${n} tasks; ${rows.length} rows\n`)
console.log('| tool | terminates | nonterminating | wrong | solved of ' + n + ' | median s (solved) | unknown | timeout | unsupported | error |')
console.log('| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |')
for (const tool of tools) {
  const rs = rows.filter(r => r.tool === tool), k = (a: string) => rs.filter(r => r.answer === a).length
  const right = rs.filter(r => decided(r.answer) && !wrong.has(r)), secs = right.map(r => r.seconds).sort((a, b) => a - b)
  const median = secs.length ? (secs.length % 2 ? secs[(secs.length - 1) / 2]! : Math.round((secs[secs.length / 2 - 1]! + secs[secs.length / 2]!) * 50) / 100) : '-'
  console.log(`| ${tool} | ${right.filter(r => r.answer === 'terminates').length} | ${right.filter(r => r.answer === 'nonterminating').length} | ${rs.filter(r => wrong.has(r)).length} | ${right.length} | ${median} | ${k('unknown')} | ${k('timeout')} | ${k('unsupported')} | ${k('error')} |`)
  if (rs.length !== n) console.log(`  (${tool}: ${rs.length} rows of ${n} tasks)`)
}
for (const w of wrong) console.log(`  WRONG ${w.tool} ${w.task}: ${w.answer}`)
for (const c of conflicts) console.log(`  CONFLICT (no certificate either way) ${c}`)
const solved = (tool: string) => new Set(rows.filter(r => r.tool === tool && decided(r.answer) && !wrong.has(r)).map(r => r.task))
const others = tools.filter(t => t !== 'gdp'), anyOther = new Set(others.flatMap(t => [...solved(t)]))
if (tools.includes('gdp')) {
  const mine = solved('gdp')
  console.log(`\nsolved by gdp-wired and by no other tool here: ${[...mine].filter(t => !anyOther.has(t)).length} ${JSON.stringify([...mine].filter(t => !anyOther.has(t)))}`)
  console.log(`solved by some other tool and not gdp-wired: ${[...anyOther].filter(t => !mine.has(t)).length}; by any tool: ${new Set([...mine, ...anyOther]).size}`)
  for (const o of others) {
    const s = solved(o)
    console.log(`  ${o}: terminates by ${o} and not by gdp-wired: ${rows.filter(r => r.tool === o && r.answer === 'terminates' && !wrong.has(r) && !mine.has(r.task)).length}; nonterminating by ${o} and not by gdp-wired: ${rows.filter(r => r.tool === o && r.answer === 'nonterminating' && !wrong.has(r) && !mine.has(r.task)).length}; gdp-wired's not ${o}'s: ${[...mine].filter(t => !s.has(t)).length}`)
  }
  const gdp = rows.filter(r => r.tool === 'gdp'), last = (r: Row, k: string) => r.stages?.findLast(s => s.stage === k)
  const imported = gdp.filter(r => last(r, 'import'))
  console.log(`\ngdp-wired: ${imported.length} translated, ${gdp.filter(r => r.answer === 'unsupported').length} refused`)
  console.log('refused:', count(gdp.filter(r => r.answer === 'unsupported'), r => String(last(r, 'answer')?.why).replace(/\d+/g, 'N')))
  console.log('features of those translated:', count(imported.flatMap(r => (last(r, 'import')!.features as string[]).length ? last(r, 'import')!.features as string[] : ['none']), x => x))
  console.log('answered by:', count(gdp.filter(r => decided(r.answer)), r => `${r.answer} by ${String(last(r, 'answer')?.by)}`))
  const why = (r: Row) => {
    const rk = last(r, 'rank')
    if (!rk) return `${r.answer} before the rank search (last: ${JSON.stringify(r.stages?.at(-1)?.stage ?? 'nothing')})`
    if (rk.error) return 'rank search threw'
    const w = typeof rk.why === 'string' ? rk.why : ''
    if (w.startsWith('no rank')) return 'no rank from the runs (linear or degree 2, in order)'
    if (w.includes('no invariant found')) return `a rank from the runs the kernel refused (goal: ${String(rk.goal).replace(/^.*halts: /, '').replace(/ @.*/, '')})`
    return w.replace(/\d+/g, 'N').slice(0, 80)
  }
  console.log('unanswered:', count(gdp.filter(r => !decided(r.answer) && r.answer !== 'unsupported'), r => `${r.answer}: ${why(r)}`))
  const errs = gdp.filter(r => r.answer === 'error')
  for (const r of errs.slice(0, 5)) console.log(`  error ${r.task}: ${r.err?.slice(-200)}`)
}
for (const o of tools.filter(t => t !== 'gdp')) for (const r of rows.filter(r => r.tool === o && r.answer === 'error').slice(0, 3)) console.log(`  error ${o} ${r.task}: ${r.err?.slice(-200)}`)
