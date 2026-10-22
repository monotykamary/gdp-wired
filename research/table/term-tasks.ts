// The termination tasks for the table's Q3 test, each with compare/term/failures.ts's class (the same labels, the same
// reading of the runs): `bun research/table/term-tasks.ts <runs/modal/term dir>` writes research/table/jobs/term-tasks.json
// ({its: {task: class}, sv: {task: class}}) and the task lists term-its.txt, term-sv.txt beside it.
import {readFileSync, writeFileSync} from 'node:fs'

type Row = {tool: string, task: string, answer: string, stages?: Record<string, unknown>[], out?: string}
const root = process.argv[2]!
const read = (d: string): Row[] => readFileSync(`${root}/${d}/results.jsonl`, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as Row)
function classes(koatDir: string | undefined, dirs: string[]): Record<string, string> {
  const rows = new Map<string, Row>()
  for (const d of dirs) for (const r of read(d)) rows.set(`${r.tool}\t${r.task}`, r)
  const get = (tool: string, task: string) => rows.get(`${tool}\t${task}`), ans = (tool: string, task: string) => get(tool, task)?.answer
  const koat = new Map(koatDir ? read(koatDir).map(r => [r.task, r]) : [])
  const depth = (out: string) => Math.max(0, ...[...out.matchAll(/of depth (\d+)/g)].map(m => Number(m[1])))
  const sccWhy = (task: string): string => {
    const r = get('gdp-scc', task)
    if (!r) return 'no gdp-scc row'
    if (r.answer === 'timeout') return 'out of time'
    const last = r.stages?.filter(s => s.stage === 'rank').at(-1)
    if (!last) return r.answer === 'unknown' ? 'out of time, or the search threw' : `no rank stage (${r.answer})`
    if (last.error) return 'out of time, or the search threw'
    const why = typeof last.why === 'string' ? last.why : ''
    const m = /drops on every turn of (\d+) sampled/.exec(why)
    if (m) return Number(m[1]) === 0 ? 'no turn sampled' : 'no rank fits the sampled turns'
    if (why.includes('no invariant found')) return /\ba\d+(\$n)?\b/.test(String(last.rank)) ? 'a rank fitted to the params' : 'a rank the kernel refused, no param read'
    return why.slice(0, 60) || 'other'
  }
  const out: Record<string, string> = {}
  for (const t of new Set([...rows.values()].map(r => r.task))) {
    const ours = (a?: string) => a === 'terminates' || a === 'nonterminating'
    if (ours(ans('gdp', t)) || ours(ans('gdp-scc', t)) || ans('gdp', t) === 'unsupported') continue
    if (!['koat2', 'loat', 'loat-abmc', 'uautomizer'].some(o => ans(o, t) === 'terminates')) continue
    const k = koat.get(t), d = k?.answer === 'terminates' ? depth(k.out ?? '') : 0
    const by = k?.answer === 'terminates' || !koatDir ? '' : ' (KoAT2 gave no proof; another tool did)'
    out[t] = d >= 2 ? `multiphase rank (KoAT2's MPRF of depth ${d})` : `${sccWhy(t)}${by}`
  }
  return out
}
const its = classes('diag-koat', ['full1', 'koat-fix1', 'gdp2']), sv = classes(undefined, ['sv2', 'sv3'])
writeFileSync('research/table/jobs/term-tasks.json', JSON.stringify({its, sv}, null, 1) + '\n')
writeFileSync('research/table/jobs/term-its.txt', Object.keys(its).join('\n') + '\n')
writeFileSync('research/table/jobs/term-sv.txt', Object.keys(sv).join('\n') + '\n')
const count = (m: Record<string, string>) => Object.entries(Object.values(m).reduce((a: Record<string, number>, c) => ((a[c] = (a[c] ?? 0) + 1), a), {})).sort((a, b) => b[1] - a[1])
console.log('its', Object.keys(its).length, count(its))
console.log('sv', Object.keys(sv).length, count(sv))
