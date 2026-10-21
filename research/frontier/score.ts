// The wall corpus's score: `bun research/frontier/score.ts [--track t] [--not t] [--shard i/n] [--limit s] [--json out]`. Each item runs in a
// process of its own, today's prover and the track's search where it has one, each under the time limit (60 s). An
// item counts for the frontier only when its verdict is proven and checked by the kernel.
// `bun research/frontier/score.ts --one <id> <today|frontier>` is one run, its verdict as JSON; `--from <dir>` reads a Modal
// run of those (jobs.ts).
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {corpus} from './corpus.ts'

const arg = (k: string) => { const i = process.argv.indexOf(k); return i < 0 ? undefined : process.argv[i + 1] }
const one = arg('--one')
if (one) {
  const item = corpus.find(i => i.id === one)!, how = process.argv[process.argv.indexOf('--one') + 2] as 'today' | 'frontier'
  const t = performance.now(), v = how === 'today' ? item.today() : item.frontier!()
  const found = foundText(v)
  console.log(JSON.stringify({proven: v.proven, checked: v.checked, goal: v.goal, stuck: v.stuck, ms: Math.round(performance.now() - t), ...(found?.length ? {found} : {})}))
  process.exit(0)
}

type Run = {proven: boolean, checked: boolean, ms: number, goal?: string, stuck?: string, found?: string[], timeout?: boolean, error?: string}
// What a search found, as text: inferLaws' list, or a verdict's `found` (laws, lemmas, facts, a rank).
function foundText(v: unknown): string[] | undefined {
  const f = (v as {found?: unknown}).found
  if (Array.isArray(f)) return f.map(x => (x as {text: string}).text)
  if (!f || typeof f !== 'object') return undefined
  const o = f as {laws?: {text: string}[], lemmas?: Record<string, {lemmas?: string[], between?: string[]}>, facts?: string[], rank?: string}
  return [...(o.rank ? [`rank ${o.rank}`] : []), ...(o.laws ?? []).map(l => l.text), ...Object.entries(o.lemmas ?? {}).flatMap(([n, l]) => [...(l.lemmas ?? []), ...(l.between ?? [])].map(t => `${n}: ${t}`)), ...(o.facts ?? [])]
}
const cell = (r?: Run, broken?: boolean) => (!r ? '-' : r.proven && r.checked ? `proven ${r.ms} ms` : r.timeout ? 'timeout' : r.error ? 'error' : broken ? `refused ${r.ms} ms` : 'not proven')

// `--from <dir>`: the table from a Modal run of jobs.ts's jobs (each log: the item's id, then its verdict).
const from = arg('--from')
if (from) {
  const runs = new Map<string, Record<string, Run>>()
  for (const f of readdirSync(from).filter(f => f.endsWith('.log'))) {
    const lines = readFileSync(`${from}/${f}`, 'utf8').trim().split('\n'), how = f.replace(/\.log$/, '').split('-').at(-1)!
    let r: Run
    try { r = JSON.parse(lines.at(-1)!) as Run } catch { r = {proven: false, checked: false, ms: 0, timeout: true} }
    runs.set(lines[0]!, {...runs.get(lines[0]!), [how]: r})
  }
  console.log('| item | today | frontier | found |\n| --- | --- | --- | --- |')
  for (const i of corpus.filter(i => runs.has(i.id))) { const r = runs.get(i.id)!; console.log(`| ${i.id} | ${cell(r.today, !!i.broken)} | ${cell(r.frontier, !!i.broken)} | ${r.frontier?.found?.join('; ') ?? ''} |`) }
  tally(corpus.filter(i => runs.has(i.id)).map(i => ({broken: !!i.broken, ...runs.get(i.id)!})))
  process.exit(0)
}
const limit = Number(arg('--limit') ?? 60) * 1000, track = arg('--track')
const run = (id: string, how: string): Run => {
  const t = performance.now()
  const p = Bun.spawnSync(['bun', import.meta.path, '--one', id, how], {timeout: limit, stdout: 'pipe', stderr: 'pipe'})
  const ms = Math.round(performance.now() - t)
  if (p.exitCode === null || p.signalCode) return {proven: false, checked: false, ms, timeout: true}
  try { return JSON.parse(p.stdout.toString().trim().split('\n').at(-1)!) as Run } catch { return {proven: false, checked: false, ms, error: p.stderr.toString().slice(-300)} }
}
// `--not <track>` leaves a track out (one with jobs of its own); `--shard i/n` runs every n-th item from the i-th.
const not = arg('--not'), shard = arg('--shard')?.split('/').map(Number)
const items = corpus.filter(i => (!track || i.track === track) && i.track !== not).filter((_, j) => !shard || j % shard[1]! === shard[0]!), rows = []
console.log('| item | removed | today | frontier |\n| --- | --- | --- | --- |')
for (const i of items) {
  const today = run(i.id, 'today'), frontier = i.frontier ? run(i.id, 'frontier') : undefined
  rows.push({id: i.id, track: i.track, broken: !!i.broken, today, frontier})
  console.log(`| ${i.id} | ${i.removed} | ${cell(today, !!i.broken)} | ${cell(frontier, !!i.broken)} |`)
}
tally(rows)
// The score: items proven, today and with the frontier's search; a broken variant counts when neither proves it.
function tally(rows: {broken: boolean, today?: Run, frontier?: Run}[]) {
  const won = (r?: Run) => !!r && r.proven && r.checked, laws = rows.filter(r => !r.broken), broken = rows.filter(r => r.broken)
  console.log(`\ntoday ${laws.filter(r => won(r.today)).length} / ${laws.length}, frontier ${laws.filter(r => won(r.frontier) || won(r.today)).length} / ${laws.length}`)
  if (broken.length) console.log(`broken variants refused: today ${broken.filter(r => !won(r.today)).length} / ${broken.length}, frontier ${broken.filter(r => !won(r.today) && !won(r.frontier)).length} / ${broken.length}`)
}
const out = arg('--json')
if (out) writeFileSync(out, JSON.stringify(rows, null, 1))
