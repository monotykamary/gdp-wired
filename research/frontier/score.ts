// The wall corpus's score: `bun research/frontier/score.ts [--track t] [--limit s] [--json out]`. Each item runs in a
// process of its own, today's prover and the track's search where it has one, each under the time limit (60 s). An
// item counts for the frontier only when its verdict is proven and checked by the kernel.
// `bun research/frontier/score.ts --one <id> <today|frontier>` is one run, its verdict as JSON.
import {writeFileSync} from 'node:fs'
import {corpus} from './corpus.ts'

const arg = (k: string) => { const i = process.argv.indexOf(k); return i < 0 ? undefined : process.argv[i + 1] }
const one = arg('--one')
if (one) {
  const item = corpus.find(i => i.id === one)!, how = process.argv[process.argv.indexOf('--one') + 2] as 'today' | 'frontier'
  const t = performance.now(), v = how === 'today' ? item.today() : item.frontier!()
  console.log(JSON.stringify({proven: v.proven, checked: v.checked, goal: v.goal, stuck: v.stuck, ms: Math.round(performance.now() - t)}))
  process.exit(0)
}

type Run = {proven: boolean, checked: boolean, ms: number, goal?: string, stuck?: string, timeout?: boolean, error?: string}
const limit = Number(arg('--limit') ?? 60) * 1000, track = arg('--track')
const run = (id: string, how: string): Run => {
  const t = performance.now()
  const p = Bun.spawnSync(['bun', import.meta.path, '--one', id, how], {timeout: limit, stdout: 'pipe', stderr: 'pipe'})
  const ms = Math.round(performance.now() - t)
  if (p.exitCode === null || p.signalCode) return {proven: false, checked: false, ms, timeout: true}
  try { return JSON.parse(p.stdout.toString().trim().split('\n').at(-1)!) as Run } catch { return {proven: false, checked: false, ms, error: p.stderr.toString().slice(-300)} }
}
const items = corpus.filter(i => !track || i.track === track), rows = []
const cell = (r?: Run) => (!r ? '-' : r.proven && r.checked ? `proven ${r.ms} ms` : r.timeout ? 'timeout' : r.error ? 'error' : 'not proven')
console.log('| item | removed | today | frontier |\n| --- | --- | --- | --- |')
for (const i of items) {
  const today = run(i.id, 'today'), frontier = i.frontier ? run(i.id, 'frontier') : undefined
  rows.push({id: i.id, track: i.track, today, frontier})
  console.log(`| ${i.id} | ${i.removed} | ${cell(today)} | ${cell(frontier)} |`)
}
const won = (r?: Run) => !!r && r.proven && r.checked
console.log(`\ntoday ${rows.filter(r => won(r.today)).length} / ${rows.length}, frontier ${rows.filter(r => won(r.frontier) || won(r.today)).length} / ${rows.length}`)
const out = arg('--json')
if (out) writeFileSync(out, JSON.stringify(rows, null, 1))
