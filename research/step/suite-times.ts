// Suite job times side by side: `bun research/step/suite-times.ts <out dir> <out dir> [...]` (each a supercomputer run's
// output: summary.tsv with name, exit or `lost`, seconds, box). Prints each run's failures and total job seconds over
// the jobs every run has, then the jobs whose time moved most between the first two.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'

type Row = {code: number; secs: number; box: string}
const runs = process.argv.slice(2).map(d => {
  const rows = new Map<string, Row>()
  for (const line of readFileSync(join(d, 'summary.tsv'), 'utf8').split('\n')) {
    const [name, code, secs, box = ''] = line.split('\t')
    if (name && secs !== undefined && /^-?\d+$/.test(code ?? '')) rows.set(name, {code: Number(code), secs: Number(secs), box}) // (not the header, nor a lost job)
  }
  return {d, rows}
})
if (!runs.length) { console.error('usage: bun research/step/suite-times.ts <out dir> <out dir> [...]'); process.exit(2) }
const common = [...runs[0]!.rows.keys()].filter(n => runs.every(r => r.rows.has(n)))
const total = (xs: number[]) => Math.round(xs.reduce((a, b) => a + b, 0) * 10) / 10
for (const {d, rows} of runs) {
  const failed = [...rows].filter(([, r]) => r.code !== 0).map(([n]) => n).sort()
  const boxes = new Set([...rows.values()].map(r => r.box)).size
  console.log(`${d}: ${rows.size} jobs, failed ${JSON.stringify(failed)}, on ${boxes} boxes, job seconds over the ${common.length} common: ${total(common.map(n => rows.get(n)!.secs))} (all: ${total([...rows.values()].map(r => r.secs))})`)
}
if (runs.length >= 2) {
  const a = runs[0]!.rows, b = runs[1]!.rows
  const moved = [...common].sort((x, y) => (b.get(x)!.secs - a.get(x)!.secs) - (b.get(y)!.secs - a.get(y)!.secs))
  const show = (ns: string[]) => JSON.stringify(ns.map(n => [n, a.get(n)!.secs, b.get(n)!.secs]))
  console.log('most slower:', show(moved.slice(-10).reverse()))
  console.log('most faster:', show(moved.slice(0, 6)))
}
