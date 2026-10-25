// Does a dev set's delta predict the full delta? Every pair of full runs in the main checkout's runs/ launched together
// (a `<x>mine<y>` directory beside its `<x>main<y>` or `<x>base<y>`), read as the bar reads them, each benchmark's full
// delta (solved here minus solved on main) against the delta the dev set predicts (gates/bar-dev.json's strata, each
// stratum's delta scaled by its count over its sample) and the raw delta on the dev set's tasks alone.
//
//   bun gates/bar-calibrate.ts [--dev gates/bar-dev.json] [--runs <main>/runs] [--json out.json]
import {existsSync, readFileSync, readdirSync, statSync, writeFileSync} from 'node:fs'
import {dirname, join} from 'node:path'
import {type Dev, VIEWS, jobLogs, pearson, predict, solvedCount} from './bar-lib.ts'

const arg = (k: string, d: string) => { const i = process.argv.indexOf(`--${k}`); return i < 0 ? d : process.argv[i + 1] ?? d }
const HERE = dirname(import.meta.path)
const MAIN = dirname(Bun.spawnSync(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'], {cwd: HERE}).stdout.toString().trim())
const RUNS = arg('runs', join(MAIN, 'runs'))
const dev = JSON.parse(readFileSync(arg('dev', join(HERE, 'bar-dev.json')), 'utf8')) as {views: Record<string, Dev>}
const TREE = join(HERE, '..')

// What a run directory holds: a compare runner's results (by its tasks' names and tools) or a corpus' job logs.
const FULL: Record<string, number> = {chc: 1406, its: 1239, 'its-scc': 1239, sv: 282, 'sv-scc': 282, tip: 492, rw: 311, f1: 134, f2: 94}
const ids = (corpus: string) => new Set(JSON.parse(Bun.spawnSync(['bun', '-e', `const {corpus} = await import('./research/${corpus}/corpus.ts'); console.log(JSON.stringify(corpus.map(i => i.id)))`], {cwd: TREE}).stdout.toString()) as string[])
const brokenOf = (corpus: string) => JSON.parse(Bun.spawnSync(['bun', '-e', `const {corpus} = await import('./research/${corpus}/corpus.ts'); console.log(JSON.stringify(corpus.filter(i => i.broken).map(i => i.id)))`], {cwd: TREE}).stdout.toString()) as string[]
const F1 = ids('frontier'), F2 = ids('frontier2'), BROKEN = new Set([...brokenOf('frontier'), ...brokenOf('frontier2')])
function kinds(dir: string): string[] {
  if (existsSync(join(dir, 'results.jsonl'))) {
    const head = readFileSync(join(dir, 'results.jsonl'), 'utf8').slice(0, 200_000).split('\n').filter(Boolean).slice(0, 400).flatMap(l => { try { return [JSON.parse(l) as {tool: string, task: string}] } catch { return [] } })
    const t = head.find(r => r.tool === 'gdp')?.task ?? ''
    const scc = head.some(r => r.tool === 'gdp-scc')
    if (t.endsWith('.ari')) return scc ? ['its', 'its-scc'] : ['its']
    if (t.endsWith('.smt2')) return ['tip']
    if (t.endsWith('.yml')) return t.startsWith('termination-') ? (scc ? ['sv', 'sv-scc'] : ['sv']) : ['chc']
    return []
  }
  const logs = readdirSync(dir).filter(f => f.endsWith('.log'))
  if (logs.length < 80) return []
  const keys = jobLogs(dir).map(l => l.key)
  if (keys.filter(k => /#\d+$/.test(k)).length > 250) return ['rw']
  if (keys.filter(k => F1.has(k)).length > 200) return ['f1']
  if (keys.filter(k => F2.has(k)).length > 150) return ['f2']
  return []
}
const parse = (view: string, dir: string) => {
  const rows = VIEWS[view]!.parse(dir, TREE)
  if (view === 'f1' || view === 'f2') for (const [id, o] of rows) if (BROKEN.has(id)) rows.set(id, {...o, answer: `broken: ${o.answer}`, solved: o.answer !== 'proven', wrong: o.answer === 'proven'})
  return rows
}

// The pairs: siblings whose names differ only in mine against main or base.
const pairs: {view: string, mine: string, main: string}[] = []
const walk = (d: string, depth: number) => {
  let names: string[]
  try { names = readdirSync(d).filter(n => { try { return statSync(join(d, n)).isDirectory() } catch { return false } }) } catch { return }
  for (const n of names) {
    if (!n.includes('mine') || n.includes('trees') || n === 'bar') continue
    for (const other of ['main', 'base']) {
      const m = n.replace('mine', other)
      if (!names.includes(m)) continue
      for (const v of kinds(join(d, n))) if (kinds(join(d, m)).includes(v)) pairs.push({view: v, mine: join(d, n), main: join(d, m)})
    }
  }
  if (depth > 0) for (const n of names) if (n !== 'bar' && n !== 'trees' && !n.includes('mine') && !n.includes('main') && !n.includes('base')) walk(join(d, n), depth - 1)
}
walk(RUNS, 3)

const out: Record<string, unknown> = {}
console.log('| benchmark | dev set | pairs | r (predicted, full) | r (raw, full) | mean abs error of the prediction | full deltas seen |')
console.log('| --- | --- | --- | --- | --- | --- | --- |')
for (const view of Object.keys(dev.views)) {
  const d = dev.views[view]!, rows: {pair: string, full: number, scaled: number, raw: number}[] = []
  for (const p of pairs.filter(x => x.view === view)) {
    const a = parse(view, p.mine), b = parse(view, p.main)
    if (a.size < 0.95 * FULL[view]! || b.size < 0.95 * FULL[view]!) continue
    const both = new Set([...a.keys()].filter(t => b.has(t)))
    const full = solvedCount(a, both) - solvedCount(b, both), pr = predict(d, a, b)
    rows.push({pair: `${p.mine.slice(RUNS.length + 1)} vs ${p.main.split('/').at(-1)}`, full, scaled: pr.scaled, raw: pr.raw})
  }
  const r = pearson(rows.map(x => x.scaled), rows.map(x => x.full)), rr = pearson(rows.map(x => x.raw), rows.map(x => x.full))
  const mae = rows.length ? rows.reduce((s, x) => s + Math.abs(x.scaled - x.full), 0) / rows.length : NaN
  const fulls = rows.map(x => x.full).sort((x, y) => x - y)
  console.log(`| ${view} | ${d.size} of ${d.of} | ${rows.length} | ${r.toFixed(3)} | ${rr.toFixed(3)} | ${mae.toFixed(1)} | ${fulls.length ? `${fulls[0]} to ${fulls.at(-1)}` : '-'} |`)
  out[view] = {size: d.size, of: d.of, pairs: rows, r, rRaw: rr, mae}
}
const json = arg('json', '')
if (json) writeFileSync(json, JSON.stringify(out, null, 1))
