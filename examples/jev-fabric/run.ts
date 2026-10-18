// Proves every law in laws.ts, times each proof, and holds each to gdp-wired's triple check (examples/harness.ts):
// the kernel accepts the proof, random runs of the interpreter and the compiled rule agree and keep the law, and the
// broken variant is refused by the kernel and broken by a real run (or draw).
//   bun examples/jev-fabric/run.ts [--json out.json]
// With --lean, every law as a Lean theorem instead (each decision's goal, each machine through the twin), for lean-kernel:
//   bun examples/jev-fabric/run.ts --lean > lean-kernel/JevFabric.lean
import {writeFileSync} from 'node:fs'
import {proveDecision, proveSteps} from '../../core/dsl.ts'
import {type LeanItem, toLean} from '../../lean-kernel/emit.ts'
import {checkCase} from '../harness.ts'
import {type Entry, bendLaws, extras} from './laws.ts'

if (process.argv.includes('--lean')) {
  const items: LeanItem[] = []
  for (const [i, e] of [...bendLaws, ...extras].entries()) {
    const c = e.case(), id = `${e.n ? `law${e.n}` : `extra${i - bendLaws.length + 1}`}`
    if (c.kind === 'decisions') c.decisions.forEach((d, j) => items.push({id: `${id}_${j}`, goal: d.goal}))
    else if (c.kind === 'rule') items.push({id, machine: c.rule.machine, laws: c.laws, stepLaws: c.steps ?? []})
  }
  console.log(toLean(items, {title: "jev-fabric's laws (examples/jev-fabric)"}))
  process.exit(0)
}

type Row = {n: number, law: string, kind: string, encoding: string, how: string, proven: boolean, checked: boolean, ms: number, runs: string, builders: string, brokenRefused: boolean, brokenRun: string, ok: boolean}

function check(e: Entry): Row {
  const c = e.case()
  // The proof alone, timed (median of five).
  const times: number[] = []
  let proven = false, checked = false
  for (let i = 0; i < 5; i++) {
    const t0 = performance.now()
    const v = c.kind === 'decisions' ? proveDecision(c.decisions[0]!) : c.kind === 'rule' ? proveSteps(c.rule, c.laws, c.steps ?? []) : undefined
    times.push(performance.now() - t0)
    proven = !!v?.proven; checked = !!v?.checked
  }
  times.sort((a, b) => a - b)
  const findings = checkCase(c)
  const runs = findings.find(f => f.check === 'runs')
  // The builders, for the rule and its broken variant: each callback against what was built from it.
  const builders = findings.filter(f => f.check === 'builders'), buildersOk = builders.length > 0 && builders.every(f => f.ok)
  const own = c.kind === 'rule' ? 'laws' : c.kind === 'decisions' ? c.decisions[0]!.name : ''
  const refused = findings.filter(f => f.check === 'kernel' && f.item !== own)
  const brokenKernel = refused.length > 0 && refused.every(f => f.ok)
  const brokenRuns = findings.filter(f => f.check === 'counterexample')
  let brokenRun = brokenRuns.map(f => `${f.item}: ${f.detail}`).join('; ')
  let brokenOk = brokenRuns.length > 0 && brokenRuns.every(f => f.ok)
  // Where random draws cannot reach the break (values past 2^32), the given witness is evaluated on the broken rule.
  if (!brokenOk && e.witness) {
    const w = e.witness()
    brokenOk = brokenKernel && w.breaks
    brokenRun = `${brokenRun} → given witness: ${w.breaks ? 'broken' : 'NOT broken'}, ${w.detail}`
  }
  const row: Row = {
    n: e.n, law: e.bend, kind: e.kind, encoding: e.encoding, how: e.how ?? 'automatic', proven, checked, ms: times[2]!,
    runs: runs ? runs.detail : '', builders: builders.filter(f => !f.ok).map(f => f.detail).join('; ') || `${builders.length} agree`, brokenRefused: brokenKernel, brokenRun, ok: false,
  }
  row.ok = proven && checked && !!runs?.ok && buildersOk && brokenKernel && brokenOk
  return row
}

const rows: Row[] = []
const t0 = performance.now()
for (const e of [...bendLaws, ...extras]) {
  let r: Row
  try { r = check(e) } catch (err) { r = {n: e.n, law: e.bend, kind: e.kind, encoding: e.encoding, how: e.how ?? '', proven: false, checked: false, ms: 0, runs: `ERROR ${(err as Error).message}`, builders: '', brokenRefused: false, brokenRun: '', ok: false} }
  rows.push(r)
  console.log(`${r.ok ? 'ok  ' : 'FAIL'} ${String(r.n || '+').padStart(2)} ${r.law.padEnd(68)} ${r.proven ? (r.checked ? 'proven' : 'KERNEL REJECTS') : 'NOT PROVEN'} ${r.ms.toFixed(1)} ms | broken: ${r.brokenRefused ? 'refused' : 'NOT REFUSED'}${r.ok ? '' : `\n       runs: ${r.runs}\n       builders: ${r.builders}\n       broken: ${r.brokenRun}`}`)
}
const bend = rows.filter(r => r.n > 0), extra = rows.filter(r => r.n === 0)
const count = (rs: Row[], f: (r: Row) => boolean) => rs.filter(f).length
console.log(`\nBend laws: ${count(bend, r => r.proven && r.checked)} / ${bend.length} proven (${count(bend, r => r.ok)} with runs and broken variant), extras: ${count(extra, r => r.proven && r.checked)} / ${extra.length}`)
console.log(`proof times: Bend laws median ${median(bend.map(r => r.ms)).toFixed(1)} ms, max ${Math.max(...bend.map(r => r.ms)).toFixed(1)} ms, sum ${bend.reduce((a, r) => a + r.ms, 0).toFixed(0)} ms; extras sum ${extra.reduce((a, r) => a + r.ms, 0).toFixed(0)} ms; whole check ${((performance.now() - t0) / 1000).toFixed(1)} s`)
function median(xs: number[]) { const s = [...xs].sort((a, b) => a - b); return s[Math.floor(s.length / 2)] ?? 0 }
const out = process.argv.indexOf('--json')
if (out > 0) writeFileSync(process.argv[out + 1]!, JSON.stringify(rows, null, 1))
if (rows.some(r => !r.ok)) process.exit(1)
