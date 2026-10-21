// The cyclic route against the usual one, from a run's `cyclic: {...}` lines (modal/run.py --cyclic):
// `bun research/cyclic/ratios.ts <run dir> [--prefix base-]`, per kind: proofs compared, the usual and the cyclic ms,
// their ratio, the comparisons left uncovered and those that differ; machines also without the normalized scope.
import {readdirSync, readFileSync} from 'node:fs'
const dir = process.argv[2]!, prefix = process.argv.includes('--prefix') ? process.argv[process.argv.indexOf('--prefix') + 1]! : ''
const by: Record<string, {n: number, usual: number, cyclic: number, uncovered: number, differ: string[]}> = {}
for (const f of readdirSync(dir).filter(f => f.endsWith('.log') && (prefix ? f.startsWith(prefix) : !f.startsWith('base-')))) for (const line of readFileSync(`${dir}/${f}`, 'utf8').split('\n')) {
  if (!line.startsWith('cyclic: {')) continue
  let x: {kind: string, name: string, usual: boolean, cyclic?: boolean, ms?: number, usualMs?: number, uncovered?: boolean}
  try { x = JSON.parse(line.slice(8)) } catch { continue }
  for (const kind of [x.kind, ...(x.kind === 'machine' && x.name !== 'normalized scope' ? ['machine, but the normalized scope'] : [])]) {
    const b = (by[kind] ??= {n: 0, usual: 0, cyclic: 0, uncovered: 0, differ: []})
    if (x.uncovered) { b.uncovered++; continue }
    b.n++; b.usual += x.usualMs ?? 0; b.cyclic += x.ms ?? 0
    if (x.usual !== x.cyclic) b.differ.push(`${f}: ${x.name}`)
  }
}
for (const [kind, b] of Object.entries(by)) console.log(`${kind}: ${b.n} compared, usual ${b.usual} ms, cyclic ${b.cyclic} ms (${(b.cyclic / Math.max(1, b.usual)).toFixed(2)}x), ${b.uncovered} uncovered, ${b.differ.length} differ${b.differ.length ? `: ${b.differ.join('; ')}` : ''}`)
