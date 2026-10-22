// The cyclic route against the usual one, from a run's `cyclic: {...}` lines (modal/run.py --cyclic):
// `bun research/cyclic/ratios.ts <run dir> [--prefix base-]`, per kind: proofs compared, the usual and the cyclic ms,
// their ratio, the comparisons left uncovered and those that differ; machines also without the normalized scope. Where
// the run translated the usual proofs (GDP_CYCLIC_ROUTE, core/cyclic.ts): how many were translated, fell back to the
// search or were searched (the usual route proved none), the translated leaves and those grown again; with
// GDP_CYCLIC_ROUTE=both, the search's ms in the same run and its ratio; with GDP_CERT=cyclic, the certificates made
// (`(certificate)`); the proofs no instance covers, by why.
import {readdirSync, readFileSync} from 'node:fs'
const dir = process.argv[2]!, prefix = process.argv.includes('--prefix') ? process.argv[process.argv.indexOf('--prefix') + 1]! : ''
type B = {n: number, usual: number, cyclic: number, uncovered: number, whys: Record<string, number>, differ: string[], routes: Record<string, number>, leaves: number, regrown: number, search: number, searched: number, searchDiffer: string[], fellBack: string[]}
const by: Record<string, B> = {}
for (const f of readdirSync(dir).filter(f => f.endsWith('.log') && (prefix ? f.startsWith(prefix) : !f.startsWith('base-')))) for (const line of readFileSync(`${dir}/${f}`, 'utf8').split('\n')) {
  if (!line.startsWith('cyclic: {')) continue
  let x: {kind: string, name: string, usual: boolean, cyclic?: boolean, ms?: number, usualMs?: number, uncovered?: boolean, why?: string, cert?: boolean, route?: string, leaves?: number, regrown?: number, searchMs?: number, searchCyclic?: boolean, fellBack?: string}
  try { x = JSON.parse(line.slice(8)) } catch { continue }
  const k0 = x.cert ? `${x.kind} (certificate)` : x.kind
  for (const kind of [k0, ...(x.kind === 'machine' && x.name !== 'normalized scope' ? [`${k0}, but the normalized scope`] : [])]) {
    const b = (by[kind] ??= {n: 0, usual: 0, cyclic: 0, uncovered: 0, whys: {}, differ: [], routes: {}, leaves: 0, regrown: 0, search: 0, searched: 0, searchDiffer: [], fellBack: []})
    if (x.uncovered) { b.uncovered++; if (x.why) b.whys[x.why] = (b.whys[x.why] ?? 0) + 1; continue }
    b.n++; b.usual += x.usualMs ?? 0; b.cyclic += x.ms ?? 0
    if (x.usual !== x.cyclic) b.differ.push(`${f}: ${x.name}`)
    if (x.route) b.routes[x.route] = (b.routes[x.route] ?? 0) + 1
    b.leaves += x.leaves ?? 0; b.regrown += x.regrown ?? 0
    if (x.fellBack) b.fellBack.push(`${f}: ${x.name} (${x.fellBack})`)
    if (x.searchMs !== undefined) { b.searched++; b.search += x.searchMs; if (x.searchCyclic !== x.usual) b.searchDiffer.push(`${f}: ${x.name}`) }
  }
}
const ratio = (a: number, b: number) => `${(a / Math.max(1, b)).toFixed(2)}x`
for (const [kind, b] of Object.entries(by)) {
  console.log(`${kind}: ${b.n} compared, usual ${b.usual} ms, cyclic ${b.cyclic} ms (${ratio(b.cyclic, b.usual)}), ${b.uncovered} uncovered, ${b.differ.length} differ${b.differ.length ? `: ${b.differ.join('; ')}` : ''}`)
  if (Object.keys(b.whys).length) console.log(`  uncovered: ${Object.entries(b.whys).map(([w, c]) => `${w} ${c}`).join(', ')}`)
  if (Object.keys(b.routes).length) console.log(`  routes ${Object.entries(b.routes).map(([r, c]) => `${r} ${c}`).join(', ')}; ${b.leaves} leaves translated, ${b.regrown} grown again`)
  if (b.searched) console.log(`  searched in the same run: ${b.searched} proofs, ${b.search} ms (${ratio(b.search, b.usual)}), ${b.searchDiffer.length} differ${b.searchDiffer.length ? `: ${b.searchDiffer.join('; ')}` : ''}`)
  if (b.fellBack.length && process.argv.includes('--why')) for (const w of b.fellBack) console.log(`  fell back: ${w}`)
}
