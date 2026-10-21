import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build} from '../translate.ts'
const t0 = performance.now()
const chc = parseChc(readFileSync(process.argv[2]!, 'utf8'))
const t1 = performance.now()
const b = build(chc)
const m = b.rule.machine
const t2 = performance.now()
const size = JSON.stringify(m.step).length
console.log({parse: Math.round(t1 - t0), build: Math.round(t2 - t1), stepJson: size, state: Object.keys(m.state).length, inputs: m.inputs.length})
const seen = new Set<object>()
const walk = (x: unknown): void => { if (!x || typeof x !== 'object' || seen.has(x)) return; seen.add(x); for (const v of Object.values(x)) walk(v) }
// tree size with memo of subtree sizes
const sizes = new Map<object, number>()
const sz = (x: unknown): number => { if (!x || typeof x !== 'object') return 0; const c = sizes.get(x); if (c !== undefined) return c; let n = 1; for (const v of Object.values(x)) n += sz(v); sizes.set(x, n); return n }
walk(m.step)
console.log({dagNodes: seen.size, treeNodes: sz(m.step)})
for (const [k, e] of Object.entries(m.step.state ?? {}).slice(0, 4)) console.log(k, sz(e))
console.log('loc', sz((m.step.state as any).loc))
