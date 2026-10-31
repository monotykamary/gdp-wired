// A dumped goal (core/counts.ts's GDP_COUNTS_DUMP, one JSON line a goal: {hyps}) asked of the prover's ways, each
// timed: the whole goal's grow, the CDCL search's refutation with its core, and grow over a relevance-filtered part
// widened to the whole, its tree checked by the kernel. Research only (gen/laneG's profile).
//   bun research/protocols/engine/goalbench.ts <file.jsonl> [--ms 20000] [--only i] [--ways whole,core,rel]
import {readFileSync} from 'node:fs'
import {type Goal, type Tree, canon, check} from '../../../kernel/kernel.ts'
import {grow, relevant, widen} from '../../../kernel/prove.ts'
import {cdclStats, growCdcl} from '../../../kernel/cdcl.ts'

const arg = (name: string) => { const i = process.argv.indexOf(`--${name}`); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('ms') ?? 20_000), only = arg('only'), ways = (arg('ways') ?? 'whole,core,rel').split(',')
const lines = readFileSync(process.argv[2]!, 'utf8').split('\n').filter(Boolean)
const size = (t: Tree): number => ('leaf' in t ? 1 : size(t.yes) + size(t.no))
const stats = () => `conflicts ${cdclStats.conflicts} decisions ${cdclStats.decisions} nodes ${cdclStats.nodes} solveMs ${Math.round(cdclStats.solveMs)} rowsMs ${Math.round(cdclStats.rowsMs)} lpMs ${Math.round(cdclStats.lpMs)} orderMs ${Math.round(cdclStats.orderMs)} unfoldMs ${Math.round(cdclStats.unfoldMs)}`
const reset = () => { for (const k of Object.keys(cdclStats) as (keyof typeof cdclStats)[]) if (typeof cdclStats[k] === 'number') (cdclStats as Record<string, unknown>)[k] = 0 }
cdclStats.on = true
for (const [i, line] of lines.entries()) {
  if (only !== undefined && String(i) !== only) continue
  const d = JSON.parse(line) as {law?: string, goal?: string, hyps: Goal['hyps']}, goal: Goal = {name: d.goal ?? `g${i}`, hyps: d.hyps}
  console.log(`goal ${i}: ${d.law} ${d.goal}: ${goal.hyps.length} hyps, ${JSON.stringify(goal.hyps).length} bytes`)
  const checked = (t: Tree) => { const t0 = performance.now(), ok = check(goal, t); return `checked ${ok} in ${Math.round(performance.now() - t0)} ms, ${size(t)} leaves, ${JSON.stringify(t).length} bytes` }
  if (ways.includes('whole')) {
    reset(); const t0 = performance.now(), o = grow(goal, new Map(), {nodes: 0, until: performance.now() + ms})
    console.log(`  whole: ${'tree' in o ? 'proven' : `${o.stuck} (${o.why ?? ''})`} in ${Math.round(performance.now() - t0)} ms; ${stats()}${'tree' in o ? `; ${checked(o.tree)}` : ''}`)
  }
  if (ways.includes('core')) {
    reset(); const t0 = performance.now(), q = growCdcl(goal, new Map(), {nodes: 0, until: performance.now() + ms}, {model: true, core: true}) as {stuck?: string, why?: string, core?: number[]}
    console.log(`  core: ${q.stuck} (${q.why}) core ${q.core?.length ?? '-'} in ${Math.round(performance.now() - t0)} ms; ${stats()}${q.core ? `: ${q.core.join(' ')}` : ''}`)
  }
  // (the clausal CDCL's refutation (Tseitin clauses, a theory leaf reading the trail's atoms), its core grown as a goal of its own and widened)
  if (ways.includes('clcore')) {
    reset(); const t0 = performance.now(), q = growCdcl(goal, new Map(), {nodes: 0, until: performance.now() + ms}, {model: true, core: true, clausal: true}) as {stuck?: string, why?: string, core?: number[]}
    console.log(`  clcore: ${q.stuck} (${q.why}) core ${q.core?.length ?? '-'} in ${Math.round(performance.now() - t0)} ms; ${stats()}${q.core ? `: ${q.core.join(' ')}` : ''}`)
    if (q.core) {
      const keep = [...new Set([...q.core, goal.hyps.length - 1])].sort((a, b) => a - b), part: Goal = {name: goal.name, hyps: keep.map(j => goal.hyps[j]!)}
      reset(); const t1 = performance.now(), o = grow(part, new Map(), {nodes: 0, until: performance.now() + ms})
      const t2 = performance.now(), wide = 'tree' in o ? widen(part, goal, o.tree) : undefined
      console.log(`  clcore part: ${keep.length} hyps: ${'tree' in o ? 'proven' : `${o.stuck} (${o.why ?? ''})`} in ${Math.round(t2 - t1)} ms; ${stats()}${wide ? `; widened in ${Math.round(performance.now() - t2)} ms, ${checked(wide)}` : ''}`)
    }
  }
  // (the step's action first: the variable compared with the most constants by =, split into each value's case, each case
  // grown on its own, the tree assembled)
  if (ways.includes('split')) {
    const consts = new Map<string, Set<number>>()
    const walk = (x: unknown): void => { if (!x || typeof x !== 'object') return; const o = x as {op?: string, a?: {op: string, name?: string, value?: number}, b?: {op: string, value?: number}}; if (o.op === '=' && o.a?.op === 'var' && o.b?.op === 'const') { const s2 = consts.get(o.a.name!) ?? new Set(); s2.add(o.b.value!); consts.set(o.a.name!, s2) } for (const y of Object.values(o)) walk(y) }
    walk(goal.hyps)
    const [x, vs] = [...consts].sort((a, b) => b[1].size - a[1].size)[0] ?? []
    if (x && vs && vs.size >= 3) {
      const values = [...vs].sort((a, b) => a - b), t0 = performance.now()
      const cases = (i: number, path: Map<string, {lin: Record<string, number>, holds: boolean}>): Tree | undefined => {
        const lin = {[x]: 1, ...(values[i] ? {'1': -values[i]!} : {})}, id = canon(lin)
        const side = (holds: boolean): Tree | undefined => {
          const p2 = new Map(path).set(id, {lin, holds})
          if (!holds && i + 1 < values.length) return cases(i + 1, p2)
          reset(); const t1 = performance.now(), c0 = growCdcl(goal, p2, {nodes: 0, until: performance.now() + ms}), o = 'tree' in c0 ? c0 : grow(goal, p2, {nodes: 0, until: performance.now() + ms / 4})
          console.log(`  split ${x} ${holds ? `<= ${values[i]}` : `> ${values[i]}`}: ${'tree' in o ? 'proven' : `${o.stuck} (${(o.why ?? '').slice(0, 80)})`} in ${Math.round(performance.now() - t1)} ms; ${stats()}`)
          return 'tree' in o ? o.tree : undefined
        }
        const yes = side(true), no = side(false)
        return yes && no ? {split: lin, yes, no} : undefined
      }
      const tree = cases(0, new Map())
      console.log(`  split: ${tree ? `proven in ${Math.round(performance.now() - t0)} ms; ${checked(tree)}` : 'not proven'}`)
    } else console.log('  split: no case variable')
  }
  if (ways.includes('rel')) for (const r of [1, 2, 3, 4]) {
    const keep = relevant(goal, r), part: Goal = {name: goal.name, hyps: keep.map(j => goal.hyps[j]!)}
    reset(); const t0 = performance.now(), o = grow(part, new Map(), {nodes: 0, until: performance.now() + ms})
    const t1 = performance.now(), wide = 'tree' in o ? widen(part, goal, o.tree) : undefined
    console.log(`  rel ${r}: ${keep.length} hyps: ${'tree' in o ? 'proven' : `${o.stuck} (${o.why ?? ''})`} in ${Math.round(t1 - t0)} ms; ${stats()}${wide ? `; widened in ${Math.round(performance.now() - t1)} ms, ${checked(wide)}` : 'tree' in o ? '; not widened' : ''}`)
    if (wide) break
  }
}
