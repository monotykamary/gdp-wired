// Untrusted search ordering only: a smaller context cannot authorize a result.
// Trees found here are lifted to the original goal before the kernel sees them.
import {type Law, type Machine, walkOnce} from './machine.ts'
import {canon, linOfE} from './solver.ts'
import {type Goal} from '../kernel/kernel.ts'

type Footprint = {vars: Set<string>, maps: Set<string>, cells: Set<string>}
function footprint(value: unknown): Footprint {
  const out: Footprint = {vars: new Set(), maps: new Set(), cells: new Set()}
  walkOnce(value, node => {
    const o = node as Record<string, unknown>
    if (o.op === 'var') out.vars.add(String(o.name))
    if (o.op === 'get') {
      out.maps.add(String(o.map))
      const key = linOfE(o.key as Parameters<typeof linOfE>[0])
      out.cells.add(JSON.stringify([o.map, key ? canon(key) : o.key]))
    }
  })
  return out
}
const overlap = (a: Set<string>, b: Set<string>) => [...a].filter(x => b.has(x)).length

// Count definitions participate through their actual read maps. Binder names
// never create relevance merely because two independent laws spell them alike.
export function relevantLaws(m: Machine, laws: Law[], target: Law, structural: ReadonlySet<Law> = new Set()): Law[][] {
  if (laws.length <= 24) return []
  const ofLaw = (law: Law) => {
    const f = footprint(law.holds), bound = new Set([law.forall, ...(law.keys ?? []), ...(law.some ?? [])])
    for (const v of f.vars) if (bound.has(v) || !Object.hasOwn(m.state, v)) f.vars.delete(v)
    for (const mp of f.maps) {
      const d = m.counts?.[mp]
      if (d) for (const read of footprint(d.body).maps) f.maps.add(read)
    }
    return f
  }
  const own = ofLaw(target)
  const ranked = laws.map((law, i) => {
    const f = ofLaw(law), shared = overlap(f.maps, own.maps), fresh = f.maps.size - shared
    const states = overlap(f.vars, own.vars)
    const scalar = !f.maps.size && (states > 0 || !f.vars.size)
    const simple = shared > 0 && !fresh && !law.keys?.length && !law.some?.length
    const score = law === target ? -10000 : (simple ? -200 : scalar ? -150 : structural.has(law) && (shared || states) ? -100 : shared ? -20 : 100) + fresh * 20 + (f.vars.size - states) * 2 + (law.keys?.length ?? 0)
    return {law, i, score}
  }).sort((a, b) => a.score - b.score || a.i - b.i)
  return [12, 24].filter(cap => cap < laws.length).map(cap => {
    const chosen = new Set(ranked.slice(0, cap).map(r => r.law))
    chosen.add(target)
    return laws.filter(l => chosen.has(l))
  })
}
// Keep exact source hypotheses, in their original order, and the conclusion last.
// Scalar premises for any newly introduced witness accompany its selected cells.
export function relevantGoals(goal: Goal): Goal[] {
  if (goal.hyps.length < 24) return []
  const fs = goal.hyps.map(footprint), root = fs.at(-1)!
  const ranked = fs.slice(0, -1).map((f, i) => {
    const cells = overlap(f.cells, root.cells), maps = overlap(f.maps, root.maps), vars = overlap(f.vars, root.vars)
    const fresh = f.vars.size - vars
    const score = i < 2 ? -10000 : cells ? -1000 - 10 * cells + fresh : maps ? -100 - maps + 4 * fresh : f.maps.size ? 100 + fresh : fresh ? 200 + fresh : -500
    return {i, score}
  }).sort((a, b) => a.score - b.score || a.i - b.i)
  const out: Goal[] = [], seen = new Set<string>()
  for (const cap of [16, 32, 64]) {
    const selected = new Set(ranked.slice(0, cap).map(r => r.i))
    const vars = new Set([...root.vars, ...[...selected].flatMap(i => [...fs[i]!.vars])])
    fs.slice(0, -1).forEach((f, i) => { if (!f.maps.size && [...f.vars].every(v => vars.has(v))) selected.add(i) })
    selected.add(goal.hyps.length - 1)
    const ids = [...selected].sort((a, b) => a - b), key = ids.join(',')
    if (ids.length >= goal.hyps.length || seen.has(key)) continue
    seen.add(key); out.push({name: goal.name, hyps: ids.map(i => goal.hyps[i]!)})
  }
  return out
}
