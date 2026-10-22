// The second translation (`solve.ts --scc`), a stronger statement than the task's, counted apart: each cycle of
// locations on its own, from any state at any of its cut points. An infinite run of the task stays in one strongly
// connected component of its locations from some step on, so if no run inside any component is infinite, from any
// values, the task terminates (the converse fails: a run inside a component from values no run of the task reaches
// may be infinite, and then nothing is proven). Within a component, the paths between cut points (the targets of a
// depth-first search's back edges: every cycle passes through one) are composed into one rule each (chaining), so a
// loop of five locations is one rule at one location. What the kernel checks is each component's halting; that the
// components' halting is the task's is this file's argument, not the kernel's.
import {type Ari, type Rule, type Sx, isVar, ruleVars} from './ari.ts'

let fresh = 0
const rename = (s: Sx, m: Map<string, string>): Sx => (typeof s === 'string' ? m.get(s) ?? s : s.map(x => rename(x, m)))
const subst = (s: Sx, m: Map<string, Sx>): Sx => (typeof s === 'string' ? m.get(s) ?? s : s.map(x => subst(x, m)))

// r1 then r2: f(x̄) → h(s̄[ȳ := t̄]) where φ1 and φ2[ȳ := t̄] (r2's variables renamed apart first).
export function compose(r1: Rule, r2: Rule): Rule {
  const {lhs, others} = ruleVars(r2), k = ++fresh
  const ren = new Map([...lhs, ...others].map(v => [v, `${v}@${k}`]))
  const lhs2 = r2.lhs.map(a => rename(a, ren)), rhs2 = r2.rhs.map(a => rename(a, ren)), g2 = rename(r2.guard, ren)
  const sub = new Map<string, Sx>(), eqs: Sx[] = []
  lhs2.forEach((a, j) => { if (typeof a === 'string' && isVar(a) && !sub.has(a)) sub.set(a, r1.rhs[j]!); else eqs.push(['=', a, r1.rhs[j]!]) })
  return {from: r1.from, lhs: r1.lhs, to: r2.to, rhs: rhs2.map(a => subst(a, sub)), guard: ['and', r1.guard, subst(g2, sub), ...eqs.map(e => subst(e, sub))]}
}

export type Component = {task: Ari, starts: string[], chained: boolean, locations: number, rules: number}
export function components(t: Ari, cap = 400): Component[] {
  const locs = [...t.funs.keys()], succ = new Map(locs.map(l => [l, new Set<string>()]))
  for (const r of t.rules) succ.get(r.from)!.add(r.to)
  // Tarjan's strongly connected components
  const index = new Map<string, number>(), low = new Map<string, number>(), on = new Set<string>(), stack: string[] = [], sccs: string[][] = []
  let i = 0
  const visit = (v: string) => {
    index.set(v, i); low.set(v, i); i++; stack.push(v); on.add(v)
    for (const w of succ.get(v)!) {
      if (!index.has(w)) { visit(w); low.set(v, Math.min(low.get(v)!, low.get(w)!)) } else if (on.has(w)) low.set(v, Math.min(low.get(v)!, index.get(w)!))
    }
    if (low.get(v) === index.get(v)) { const c: string[] = []; let w; do { w = stack.pop()!; on.delete(w); c.push(w) } while (w !== v); sccs.push(c) }
  }
  for (const l of locs) if (!index.has(l)) visit(l)
  const out: Component[] = []
  for (const c of sccs) {
    const inC = new Set(c), rules = t.rules.filter(r => inC.has(r.from) && inC.has(r.to))
    if (!rules.length) continue
    // cut points: the targets of back edges of a depth-first search inside the component
    const cut = new Set<string>(), state = new Map<string, number>()
    const dfs = (v: string) => {
      state.set(v, 1)
      for (const r of rules) if (r.from === v) { const s = state.get(r.to); if (s === 1) cut.add(r.to); else if (s === undefined) dfs(r.to) }
      state.set(v, 2)
    }
    dfs(c[0]!)
    const composed: Rule[] = []
    let over = false
    const walk = (r: Rule, depth: number) => {
      if (over) return
      if (cut.has(r.to)) { composed.push(r); if (composed.length > cap) over = true; return }
      for (const r2 of rules) if (r2.from === r.to) walk(compose(r, r2), depth + 1)
    }
    for (const r of rules) if (cut.has(r.from)) walk(r, 0)
    const chained = !over, use = chained ? composed : rules, keep = chained ? [...cut] : c
    const funs = new Map(keep.map(l => [l, t.funs.get(l)!]))
    out.push({task: {funs, entry: keep[0]!, rules: use}, starts: keep, chained, locations: keep.length, rules: use.length})
  }
  return out
}
