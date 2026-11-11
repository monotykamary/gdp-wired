// Untrusted minimal-view-first count queries. A reduced view proves no new fact:
// its tree is exactly reindexed and checked against the caller's original goal.
import {type C, walkOnce} from './machine.ts'
import {type CountCert, type CountDecl, type CountInst, type Goal, type Path, type Tree, check, mcGoal} from '../kernel/kernel.ts'
import {type Outcome, clock, fullRate, fullWork, late, rowsAt} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {solve} from './solver.ts'
import {rebasePath} from './count-recovery/rebase-path.ts'
// Only conjunctive consequences are projected. A positive disjunction remains
// intact; negation is pushed through it before any unrelated clause is dropped.
export function countQueryConjuncts(c: C, negated = false): C[] {
  if (c.op === 'not') return countQueryConjuncts(c.x, !negated)
  if ((c.op === 'and' || c.op === 'or') && c.op === (negated ? 'or' : 'and')) return c.xs.flatMap(h => countQueryConjuncts(h, negated))
  return [negated ? {op: 'not', x: c} : c]
}
export function countSearchView(raw: Goal, decls: CountDecl[], request: Pick<CountCert, 'reads' | 'insts' | 'picks'>, selected?: CountInst): Goal | undefined {
  const other = new Set(selected ? request.insts.filter(i => i !== selected).map(i => i.wit) : [])
  const hyps = raw.hyps.flatMap(h => countQueryConjuncts(h)).filter(h => {
    let unrelated = false
    walkOnce(h, (node: any) => {if (node.op === 'if' || node.op === 'var' && other.has(node.name)) unrelated = true})
    return !unrelated
  })
  return mcGoal(hyps, decls, {...request, insts: selected ? [selected] : request.insts, picks: []})
}
export type CountQueryOptions = {query: string, minimal?: Goal, trace?: (event: Record<string, unknown>) => void, direct?: boolean, deferCheck?: boolean, leafUnits?: number, minimalUnits?: number, fullUnits?: number}
export function proveCountQuery(goal: Goal, path: Path, until: number, options: CountQueryOptions): Tree | undefined {
  const leafEnd = Math.min(until, clock() + (options.leafUnits ?? Infinity))
  const attempt = (view: Goal, mode: 'minimal' | 'full'): {out: Outcome, tree?: Tree} | undefined => {
    if (clock() >= leafEnd || late(leafEnd)) {
      if (leafEnd < until && !late(until)) options.trace?.({query: options.query, mode, outcome: 'leaf-cap', units: 0, remaining: until - clock(), hyps: view.hyps.length, fullHyps: goal.hyps.length})
      return
    }
    const start = fullWork(), end = Math.min(leafEnd, clock() + (mode === 'minimal' ? options.minimalUnits ?? Infinity : options.fullUnits ?? Infinity))
    let out: Outcome | undefined
    if (options.direct) {
      const direct = solve(rowsAt(view, path), 2000, true, () => clock() < end && !late(end))
      if (direct.kind === 'refuted') out = {tree: {leaf: direct.steps}, nodes: 0}
    }
    out ??= clock() < end && !late(end) ? growCdcl(view, path, {nodes: 0, until: end}) : {stuck: 'unknown', path, why: 'leaf deadline'}
    const searchUnits = (fullWork() - start) / fullRate, capped = leafEnd < until && clock() >= leafEnd
    const tree = 'tree' in out ? view === goal ? out.tree : rebasePath(view, out.tree, path, path, until, goal) : undefined
    const accepted = !capped && tree && (options.deferCheck || check(goal, tree, path)) && clock() < until ? tree : undefined
    options.trace?.({query: options.query, mode, outcome: capped ? 'leaf-cap' : clock() >= until ? 'pool-exhausted' : 'tree' in out ? accepted ? 'proposed' : 'transport-rejected' : out.stuck, units: (fullWork() - start) / fullRate, searchUnits, remaining: until - clock(), hyps: view.hyps.length, fullHyps: goal.hyps.length, ...(!('tree' in out) ? {goal: view, path: [...path.values()], ...('witness' in out ? {witness: out.witness} : {}), ...('why' in out ? {why: out.why} : {})} : {})})
    return {out, ...(accepted ? {tree: accepted} : {})}
  }
  if (options.minimal) {
    const small = attempt(options.minimal, 'minimal')
    if (!small || small.tree) return small?.tree
    // Unknown and a failed transport are not grounds to spend a second budget.
    if ('tree' in small.out || small.out.stuck !== 'sat') return
  }
  return attempt(goal, 'full')?.tree
}
