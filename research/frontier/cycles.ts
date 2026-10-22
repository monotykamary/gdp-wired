// The cycle track's corpus: cyclic proofs nobody shaped (examples/cycles.ts), each stated with nothing a proof needs.
// `frontier` is core/cycles.ts's search; `today` is what the library did before it, with the same statement:
//   - claims over functions: core/cyclic.ts's builders' shape (recurNodes'), each claim at rank (x) for one of its
//     variables x (each tried), using every claim at x − 1 where 1 <= x, with the facts at the terms the goal reads and
//     at those the facts read (the search's own instances, so only the shape differs)
//   - loops: a loop's rank is stated (`proveLoop` takes none), so today is kernel/run-more.ts's templates, each checked
//     by the kernel: a state variable, a param minus a state variable, a sum of two state variables
//   - rules reading functions known by their facts: `proveRule` with its search as at 0.17.0 (deeper runs, discover,
//     inferLaws; `cycles: false`)
//   - liveness with no rank: `proveLeadsTo` takes one, so today is the loops' templates as its rank, each through
//     `proveLiveness`: a state variable, a param minus a state variable, a sum of two state variables
// A broken variant is an item too (`broken`): it counts when nothing proves it.
import type {E} from '../../core/machine.ts'
import type {Loop} from '../../kernel/kernel.ts'
import {check, loopObligations} from '../../kernel/kernel.ts'
import {grow, proveLiveness} from '../../kernel/prove.ts'
import {type Verdict, proveLeadsTo, proveLoop, proveRule} from '../../core/dsl.ts'
import {type NodeSpec, proveCyclic} from '../../core/cyclic.ts'
import {claimInstances, findCycles, showE} from '../../core/cycles.ts'
import {type Case, type LiveCase, claimCases, liveCases, loopCases, ruleCases} from '../../examples/cycles.ts'
import type {Item} from './corpus.ts'

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const vars = (c: Case) => [...new Set(c.claims.flatMap(cl => [...JSON.stringify(cl).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!)))].sort()

function builders(c: Case): Verdict {
  let last: Verdict = {proven: false, checked: false}
  for (const x of vars(c)) {
    if (!c.claims.every(cl => JSON.stringify(cl).includes(`"op":"var","name":"${x}"`))) continue
    const specs: NodeSpec[] = c.claims.map(cl => ({name: cl.name, hyps: cl.hyps ?? [], concl: cl.concl, rank: [v(x)], insts: claimInstances(c.facts, cl, 2),
      uses: c.claims.map((_, j) => ({node: j, subst: {[x]: {op: 'sub', a: v(x), b: k(1)} as E}, guard: {op: '<=', a: k(1), b: v(x)}}))}))
    const out = proveCyclic(c.facts, specs)
    if (out.proven && out.checked) return {proven: true, checked: true, found: {rank: `(${x})`}}
    last = {proven: false, checked: false, ...(out.proven ? {} : {goal: out.goal, stuck: out.stuck})}
  }
  return last
}
const searched = (c: Case): Verdict => {
  const out = findCycles(c.facts, c.claims)
  return {proven: out.proven, checked: out.checked, ...(out.goal ? {goal: out.goal, stuck: out.stuck} : {}), ...(out.why ? {why: out.why} : {}),
    ...(out.found ? {found: {rank: Object.entries(out.found.ranks).map(([n, r]) => `${n}: ${r}`).join('; '), ...(out.found.companions.length ? {facts: out.found.companions} : {})}} : {})}
}
// kernel/run-more.ts's templates.
function templates(l: Loop): Verdict {
  const st = Object.keys(l.state), sub = (a: E, b: E): E => ({op: 'sub', a, b}), add = (a: E, b: E): E => ({op: 'add', a, b})
  const ranks: E[] = [...st.map(v), ...l.params.flatMap(p => st.map(s => sub(v(p), v(s)))), ...st.flatMap((s, i) => st.slice(i + 1).map(w => add(v(s), v(w))))]
  for (const r of ranks) {
    if (loopObligations(l, [], r).every(g => { const o = grow(g); return 'tree' in o && check(g, o.tree) })) return {proven: true, checked: true, found: {rank: showE(r)}}
  }
  return {proven: false, checked: false, why: `no rank among ${ranks.length} templates`}
}

// The same templates as a liveness's rank.
function liveTemplates(c: LiveCase): Verdict {
  const m = c.r.machine, st = Object.keys(m.state), sub = (a: E, b: E): E => ({op: 'sub', a, b}), add = (a: E, b: E): E => ({op: 'add', a, b})
  const ranks: E[] = [...st.map(v), ...m.params.flatMap(p => st.map(s => sub(v(p), v(s)))), ...st.flatMap((s, i) => st.slice(i + 1).map(w => add(v(s), v(w))))]
  const laws = [...c.r.kindLaws().filter(k => !c.laws.some(l => l.name === k.name)), ...c.laws]
  for (const r of ranks) { const o = proveLiveness(m, laws, {...c.live, rank: r}); if (o.proven && o.checked) return {proven: true, checked: true, found: {rank: showE(r)}} }
  return {proven: false, checked: false, why: `no rank among ${ranks.length} templates`}
}

const slug = (s: string) => s.replace(/ \(.*\)$/, '')
export const cycleItems: Item[] = [
  ...claimCases().map(([c, ok]): Item => ({id: `cycle/${c.name}`, track: 'cycle', removed: 'the rank, the back-edges and any lemma', ...(ok ? {} : {broken: slug(c.name)}), today: () => builders(c), frontier: () => searched(c)})),
  ...loopCases().map(([l, ok]): Item => ({id: `cycle/loop: ${l.loop.name}`, track: 'cycle', removed: 'the rank and any invariant', ...(ok ? {} : {broken: slug(l.loop.name)}), today: () => templates(l.loop), frontier: () => proveLoop(l, [])})),
  ...ruleCases().map(([{r, laws}, ok]): Item => ({id: `cycle/rule: ${r.machine.name}`, track: 'cycle', removed: 'the lemma about the function', ...(ok ? {} : {broken: slug(r.machine.name)}),
    today: () => proveRule(r, laws, {search: {cycles: false}}), frontier: () => proveRule(r, laws)})),
  ...liveCases().map(([c, ok]): Item => ({id: `cycle/liveness: ${c.name}: ${c.live.name}`, track: 'cycle', removed: 'the rank', ...(ok ? {} : {broken: slug(c.name)}),
    today: () => liveTemplates(c), frontier: () => proveLeadsTo(c.r, c.laws, c.live)})),
]
