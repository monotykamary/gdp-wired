// The certificates of a task rewritten by its facts (facts.ts), made again on the task's own loop (translate.ts's, the
// task's statement): the rewritten task is only where the searches look, and no answer rests on it. Its locations and
// slots are the task's, in its order (no location split), so a rank or a set found on it reads the task's names.
// - The facts: each location's constants, as the loop's laws (`pc = L → s = c`), proven inductive by the kernel with
//   whatever needs them (the halting goals, which assume them only where they prove them), or put in a recurrent set
//   (the set's part at each location, its closure then proving them along the witnessed turns).
// - A rank: the halting goals of the task's loop with the facts and the rank's own laws, each tree grown and checked.
// - A recurrent set: its turn's rule and inputs read back to the task's (each rewritten rule's origin, a value the
//   rewrite fixed its constant), its stem lifted to the task's steps (facts.ts's `lift`), the set with the facts, the
//   closure grown again and the whole certificate checked by kernel.ts's checkRecur.
// A residue (x ≡ c mod k) is no term of the kernel's: an answer that needs one is not made here (the hand-off: division
// by a constant in a loop's terms).
import type {Ari, Step} from './ari.ts'
import {type Built, stepOf, varsOf} from './translate.ts'
import {type Facts, lift, unreached} from './facts.ts'
import type {C, E, Law} from '../../core/machine.ts'
import {interpret} from '../../core/machine.ts'
import {type Goal, type Recur, type RecurCases, type Tree, caseGoals, check, checkRecur, coverGoal, loopMachine, loopObligations, recurGoal} from '../../kernel/kernel.ts'
import {grow, realModels} from '../../kernel/prove.ts'

const K = (value: number): E => ({op: 'const', value}), V = (name: string): E => ({op: 'var', name})
const eq = (a: E, b: E): C => ({op: '=', a, b}), and = (xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})
const plus = (a: E, k: number): E => (k ? {op: 'add', a, b: K(k)} : a)

// Each location's constants, as `pc = L → each slot its value` (a slot read as a param left out: no rule changes it),
// and a location no run reaches as `pc = L → false`.
function atLocation(b: Built, consts: Map<string, Map<number, bigint>>): [number, C][] {
  const out: [number, C][] = []
  for (const [loc, cs] of consts) {
    if (cs === unreached) { const i = b.locs.indexOf(loc); if (i >= 0) out.push([i, {op: '<', a: K(0), b: K(0)}]); continue }
    const i = b.locs.indexOf(loc), xs = [...cs].filter(([j]) => !b.fixed.has(j) && !b.dropped.has(j)).map(([j, c]) => eq(plus(V(`s${j}`), Math.max(0, -Number(c))), plus(V(`s${j}$n`), Math.max(0, Number(c)))))
    if (i >= 0 && xs.length) out.push([i, and(xs)])
  }
  return out
}
export const factLaws = (b: Built, consts: Map<string, Map<number, bigint>>): Law[] =>
  atLocation(b, consts).map(([i, c]) => ({name: `the facts at ${b.locs[i]}`, holds: {op: 'or', xs: [{op: 'not', x: eq(V('pc'), K(i))}, c]}}))
// The facts a rank of the rewritten task needs on the task's, first: where a rule the rewrite left out starts, its
// location's (no run reaches it, or the constants its guard reads); then every location's, as one law (one goal to
// prove it inductive, not one a location).
export function factLawSets(b: Built, t: Ari, f: Facts): Law[][] {
  const kept = new Set(f.origins.map(o => o.rule)), need = new Map<string, Map<number, bigint>>()
  for (const [i, r] of t.rules.entries()) {
    if (kept.has(i)) continue
    const cs = f.consts.get(r.from)
    if (!cs) continue
    if (cs === unreached) { need.set(r.from, cs); continue }
    const read = varsOf(r.guard), slots = new Map([...cs].filter(([j]) => typeof r.lhs[j] === 'string' && read.has(r.lhs[j] as string)))
    if (slots.size) need.set(r.from, new Map([...need.get(r.from) ?? [], ...slots]))
  }
  const first = factLaws(b, need), all = factLaws(b, f.consts)
  const one: Law[] = all.length ? [{name: 'the facts at each location', holds: and(all.map(l => l.holds))}] : []
  return [first, ...(all.length > first.length ? [one] : [])]
}
const factsC = (b: Built, consts: Map<string, Map<number, bigint>>): C => and([{op: '<=', a: K(0), b: K(0)}, ...factLaws(b, consts).map(l => l.holds)])

const grown = (g: Goal, until: number): Tree | undefined => { const o = grow(g, new Map(), {nodes: 0, until}); return 'tree' in o && check(g, o.tree) ? o.tree : undefined }

// A rank on the task's own loop: every halting goal with the laws, its tree grown within `until` and checked.
export function rankOnTask(b: Built, laws: Law[], rank: E[], until: number): Record<string, Tree> | undefined {
  const trees: Record<string, Tree> = {}
  for (const g of loopObligations(b.loop, laws, rank)) { const t = grown(g, until); if (!t) return undefined; trees[g.name] = t }
  return trees
}

// A recurrent set of the rewritten task's loop on the task's own.
export function recurOnTask(b: Built, bR: Built, t: Ari, f: Facts, r: Recur | RecurCases, until: number): Recur | RecurCases | undefined {
  // (the turn: the rewritten rule the witness names, each rewritten rule its origin's index and inputs)
  const fires = (k: number): C => ({op: 'and', xs: [eq(V('pc'), K(bR.plans[k]!.from)), eq(r.wit.t ?? K(0), K(bR.plans[k]!.local))]})
  const chain = (val: (k: number) => E): E => bR.plans.reduceRight<E>((e, _, k) => ({op: 'if', c: fires(k), then: val(k), else: e}), K(0))
  const input = (k: number, m: number, part: '' | '$n'): E => {
    const p0 = b.plans[f.origins[k]!.rule]!, pR = bR.plans[k]!, x = p0.inputs[m]
    if (x === undefined) return K(0)
    const mR = pR.inputs.indexOf(x)
    if (mR >= 0) return r.wit[`i${mR}${part}`] ?? K(0)
    const c = f.origins[k]!.fixed.get(x)
    return c === undefined ? K(0) : K(Math.max(0, part ? -Number(c) : Number(c)))
  }
  const wit: Record<string, E> = {t: chain(k => K(b.plans[f.origins[k]!.rule]!.local))}
  for (let m = 0; m < b.nInputs; m++) for (const part of ['', '$n'] as const) wit[`i${m}${part}`] = chain(k => input(k, m, part))
  // (the stem: the rewritten loop's turns as the task's steps, then each as the task's loop's inputs)
  const run = interpret(loopMachine(bR.loop)), ps = r.start
  let st = run.init(ps)
  const steps: Step[] = []
  for (const turn of r.stem) { steps.push(stepOf(bR, ps, st.scalars, turn)); st = run.step(ps, st, turn) }
  const start = Array.from({length: b.slots}, (_, j) => String((ps[`a${j}`] ?? 0) - (ps[`a${j}$n`] ?? 0)))
  const stem: Record<string, number>[] = []
  for (const s of lift(t, f, start, steps)) {
    const p = b.plans[s.rule]!, turn: Record<string, number> = {t: p.local}
    for (const [m, x] of p.inputs.entries()) { const v = Number(s.others[x] ?? 'NaN'); if (!Number.isSafeInteger(v)) return undefined; turn[`i${m}`] = Math.max(v, 0); turn[`i${m}$n`] = Math.max(-v, 0) }
    stem.push(turn)
  }
  // (the set as found, then with every location's facts: each its share of the time)
  const was = realModels.on
  realModels.on = true
  try {
    for (const [n, facts] of [and([{op: '<=', a: K(0), b: K(0)}]), factsC(b, f.consts)].entries()) {
      const set: C = and([r.set, facts]), base = {start: ps, stem, set, wit}, end = n === 0 ? performance.now() + (until - performance.now()) / 3 : until
      if ('cases' in r) {
        const cases = r.cases.map(c => ({pins: c.pins, cond: and([c.cond, facts])}))
        const cover = grown(coverGoal({set, cases}), end)
        if (!cover) continue
        const trees: Tree[] = []
        for (const g of caseGoals(b.loop, {set, wit}, cases)) { const tr = grown(g, end); if (!tr) break; trees.push(tr) }
        if (trees.length < cases.length) continue
        const out: RecurCases = {...base, cover, cases: cases.map((c, i) => ({...c, tree: trees[i]!}))}
        if (checkRecur(b.loop, out)) return out
        continue
      }
      const tree = grown(recurGoal(b.loop, {set, wit}), end)
      if (!tree) continue
      const out: Recur = {...base, tree}
      if (checkRecur(b.loop, out)) return out
    }
    return undefined
  } catch { return undefined } finally { realModels.on = was }
}
