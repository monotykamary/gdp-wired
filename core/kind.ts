// k-induction's search: a law the kernel's induction (one step) doesn't prove, proven over k steps in a row. Nothing
// here is trusted: the certificate is kernel.ts's (checkKInduction, whose Lean twin is KInd.lean's kind_sound), its
// goals built by kernel.ts from the law alone; this file only looks for the trees.
//
// For k = from, from + 1, ...: the step's goal first (k states where the law held and the steps between, the law after
// them refuted), its verdict asked of kernel/cdcl.ts's search for a model alone (as core/bmc.ts asks a bounded run's):
// a model is a run of k steps that keeps the law and then breaks it, which a larger k may rule out; refuted, the step's
// tree is grown: CDCL's, unfolded (else prove.ts's grow, the plain search and its cuts). Then the base, each depth's goal grown once (it doesn't depend on k), and
// the law's start goal. A base goal with a model is a run from the start that breaks the law: the search stops there
// (core/bmc.ts finds the run). Everything is on prove.ts's counted clock (`rate` units of the kernel's work a ms), with a
// wall-clock stop beside it for callers under a wall-clock limit.
import type {C, Law, Machine} from './machine.ts'
import {type Goal, type Instances, type KInduction, type Tree, checkKInduction, historyMachine, kInductionStart, kInductionSteps, stepLawObligations} from '../kernel/kernel.ts'
import {clock, counted, grow, proveLaws, type Outcome} from '../kernel/prove.ts'
import {REFUTED, growCdcl} from '../kernel/cdcl.ts'

export type KindProof = {laws: {instances: Record<string, Instances>, trees: Record<string, Tree>}, instances: Instances, trees: Record<string, Tree>}
export type KindResult = {proven: boolean, checked: boolean, k?: number, kl?: KInduction, proof?: KindProof, laws?: Law[],
  // each k tried: [k, its step goal's outcome (r refuted, s a model, u unknown, t no tree), counted ms]
  depths: [number, string, number][], why?: string}
export type KindOptions = {ms: number, wall?: number, from?: number, to?: number, rate?: number}

// Machines whose k-step goals need no instances: no map a law or fact reads at keys, no flag that holds at every key.
export const kindFits = (m: Machine, laws: Law[], law: Law): boolean => {
  const plain = m.history ? historyMachine(m).machine : m
  return !Object.values(plain.step.flags ?? {}).some(c => c.op === 'all') && !plain.inputMaps?.length && [...laws, law, ...(plain.facts ?? [])].every(l => !l.forall && !l.keys?.length && !l.some?.length)
}

// The laws as one: their conjunction, named by them.
export const conjunction = (laws: Law[]): Law => (laws.length === 1 ? laws[0]! : {name: laws.map(l => l.name).join(' and '), holds: {op: 'and', xs: laws.map(l => l.holds)} as C})

export function proveKInduction(m: Machine, laws: Law[], law: Law, opts: KindOptions): KindResult {
  const depths: KindResult['depths'] = []
  if (!kindFits(m, laws, law)) return {proven: false, checked: false, depths, why: 'a law or fact about every key, a flag at every key, or a carried map'}
  return counted(opts.rate ?? 200, () => {
    const until = clock() + opts.ms, over = () => clock() > until || (opts.wall !== undefined && performance.now() > opts.wall)
    const base = proveLaws(m, laws)
    if (!base.proven || !base.checked || !base.proof) return {proven: false, checked: false, depths, why: 'the laws it assumes are not proven'}
    const assumed = base.laws ?? laws
    // A goal's tree: CDCL's, unfolded (prove.ts's grow keeps CDCL off a goal over k steps, for the size of the tree its
    // cuts would make smaller; but here the plain search's cases multiply with every step), else the plain search's.
    const treeOf = (g: Goal): Outcome => {
      const c = growCdcl(g, new Map(), {nodes: 0, until}, opts.wall !== undefined ? {wall: opts.wall} : {})
      if ('tree' in c || c.stuck === 'sat' || over()) return c
      return grow(g, new Map(), {nodes: 0, until})
    }
    const trees: Record<string, Tree> = {}
    const start = kInductionStart(m, {law, k: 1}, {}), s0 = treeOf(start)
    if (!('tree' in s0)) return {proven: false, checked: false, depths, why: `${start.name}: ${s0.stuck}`}
    trees[start.name] = s0.tree
    for (let k = Math.max(1, opts.from ?? 2); k <= Math.min(64, opts.to ?? 64) && !over(); k++) {
      const t0 = clock(), kl: KInduction = {law, k}, steps = kInductionSteps(m, kl), last = steps.at(-1)!
      const goal = stepLawObligations(m, assumed, {}, last)[0]!
      const decided = growCdcl(goal, new Map(), {nodes: 0, until}, {model: true, ...(opts.wall !== undefined ? {wall: opts.wall} : {})})
      if (!('tree' in decided) && decided.why !== REFUTED) {
        depths.push([k, decided.stuck[0]!, Math.round(clock() - t0)])
        if (decided.stuck === 'sat') continue
        return {proven: false, checked: false, depths, why: `${goal.name}: unknown`}
      }
      const st = treeOf(goal)
      if (!('tree' in st)) { depths.push([k, 't', Math.round(clock() - t0)]); return {proven: false, checked: false, depths, why: `${goal.name}: refuted, but no tree within the budget`} }
      depths.push([k, 'r', Math.round(clock() - t0)])
      trees[goal.name] = st.tree
      // The base, from the start: each depth below k (grown once, whatever k).
      for (const sl of steps.slice(0, -1)) {
        const g = stepLawObligations(m, assumed, {}, sl)[0]!
        if (trees[g.name]) continue
        const b = treeOf(g)
        if (!('tree' in b)) return {proven: false, checked: false, depths, why: `${g.name}: ${b.stuck === 'sat' ? 'a run from the start breaks it' : 'unknown'}`}
        trees[g.name] = b.tree
      }
      const proof: KindProof = {laws: base.proof, instances: {}, trees}
      const checked = checkKInduction(m, assumed, kl, proof)
      return {proven: true, checked, k, kl, proof, laws: assumed, depths}
    }
    return {proven: false, checked: false, depths, why: 'no k within the budget'}
  })
}
