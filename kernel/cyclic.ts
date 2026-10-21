// Cyclic proofs: one rule for every induction. Trusted, beside kernel.ts, whose tree check it calls; its twin is
// lean-kernel/Cyclic.lean (`cyclic_sound`), which builds the same goals from the same nodes.
//
// The run algebra (kernel.ts, "runs") has its repetitions built in: a law kept by every step, a recurrence's lemma from
// x to x + 1, a fold from children to a node, a rank that drops. Here they are one: a proof is a graph of sequents, its
// cycles the inductions, each back-edge lowering a rank.
//
// A cyclic proof is facts and nodes. A fact is a condition that holds at every value of its keys (a function's
// equation: f(k + 1) = next(k, f(k)) at every k), the rest of the environment fixed. A node is a sequent: its
// hypotheses imply its conclusion, at every environment where the facts hold, for any maps. A node's goal, refuted by
// one tree, is its hypotheses, the facts at the terms it names, and what its uses give, against its conclusion. A use
// reads a node m (any node, this one included) at a substitution of m's variables by terms of this node's frame, where
// a guard holds: it gives m's conclusion there, once m's hypotheses there follow (a goal each) and m's rank there is
// below this node's (one goal; ranks are tuples of naturals, compared in order). Every chain of uses lowers the rank,
// so none is infinite, and a node holds by well-founded induction on its rank.
//
// What is trusted: the goals below, built from the nodes, and kernel.ts's `check` on each. A substitution may assign a
// variable a fact reads only where it is one of the fact's keys (the facts then hold at the substituted frame too).
import type {C, E} from '../core/machine.ts'
import {type Goal, type Tree, check, substC, substE} from './kernel.ts'

export type Fact = {name: string, keys: string[], holds: C}
export type Use = {node: number, subst: Record<string, E>, guard: C, premises: Tree[], descent: Tree}
export type CNode = {name: string, hyps: C[], concl: C, rank: E[], insts: {fact: number, at: E[]}[], uses: Use[], main: Tree}
export type Cyclic = {facts: Fact[], nodes: CNode[]}

const zero: E = {op: 'const', value: 0}
export const falseC: C = {op: '<', a: zero, b: zero}
// as below bs in order: the first place they differ, as's is smaller (Lean's lexLtC, built the same way).
export const lexLt = (as: E[], bs: E[]): C => (as.length && bs.length
  ? {op: 'or', xs: [{op: '<', a: as[0]!, b: bs[0]!}, {op: 'and', xs: [{op: '=', a: as[0]!, b: bs[0]!}, lexLt(as.slice(1), bs.slice(1))]}]}
  : falseC)
const sub = (s: Record<string, E>) => ({vars: s, maps: {}, flags: {}})
// A fact at the terms a node names: its keys paired with the terms (the shorter list decides, as Lean's zip does).
const keyed = (keys: string[], at: E[]): Record<string, E> => Object.fromEntries(keys.slice(0, at.length).map((key, i) => [key, at[i]!]))

export const instHyps = (facts: Fact[], insts: CNode['insts']): C[] => insts.flatMap(p => { const f = facts[p.fact]; return f ? [substC(f.holds, sub(keyed(f.keys, p.at)))] : [] })
export const baseHyps = (facts: Fact[], n: Pick<CNode, 'hyps' | 'insts'>): C[] => [...n.hyps, ...instHyps(facts, n.insts)]
export const useHyps = (nodes: Pick<CNode, 'concl'>[], uses: Pick<Use, 'node' | 'subst' | 'guard'>[]): C[] => uses.flatMap(u => {
  const m = nodes[u.node]
  return m ? [{op: 'or', xs: [{op: 'not', x: u.guard}, substC(m.concl, sub(u.subst))]} as C] : []
})
type Shape = Pick<CNode, 'name' | 'hyps' | 'concl' | 'rank' | 'insts'> & {uses: Pick<Use, 'node' | 'subst' | 'guard'>[]}
export const mainGoal = (facts: Fact[], nodes: Shape[], n: Shape): Goal => ({name: `${n.name}`, hyps: [...baseHyps(facts, n), ...useHyps(nodes, n.uses), {op: 'not', x: n.concl}]})
export const premiseGoal = (facts: Fact[], n: Shape, u: Shape['uses'][number], c: C, i: number): Goal =>
  ({name: `${n.name}: use of node ${u.node}, its hypothesis ${i}`, hyps: [...baseHyps(facts, n), u.guard, {op: 'not', x: substC(c, sub(u.subst))}]})
export const descentGoal = (facts: Fact[], n: Shape, u: Shape['uses'][number], m: Shape): Goal =>
  ({name: `${n.name}: use of node ${u.node}, its rank below`, hyps: [...baseHyps(facts, n), u.guard, {op: 'not', x: lexLt(m.rank.map(e => substE(e, sub(u.subst))), n.rank)}]})

const occurs = (name: string, t: unknown): boolean => JSON.stringify(t).includes(`"op":"var","name":${JSON.stringify(name)}`)
// The language Lean's twin has: no flag, no quantifier.
const plain = (t: unknown): boolean => !/"op":"(?:flag|all)"/.test(JSON.stringify(t))
export const factsAvoid = (facts: Fact[], subst: Record<string, E>): boolean =>
  Object.keys(subst).every(v => facts.every(f => f.keys.includes(v) || !occurs(v, f.holds)))

// Why a cyclic proof is refused, or undefined when it checks.
export function refuseCyclic(p: Cyclic): string | undefined {
  const {facts, nodes} = p
  if (!plain(facts) || !plain(nodes.map(n => [n.hyps, n.concl, n.rank, n.insts, n.uses.map(u => [u.subst, u.guard])]))) return 'a flag or a quantifier (no cyclic proof reads one)'
  for (const f of facts) if (new Set(f.keys).size !== f.keys.length) return `fact ${f.name}: a key twice`
  for (const n of nodes) {
    if (!check(mainGoal(facts, nodes, n), n.main)) return `${n.name}: its goal`
    for (const [j, u] of n.uses.entries()) {
      const m = nodes[u.node]
      if (!m) return `${n.name}: use ${j} names no node`
      if (m.rank.length !== n.rank.length) return `${n.name}: use ${j} compares ranks of different lengths`
      if (!factsAvoid(facts, u.subst)) return `${n.name}: use ${j} assigns a variable a fact reads`
      if (m.hyps.length !== u.premises.length) return `${n.name}: use ${j} has ${u.premises.length} premise trees for ${m.hyps.length} hypotheses`
      for (const [i, c] of m.hyps.entries()) if (!check(premiseGoal(facts, n, u, c, i), u.premises[i]!)) return `${n.name}: use ${j}, hypothesis ${i} of ${m.name}`
      if (!check(descentGoal(facts, n, u, m), u.descent)) return `${n.name}: use ${j} doesn't lower the rank`
    }
  }
  return undefined
}
export const checkCyclic = (p: Cyclic): boolean => refuseCyclic(p) === undefined
