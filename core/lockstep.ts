// Search shortcut for two scalars initialized and updated in lockstep. The
// matched form only chooses a proof attempt; the normal kernel decides it.
import type {E, Law, Machine} from './machine.ts'
import {retainFamily} from './proof-output.ts'
import {checkLaws, obligations, type Tree} from '../kernel/kernel.ts'
import {clock, grow, withDeadline} from '../kernel/prove.ts'

const same = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b)
function renaming(e: E, self: string): string {
  return JSON.stringify(e, (_key, node: unknown) => {
    const t = node as E | undefined
    return t?.op === 'var' && t.name === self ? {op: '$self'} : node
  })
}

export function tryLockstepScalars(m: Machine, law: Law, ms: number): {proven: true, checked: true} | undefined {
  if (law.holds.op !== '=' || law.forall || law.keys?.length || law.some?.length || law.finite ||
      law.holds.a.op !== 'var' || law.holds.b.op !== 'var') return
  const a = law.holds.a.name, b = law.holds.b.name, u = m.step.state?.[a], v = m.step.state?.[b]
  if (!u || !v || a === b || !m.state[a] || !m.state[b] || !same(m.state[a], m.state[b]) || renaming(u, a) !== renaming(v, b)) return
  const until = clock() + ms
  return withDeadline(until, () => {
    // No kind or quantified instances are needed if these obligations close.
    const laws = [law], instances = {}, trees: Record<string, Tree> = {}
    for (const g of obligations(m, laws, instances)) {
      const got = grow(g, new Map(), {nodes: 0, until})
      if (!('tree' in got)) return undefined
      trees[g.name] = got.tree
    }
    const proof = {instances, trees}
    return checkLaws(m, laws, proof) ? retainFamily({proven: true as const, checked: true as const}, m, laws, proof) : undefined
  })
}
