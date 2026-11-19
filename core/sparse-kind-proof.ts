// Try a small instantiation of the ordinary family. Only the unchanged
// kernel's checkLaws can accept it. This is useful when numerous kind guards
// share a record but each output only needs the previous kind at its own key.
import {type C, type E, type Law, type Machine, walkOnce} from './machine.ts'
import {checkLaws, obligations, type Instances, type Tree} from '../kernel/kernel.ts'
import {grow} from '../kernel/prove.ts'

// A conjunction of state laws at one arbitrary key holds exactly when all
// of its conjuncts hold at that same key. Preserve the binders and check the
// entire resulting family; this only removes branching between kind fields.
export function kindConjuncts(kinds: Law[], reserved: Law[]): Law[] {
  const names = new Set([...kinds, ...reserved].map(l => l.name))
  const flatten = (c: C): C[] => c.op === 'and' && c.xs.length ? c.xs.flatMap(flatten) : [c]
  return kinds.flatMap(law => {
    if (law.some?.length || law.finite || law.keys?.length) return [law]
    const parts = flatten(law.holds)
    return parts.length === 1 ? [law] : parts.map((holds, i) => {
      let name = `${law.name} [conjunct ${i + 1}]`
      while (names.has(name)) name += '_'
      names.add(name)
      return {...law, name, holds}
    })
  })
}
export function sparseKindProof(m: Machine, laws: Law[], until: number) {
  if (laws.some(l => l.keys?.length || l.some?.length || l.finite)) return undefined
  const instances: Record<string, Instances> = Object.fromEntries(laws.filter(l => l.forall).map(law => {
    const reads = new Set<string>(), key: E = {op: 'var', name: `${law.forall}#`}
    walkOnce(law.holds, x => { const t = x as E; if (t.op === 'get') reads.add(t.map) })
    const addresses = [...reads].flatMap(map => {
      const w = m.step.maps?.[map]
      return w && 'key' in w ? [w.key] : []
    })
    const terms = [...new Map([key, ...addresses].map(t => [JSON.stringify(t), t])).values()]
    return [law.name, {[law.name]: terms}]
  }))
  const trees: Record<string, Tree> = Object.create(null) as Record<string, Tree>
  for (const goal of obligations(m, laws, instances)) {
    const got = grow(goal, new Map(), {nodes: 0, until})
    if (!('tree' in got)) return undefined
    trees[goal.name] = got.tree
  }
  const proof = {instances, trees}
  return checkLaws(m, laws, proof) ? proof : undefined
}
