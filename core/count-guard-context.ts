// One conservative definition extension, shared by every operation case.
// This prepares syntax only; no discovered relationship becomes an assumption.
import {type Law, type Machine, walkOnce} from './machine.ts'
import {type CountGuardShape, discoverCountGuardShape} from './count-guard-shape.ts'
import {type Restriction, restrictedCounts} from './count-restrictions.ts'
export type GuardCountContext = {original: Machine, machine: Machine, shape: CountGuardShape, restrictions: Restriction[], inputCounts: Record<string, string>}
export function prepareGuardCountContext(original: Machine, law: Law, family: readonly Law[]): GuardCountContext | undefined {
  const shape = discoverCountGuardShape(original, law, family)
  if (!shape) return
  const inputCounts: Record<string, string> = {}, selected = [shape.voteMap, shape.rowMap]
  for (const input of original.inputMaps ?? []) {
    const found = Object.entries(original.counts ?? {}).filter(([, d]) => {
      if (d.base || d.body.op !== 'if' || d.body.then.op !== 'const' || d.body.then.value !== 1 || d.body.else.op !== 'const' || d.body.else.value !== 0) return false
      const fields = new Set<string>()
      walkOnce(d.body, (node: any) => {if (node.op === 'get') fields.add(node.map)})
      return fields.size === 1 && fields.has(input)
    })
    if (found.length !== 1) return
    inputCounts[input] = found[0]![0]; selected.push(found[0]![0])
  }
  if (selected.length * (original.inputMaps?.length ?? 0) > 128) return
  const reserved = new Set([...original.params, ...original.inputs, ...Object.keys(original.fns ?? {}), ...Object.keys(original.step.flags ?? {})])
  for (const base of selected) for (const input of original.inputMaps ?? []) {
    const name = `${base}$restricted$${input}`
    if (reserved.has(name) || reserved.has(name + '$not')) return
  }
  try {
    // Reuse only exact definitions installed at the admission boundary. A name
    // collision is never permission to replace a user count or add a premise.
    const planned = new Set(selected.flatMap(base => (original.inputMaps ?? []).flatMap(input => [`${base}$restricted$${input}`, `${base}$restricted$${input}$not`])))
    const source = {...original, counts: Object.fromEntries(Object.entries(original.counts ?? {}).filter(([name]) => !planned.has(name)))}
    const extended = restrictedCounts(source, selected, 128, shape.memberKey)
    for (const name of planned) if (original.counts?.[name] && JSON.stringify(original.counts[name]) !== JSON.stringify(extended.machine.counts?.[name])) return
    const added = Object.keys(extended.machine.counts ?? {}).some(name => !original.counts?.[name])
    const machine = added ? {...original, counts: {...original.counts, ...extended.machine.counts}} : original
    return {original, machine, shape, restrictions: extended.entries, inputCounts}
  } catch { return }
}
