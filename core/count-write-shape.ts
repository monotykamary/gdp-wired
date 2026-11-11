// Untrusted structural discovery for a threshold write at its source row.
// No operation, field, law, or protocol name is built in.
import {type C, type E, type Machine, walkOnce} from './machine.ts'
import {type CountGuardShape} from './count-guard-shape.ts'
const atoms = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(atoms) : [c]
export type CountThresholdWrite = {source: string, guard: string, increment: 0 | 1, input: string, inputCount: string, committedInput?: string, committedCount?: string}
const fields = (value: unknown): Set<string> => {const out = new Set<string>(); walkOnce(value, (node: any) => {if (node.op === 'get') out.add(node.map)}); return out}
export function discoverCountThresholdWrite(m: Machine, shape: CountGuardShape, choice: {name: string, value: number}): CountThresholdWrite | undefined {
  const write = m.step.maps?.[shape.thresholdField]
  if (!write || !('each' in write)) return
  const inputCount = (input: string) => Object.entries(m.counts ?? {}).filter(([, count]) => {
    const maps = fields(count.body)
    return !count.base && count.body.op === 'if' && count.body.then.op === 'const' && count.body.then.value === 1 && count.body.else.op === 'const' && count.body.else.value === 0 && maps.size === 1 && maps.has(input)
  }).map(([name]) => name)
  const candidates: CountThresholdWrite[] = []
  walkOnce(write.value, (node: any) => {
    if (node.op !== 'if') return
    let value: E = node.then, increment: 0 | 1 = 0
    if (value.op === 'add') {
      const [a, b] = value.a.op === 'const' ? [value.b, value.a] : [value.a, value.b]
      if (b.op !== 'const' || b.value !== 1) return
      value = a; increment = 1
    }
    if (value.op !== 'get' || value.map !== shape.memberField || value.key.op !== 'var' || !m.inputs.includes(value.key.name)) return
    const source = value.key.name, gate = atoms(node.c)
    if (!gate.some(c => c.op === '=' && ((c.a.op === 'var' && c.a.name === write.each && c.b.op === 'var' && c.b.name === source) || (c.b.op === 'var' && c.b.name === write.each && c.a.op === 'var' && c.a.name === source)))) return
    for (const c of gate) {
      if (c.op !== 'flag') continue
      const active = m.step.flags?.[c.name]
      if (!active || active.op === 'all' || !atoms(active).some(a => {
        if (a.op !== '=') return false
        const [v, n] = a.a.op === 'var' ? [a.a, a.b] : [a.b, a.a]
        return v.op === 'var' && v.name === choice.name && n.op === 'const' && n.value === choice.value
      })) continue
      const direct = [...fields(active)].filter(map => m.inputMaps?.includes(map))
      if (direct.length !== 1) continue
      const input = direct[0]!, ownCounts = inputCount(input)
      if (ownCounts.length !== 1) continue
      const all = new Set(fields(active)), seen = new Set<string>()
      const expand = (value: C): void => walkOnce(value, (node: any) => {
        if (node.op !== 'flag' || seen.has(node.name)) return
        seen.add(node.name)
        const flag = m.step.flags?.[node.name]
        if (flag) {for (const field of fields(flag)) all.add(field); expand(flag)}
      })
      expand(active)
      const other = [...all].filter(map => map !== input && m.inputMaps?.includes(map))
      if (other.length > 1) continue
      const committedInput = other[0], committed = committedInput ? inputCount(committedInput) : []
      if (committedInput && committed.length !== 1) continue
      candidates.push({source, guard: c.name, increment, input, inputCount: ownCounts[0]!, ...(committedInput ? {committedInput, committedCount: committed[0]!} : {})})
    }
  })
  const unique = [...new Map(candidates.map(value => [JSON.stringify(value), value])).values()]
  return unique.length === 1 ? unique[0] : undefined
}
