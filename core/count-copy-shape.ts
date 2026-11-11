// Structural hints only; a matched write still needs an ordinary checked proof.
import {type C, type Machine, walkOnce} from './machine.ts'
import {type CountGuardShape} from './count-guard-shape.ts'
const atoms = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(atoms) : [c]
export type CountRowCopy = {from: string, to: string, guard: string}
export function discoverCountRowCopy(m: Machine, shape: CountGuardShape, choice: {name: string, value: number}): CountRowCopy | undefined {
  const write = m.step.maps?.[shape.thresholdField]
  if (!write || !('each' in write)) return
  const found: CountRowCopy[] = []
  walkOnce(write.value, (node: any) => {
    if (node.op !== 'if' || node.then.op !== 'get' || node.then.map !== shape.thresholdField || node.then.key.op !== 'var' || !m.inputs.includes(node.then.key.name)) return
    const gate = atoms(node.c), target = gate.flatMap(c => {
      if (c.op !== '=') return []
      const [a, b] = c.a.op === 'var' && c.a.name === write.each ? [c.a, c.b] : [c.b, c.a]
      return a.op === 'var' && a.name === write.each && b.op === 'var' && m.inputs.includes(b.name) ? [b.name] : []
    })
    if (target.length !== 1) return
    for (const c of gate) {
      if (c.op !== 'flag') continue
      const guard = m.step.flags?.[c.name]
      if (!guard || guard.op === 'all' || !atoms(guard).some(a => {
        if (a.op !== '=') return false
        const [v, n] = a.a.op === 'var' ? [a.a, a.b] : [a.b, a.a]
        return v.op === 'var' && v.name === choice.name && n.op === 'const' && n.value === choice.value
      })) continue
      let used = false
      walkOnce(m.step.maps?.[shape.membershipMap], (node: any) => {if (node.op === 'flag' && node.name === c.name) used = true})
      if (used) found.push({from: node.then.key.name, to: target[0]!, guard: c.name})
    }
  })
  const unique = [...new Map(found.map(copy => [JSON.stringify(copy), copy])).values()]
  return unique.length === 1 ? unique[0] : undefined
}
