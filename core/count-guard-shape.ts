// Untrusted structural discovery for optional guarded-count strategies.
// A match supplies names and existing laws, never a premise or a verdict.
import {type C, type Counted, type Law, type Machine, n, walkOnce, x} from './machine.ts'
import {substC} from '../kernel/kernel.ts'

export type CountGuardShape = {
  voteMap: string
  rowMap: string
  memberField: string
  thresholdField: string
  memberKey: string
  rowKey: string
  otherKey: string
  width: number
  membershipMap: string
  phase?: {name: string, laws: Law[]}
  weakerLaw?: Law
}
const json = (value: unknown) => JSON.stringify(value)
const atoms = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(atoms) : [c]
const indicator = (d: Counted): d is Counted & {body: Extract<Counted['body'], {op: 'if'}>} =>
  d.body.op === 'if' && json(d.body.then) === json(n(1)) && json(d.body.else) === json(n(0))

export function discoverCountGuardShape(m: Machine, law: Law, family: readonly Law[]): CountGuardShape | undefined {
  if (!law.forall || law.keys?.length !== 1) return
  let voteMap: string | undefined, rowMap: string | undefined
  walkOnce(law.holds, (node: any) => {
    if (node.op !== '<=' || node.a.op !== 'mul' || node.a.k !== 2 || node.a.a.op !== 'get' || node.b.op !== 'get') return
    const vote = m.counts?.[node.a.a.map], row = m.counts?.[node.b.map]
    if (!vote?.base || !row || row.base || !indicator(vote) || !indicator(row) || json(vote.below) !== json(row.below)) return
    const packed = node.a.a.key
    if (packed.op !== 'add' || packed.a.op !== 'mul' || packed.a.k !== vote.base || json(packed.a.a) !== json(x(law.forall!)) || json(packed.b) !== json(x(law.keys![0]!)) || json(node.b.key) !== json(x(law.forall!))) return
    const membership = substC(row.body.c, {vars: {[row.j]: x(vote.j), [row.key]: x(vote.key)}, maps: {}, flags: {}})
    if (!atoms(vote.body.c).some(c => json(c) === json(membership))) return
    voteMap = node.a.a.map; rowMap = node.b.map
  })
  if (!voteMap || !rowMap) return
  const vote = m.counts![voteMap]!
  if (!indicator(vote)) return
  const comparisons = atoms(vote.body.c)
  const threshold = comparisons.find(c => c.op === '<' && c.a.op === 'get' && c.b.op === 'get' && json(c.a.key) === json(x(vote.key)) && json(c.b.key) === json(x(vote.lo ?? vote.j)))
  if (!threshold || threshold.op !== '<' || threshold.a.op !== 'get' || threshold.b.op !== 'get' || !(threshold.a.map in (m.maps ?? {})) || !(threshold.b.map in (m.maps ?? {}))) return
  const thresholdField = threshold.b.map, phaseNames = new Set<string>(), phaseLaws: Law[] = []
  for (const candidate of family) {
    if (!candidate.forall || candidate.keys?.length) continue
    const fields = new Set<string>(), variables = new Set<string>()
    walkOnce(candidate.holds, (node: any) => {if (node.op === 'get') fields.add(node.map); if (node.op === 'var') variables.add(node.name)})
    const phases = Object.keys(m.state).filter(name => variables.has(name))
    if (fields.size && [...fields].every(name => name === thresholdField) && phases.length) {
      phases.forEach(name => phaseNames.add(name)); phaseLaws.push(candidate)
    }
  }
  // Several existing zero-phase laws can hold (e.g. before selection and
  // before activation). Prefer only a unique phase named by every non-frame
  // threshold-write guard. This remains a proposal: all resulting proofs check.
  if (phaseNames.size > 1) {
    const write = m.step.maps?.[thresholdField], gates: Set<string>[] = []
    if (write && 'each' in write) walkOnce(write.value, (node: any) => {
      if (node.op !== 'if' || node.then.op === 'if' || node.then.op === 'get' && node.then.map === thresholdField && node.then.key.op === 'var' && node.then.key.name === write.each) return
      const names = new Set<string>(), seen = new Set<string>()
      const scan = (value: C): void => walkOnce(value, (part: any) => {
        if (part.op === 'var' && phaseNames.has(part.name)) names.add(part.name)
        if (part.op === 'flag' && !seen.has(part.name)) {seen.add(part.name); const flag = m.step.flags?.[part.name]; if (flag) scan(flag.op === 'all' ? flag.c : flag)}
      })
      scan(node.c); gates.push(names)
    })
    const common = gates.length ? [...phaseNames].filter(name => gates.every(gate => gate.has(name))) : []
    if (common.length === 1) {phaseNames.clear(); phaseNames.add(common[0]!)}
  }
  const serialized = new Set(comparisons.map(json))
  const weakerLaw = family.find(candidate => {
    if (!candidate.forall || candidate.keys?.length !== 1) return false
    let found = false
    walkOnce(candidate.holds, (node: any) => {
      const count = node.op === 'get' && m.counts?.[node.map]
      if (count && node.map !== voteMap && count.base && indicator(count) && atoms(count.body.c).length < comparisons.length && atoms(count.body.c).every(c => serialized.has(json(c)))) found = true
    })
    return found
  })
  const row = m.counts![rowMap]!
  const membershipMaps = new Set<string>()
  if (indicator(row)) walkOnce(row.body.c, (node: any) => {if (node.op === 'get') membershipMaps.add(node.map)})
  if (membershipMaps.size !== 1) return
  return {membershipMap: [...membershipMaps][0]!, voteMap, rowMap, memberField: threshold.a.map, thresholdField, memberKey: vote.key, rowKey: vote.j, otherKey: vote.lo ?? vote.j, width: vote.base!, ...(phaseNames.size === 1 ? {phase: {name: [...phaseNames][0]!, laws: phaseLaws.filter(law => {let found = false; walkOnce(law.holds, (node: any) => {if (node.op === 'var' && phaseNames.has(node.name)) found = true}); return found})}} : {}), ...(weakerLaw ? {weakerLaw} : {})}
}
