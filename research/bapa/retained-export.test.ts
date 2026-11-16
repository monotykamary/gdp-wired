import {expect, test} from 'bun:test'
import {atMost, n, x, type Law, type Machine} from '../../core/machine.ts'
import {checkCountedLaws, checkLaws, countedObligations, leafConstraints, mcGoal, obligations, type Goal, type Tree, type CountCert} from '../../kernel/kernel.ts'
import {retainedCMachineToLean, retainedSMachineToLean, seedStepProof, smachineToLean} from '../../lean-kernel/emit.ts'

// Constant contradictions give checked certificates without invoking search. The
// unused bound is symbolic, not an assertion about any bounded source model.
function contradiction(g: Goal): Tree {
  const rows = leafConstraints(g, new Map())
  const index = rows.findIndex(r => Object.keys(r.lin).every(k => k === '1') && (r.lin['1'] ?? 0) > 0)
  if (index < 0) throw Error('missing constant contradiction')
  return {leaf: [{kind: 'input', index}]}
}
function plain() {
  const machine: Machine = {name: 'symbolic', params: ['size'], inputs: [], state: {s: n(0)}, step: {state: {s: x('s')}}}
  const laws: Law[] = [{name: 'true law', holds: atMost(n(0), n(0))}]
  const proof = {instances: {}, trees: Object.fromEntries(obligations(machine, laws).map(g => [g.name, contradiction(g)]))}
  return {machine, laws, proof}
}
function counted() {
  const p = plain(), machine: Machine = {...p.machine, counts: {empty: {j: 'j', key: 'countKey', below: n(0), body: n(0)}}}
  const certs: Record<string, CountCert> = {}
  for (const {goal, decls} of countedObligations(machine, p.laws)) {
    const partial = {reads: [], insts: []}
    const g = mcGoal(goal.hyps, decls, partial)
    if (!g) throw Error('missing counted goal')
    certs[goal.name] = {...partial, tree: contradiction(g)}
  }
  return {machine, laws: p.laws, proof: {instances: {}, certs}}
}
test('usual retained export uses supplied proof and restores a prior cache entry', () => {
  const p = plain()
  expect(checkLaws(p.machine, p.laws, p.proof)).toBe(true)
  seedStepProof(p.machine, p.laws, [], {proven: false, checked: false, nodes: 0, leaves: 0})
  const text = retainedSMachineToLean('symbolic', p.machine, p.laws, p.proof)
  expect(text).toContain('decide +kernel')
  expect(text).not.toContain('native_decide')
  expect(text).toContain('symbolic_machine')
  expect(() => smachineToLean('prior', p.machine, p.laws)).toThrow('not proven')
  expect(() => retainedSMachineToLean('bad', p.machine, p.laws, {instances: {}, trees: {}})).toThrow('does not check')
})
test('counted retained export checks its certificate and rejects corruption', () => {
  const p = counted()
  expect(checkCountedLaws(p.machine, p.laws, p.proof)).toBe(true)
  const text = retainedCMachineToLean('counted', p.machine, p.laws, p.proof)
  expect(text).toContain('List CEntry')
  expect(text).toContain('decide +kernel')
  expect(text).not.toContain('native_decide')
  expect(() => retainedCMachineToLean('bad', p.machine, p.laws, {instances: {}, certs: {}})).toThrow('does not check')
})
test('malformed Lean identifiers are rejected before checking or emitting', () => {
  const p = plain()
  for (const id of ['x\naxiom forged : False', 'a.b', 'a-b', '']) {
    expect(() => retainedSMachineToLean(id,p.machine,p.laws,p.proof)).toThrow('identifier')
    expect(() => retainedCMachineToLean(id,p.machine,p.laws,{instances:{},certs:{}})).toThrow('identifier')
  }
})
test('unsupported projections fail closed before export', () => {
  const p = plain()
  const history = {...p.machine, history: {} as NonNullable<Machine['history']>}
  expect(() => retainedSMachineToLean('bad', history, p.laws, p.proof)).toThrow('history/sums')
  const unresolved: Law[] = [{...p.laws[0]!, some: ['w']}]
  expect(() => retainedSMachineToLean('bad', p.machine, unresolved, p.proof)).toThrow('resolved witness')
  expect(() => retainedCMachineToLean('bad', history, p.laws, {instances: {}, certs: {}})).toThrow('history/sums')
})
