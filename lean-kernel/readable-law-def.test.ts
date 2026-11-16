import {expect, test} from 'bun:test'
import type {Law, Machine} from '../core/machine.ts'
import {n, x} from '../core/machine.ts'
import {machineNodes, proveCyclic} from '../core/cyclic.ts'
import {proveLaws} from '../kernel/prove.ts'
import {cycMachineToLean, readable, toLean} from './emit.ts'

const laws: Law[] = [{name: 'zero stays zero', holds: {op: '=', a: x('x'), b: n(0)}}]
const machine: Machine = {name: 'zero', params: [], inputs: [], state: {x: n(0)}, step: {state: {x: n(0)}}}
const reach = {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: 'SReach fixture_machine ρ μ', call: 'fixture_laws ρ μ h'}

test('inline law definitions retain their original surface simplification', () => {
  const text = readable('fixture', laws, ['x'], [], reach)
  expect(text).toContain("by simpa [fixture_l0, holdsC, evalE, upd] using hl'")
  expect(text).not.toContain('fixture_law0')
})

test('a separate cyclic law definition is unfolded with its MLaw wrapper', () => {
  const text = readable('fixture', laws, ['x'], [], {...reach, lawDef: j => `fixture_law${j}`})
  expect(text).toContain("by simpa [fixture_l0, fixture_law0, holdsC, evalE, upd] using hl'")
  expect(text).toContain('theorem law0')
  expect(text).toContain('ρ «x» = 0')
})

test('each corollary unfolds only its own separate law definition', () => {
  const text = readable('fixture', [...laws, {...laws[0]!, name: 'second zero law'}], ['x'], [], {...reach, lawDef: j => `fixture_law${j}`})
  expect(text).toContain('[fixture_l0, fixture_law0, holdsC, evalE, upd]')
  expect(text).toContain('[fixture_l1, fixture_law1, holdsC, evalE, upd]')
  expect(text).not.toContain('[fixture_l0, fixture_law0, fixture_law1')
})

function exported(id: string, input: Machine): string {
  const result = cycMachineToLean(id, input, laws)
  if ('why' in result) throw new Error(result.why)
  return result.text
}

test('the cyclic machine exporter supplies its separate condition definition', () => {
  const text = exported('cyclic_scalar', machine)
  expect(text).toContain('def cyclic_scalar_law0 : C :=')
  expect(text).toContain('[cyclic_scalar_l0, cyclic_scalar_law0, holdsC, evalE, upd]')
})

test('an explicitly supplied cyclic bridge unfolds its separate law definition', () => {
  const usual = proveLaws(machine, laws)
  if (!usual.proven || !usual.proof) throw new Error('fixture has no checked usual proof')
  const nodes = machineNodes(machine, laws, usual.proof.instances)
  const cyclic = proveCyclic(nodes.facts, nodes.specs)
  if (!cyclic.proven || !cyclic.checked) throw new Error('fixture has no checked cyclic proof')
  const text = toLean([{id: 'explicit_bridge', cyclic: cyclic.proof, bridge: {machine, laws}}])
  expect(text).toContain('def explicit_bridge_law0 : C :=')
  expect(text).toContain('[explicit_bridge_l0, explicit_bridge_law0, holdsC, evalE, upd]')
})

test('the cyclic history exporter supplies its separate condition definition', () => {
  const text = exported('cyclic_history', {...machine, inputs: ['request'], history: {keep: {op: '=', a: n(0), b: n(0)}, record: ['request'], sums: {}, queries: {}}})
  expect(text).toContain('HReach cyclic_history_hist ρ μ hist')
  expect(text).toContain('[cyclic_history_l0, cyclic_history_law0, holdsC, evalE, upd]')
})
