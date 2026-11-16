import {type C, type E, type Law, type Machine} from '../../core/machine.ts'
import {type RigidSignature} from './rigid-instance.ts'
import {lowerRigid} from './rigid-lower.ts'
import {substC} from '../../kernel/kernel.ts'
const V = (variable: string) => ({variable})
export const rigidQuorumSignature: RigidSignature = {
  sorts: {Node: 'nodes', Quorum: 'quorums', Value: 'values'},
  symbols: {member: {args: ['Node', 'Quorum']}},
  axioms: [{name: 'intersection', forall: [{name: 'q1', sort: 'Quorum'}, {name: 'q2', sort: 'Quorum'}], exists: {name: 'n', sort: 'Node'}, body: [
    {relation: 'member', args: [V('n'), V('q1')]}, {relation: 'member', args: [V('n'), V('q2')]},
  ]}],
}
export const rigidMinimalBase: Machine = {name: 'rigid minimal no-helper', params: ['nodes', 'quorums', 'values'], inputs: [], state: {}, step: {}}
export const rigidMinimal = () => lowerRigid(rigidMinimalBase, rigidQuorumSignature)

// Diagnostic control ONLY. This hand-supplied search seed is GIVEN, not found.
// It is a consequence of the universal axiom. The default-OFF legacy search
// needs this assistance; the separately tested opt-in strategy does not.
// The generic lowerer supplies no seed.
export function rigidMinimalGivenZero() {
  const p = rigidMinimal(), ax = p.abstractMachine.facts!.find(f => f.forall && f.name.includes('axiom'))!
  const keys = [ax.forall!, ...ax.keys ?? []]
  const ground: Law = {name: 'GIVEN intersection instance at (0,0)', holds: substC(ax.holds, {vars: Object.fromEntries(keys.map(key => [key, {op: 'const', value: 0} as E])), maps: {}, flags: {}})}
  return {...p, abstractMachine: {...p.abstractMachine, name: 'rigid minimal GIVEN zero-tuple seed', facts: [...p.abstractMachine.facts!, ground]}}
}
const variable = (name: string): E => ({op: 'var', name}), zero: E = {op: 'const', value: 0}
export const rigidMinimalLaw: Law = {name: 'inhabited quorum implies inhabited node', holds: {op: 'or', xs: [
  {op: 'not', x: {op: '<', a: zero, b: variable('quorums')}}, {op: '<', a: zero, b: variable('nodes')},
]} as C}
