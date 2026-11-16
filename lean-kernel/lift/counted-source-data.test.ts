import {expect, test} from 'bun:test'
import {atMost, n, x, type Law, type Machine} from '../../core/machine.ts'
import {countedObligations, leafConstraints, mcGoal, type CountCert, type Goal, type Tree} from '../../kernel/kernel.ts'
import {retainedCMachineToLean} from '../emit.ts'
import {countedSourceDefinitions} from './counted-source-data.ts'
import type {FamilyBundle} from './proof-capture.ts'

function contradiction(g: Goal): Tree {
  const index = leafConstraints(g, new Map()).findIndex(r => Object.keys(r.lin).every(k => k === '1') && (r.lin['1'] ?? 0) > 0)
  if (index < 0) throw Error('missing contradiction')
  return {leaf: [{kind: 'input', index}]}
}
function fixture(): FamilyBundle {
  const machine: Machine = {name:'source', params:['size'], inputs:[], state:{s:n(0)}, step:{state:{s:x('s')}}, counts:{empty:{j:'j',key:'key',below:n(0),body:n(0)}}}
  const laws: Law[] = [{name:'true', holds:atMost(n(0),n(0))}]
  const certs: Record<string, CountCert> = {}
  for (const {goal, decls} of countedObligations(machine, laws)) {
    const partial = {reads:[], insts:[]}, g = mcGoal(goal.hyps, decls, partial)
    if (!g) throw Error('missing goal')
    certs[goal.name] = {...partial, tree:contradiction(g)}
  }
  return {schema:'bapa-family/v1',route:'counted-family',original:{machine,laws},final:{phase:'closed-family',checked:true,machine,laws,proof:{instances:{},certs}},verdict:{proven:true,checked:true},identity:{} as FamilyBundle['identity'],terms:{terms:[],identities:[]},publicLawIndices:[0],projection:{kind:'same-machine',publicLawIndices:[0]}}
}
test('counted source is data only and leaves default retained output unchanged', () => {
  const b = fixture(), f = b.final
  const before = retainedCMachineToLean('sample',f.machine,f.laws,f.proof)
  const result = countedSourceDefinitions('sample', b)
  expect(result.producerText).toBe(before)
  expect(result.sourceDefs).toContain('def sample_source_decls : List CDecl')
  expect(result.sourceDefs).toContain('def sample_source_law0 : MLaw')
  expect(result.sourceDefs).not.toContain('theorem')
  expect(result.publicLawIndices).toEqual([0])
  expect(result.newCountMapIndices).toEqual([])
})
test('extra source names preserve the complete producer basis prefix',()=>{
 const f=fixture().final;let vars:string[]=[],maps:string[]=[]
 retainedCMachineToLean('prefix',f.machine,f.laws,f.proof,{after:b=>{vars=[...b.vars];maps=[...b.maps];return ''}})
 retainedCMachineToLean('prefix',f.machine,f.laws,f.proof,{extraVars:['sourceOnly'],extraMaps:['sourceMapOnly'],after:b=>{
  expect(b.vars.slice(0,vars.length)).toEqual(vars)
  expect(b.maps.slice(0,maps.length)).toEqual(maps)
  expect(b.vars.at(-1)).toBe('sourceOnly')
  expect(b.maps.at(-1)).toBe('sourceMapOnly')
  return ''
 }})
})
test('refuses missing and unsupported public claims', () => {
  const b = fixture()
  expect(() => countedSourceDefinitions('sample', {...b, original:{...b.original,laws:[{...b.original.laws[0]!,name:'absent'}]}})).toThrow('not present')
  expect(() => countedSourceDefinitions('sample', {...b, original:{...b.original,laws:[{...b.original.laws[0]!,some:['w']}]}})).toThrow('metadata')
})
