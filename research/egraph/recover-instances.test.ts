import {expect,test} from 'bun:test'
import {get,n,x,same,not,type Law} from '../../core/machine.ts'
import {Meter} from './match.ts'
import {recoverInstances} from './recover-instances.ts'
const law:Law={name:'row',forall:'k',holds:same(get('R',x('k')),x('k'))}
test('recovery records only exact kernel-reconstructable existing positive rows',()=>{
  const row=same(get('R',n(3)),n(3)),g={name:'source',hyps:[row,{op:'and' as const,xs:[row,same(get('R',n(4)),n(4))]}]}
  const out=recoverInstances(g,[law],new Meter(10000));expect(out.instances).toEqual({row:[n(3),n(4)]});expect(out.records.map(r=>r.path)).toEqual([[0],[1,1]])
})
test('recovery rejects inconsistent repeated keys and hidden negative/disjunctive rows',()=>{
  const row=same(get('R',n(3)),n(3))
  const out=recoverInstances({name:'source',hyps:[same(get('R',n(3)),n(4)),not(row),{op:'or',xs:[row]}]},[law],new Meter(10000))
  expect(out.records).toEqual([])
})
test('recovery cannot invent an unbound key and remains work/record bounded',()=>{
  const row=same(get('R',n(3)),n(3)),g={name:'source',hyps:[row]}
  expect(recoverInstances(g,[{...law,keys:['unused']}],new Meter(10000)).records).toEqual([])
  expect(()=>recoverInstances(g,[law],new Meter(1))).toThrow('budget')
  expect(()=>recoverInstances(g,[law],new Meter(10000),0)).toThrow('record limit')
})
