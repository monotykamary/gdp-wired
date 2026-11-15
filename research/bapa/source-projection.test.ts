import {expect,test} from 'bun:test'
import type {Machine} from '../../core/machine.ts'
import {alphaProposals,emitAlphaSource} from './source-projection.ts'
import type {NativeBundle} from './proof-capture.ts'

const q=(key:string)=>({op:'all',key,c:{op:'=',a:{op:'var',name:key},b:{op:'const',value:0}}})
const machine=(key:string)=>({step:{flags:{ok:q(key)}}}) as unknown as Machine

test('only proposes positional quantified flag binder differences',()=>{
  expect(alphaProposals(machine('old'),machine('fresh'))).toEqual([{flag:'ok',old:'old',fresh:'fresh'}])
  expect(alphaProposals(machine('same'),machine('same'))).toEqual([])
})
test('binder arity mismatch is refused',()=>{
  const p=machine('fresh')
  const flag=p.step.flags!.ok!
  if(flag.op !== 'all') throw Error('fixture')
  flag.keys=['extra']
  expect(()=>alphaProposals(machine('old'),p)).toThrow('arity')
})
test('a capture candidate is only proposed, never validated in JS',()=>{
  const source=machine('old')
  const flag=source.step.flags!.ok!
  if(flag.op !== 'all') throw Error('fixture')
  flag.c={op:'=',a:{op:'var',name:'old'},b:{op:'var',name:'fresh'}}
  expect(alphaProposals(source,machine('fresh'))).toEqual([{flag:'ok',old:'old',fresh:'fresh'}])
  // The emitted validAll check, not this proposal, must reject capture.
})
test('refuses public law metadata needing a separate semantic interpretation',()=>{
  for(const extra of [{stated:{}},{some:[]},{ex:{}},{finite:'size'},{witness:{}}]){
    const law={name:'x',holds:{},...extra},m=machine('old')
    const leaf={kind:'usual',machine:m,laws:[law],proof:{instances:{},trees:{}}}
    const bundle={schema:'bapa-proof/v1',route:'plain',verdict:{proven:true,checked:true},original:{machine:m,laws:[law]},proof:leaf} as unknown as NativeBundle
    expect(()=>emitAlphaSource('x',bundle)).toThrow('ordinary public laws')
  }
})
test('refuses counted or witness rather than asserting source soundness',()=>{
  expect(()=>emitAlphaSource('x',{schema:'bapa-family/v1',route:'counted-family'} as NativeBundle)).toThrow()
  expect(()=>emitAlphaSource('x',{schema:'bapa-proof/v1',route:'witness'} as NativeBundle)).toThrow()
})
