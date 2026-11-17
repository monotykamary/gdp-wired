import {expect,test} from 'bun:test'
import type {E,Machine} from '../core/machine.ts'
import {wordDivisionKey,wordDivisionName} from '../kernel/word-division.ts'
import {leanProject,wordDigitRangeMachineToLean} from './emit.ts'

function fixture(width:8|16|32|64,part:'q'|'r'|'c',index=0):Machine{
  if(part==='c'&&index===0)index=1
  const n=width===8?1:width/16,inputs=Array.from({length:2*n},(_,i)=>'x'+i)
  const key=wordDivisionKey(inputs.map((name):E=>({op:'var',name})))
  return{name:'restricted helper fixture',params:[],inputs,state:{out:{op:'const',value:0}},
    step:{state:{out:{op:'get',map:wordDivisionName(width,part,index),key}}}}
}

test('restricted helper exports are standalone and ship their complete proof dependencies',()=>{
  for(const width of [8,16,32,64] as const)for(const part of ['q','r','c'] as const){
    const m=fixture(width,part),source=wordDigitRangeMachineToLean('helper',m)
    expect(source.startsWith('import WordDivisionBridge\n')).toBe(true)
    expect(source).toContain('theorem helper_range')
    expect(source).toContain('WordDivisionBridge.checkEntries_sound')
    const project=leanProject(source)
    expect(project['WordDivision.lean']).toContain('namespace WordDivision')
    expect(project['WordDivisionBridge.lean']).toContain('theorem checkEntries_sound')
    expect(project['Proofs.lean']).toBe(source)
  }
})

test('restricted helper exports reject every auxiliary or unknown semantic field',()=>{
  for(const key of ['primitiveFailure','pre','assume','maps','fns','facts','inputMaps','counts','leasts','relations','history','sums','futureField']){
    const m=Object.assign(fixture(8,'q'),{[key]:undefined})
    expect(()=>wordDigitRangeMachineToLean('bad',m)).toThrow()
  }
  for(const key of ['maps','flags','futureField']){
    const m=fixture(8,'q');Object.assign(m.step,{[key]:undefined})
    expect(()=>wordDigitRangeMachineToLean('bad',m)).toThrow()
  }
})

test('restricted helper exports refuse a different initialized or updated machine',()=>{
  const init=fixture(8,'q');init.state.out={op:'const',value:1}
  expect(()=>wordDigitRangeMachineToLean('bad',init)).toThrow()
  const changed=fixture(8,'q');changed.step.state!.out={op:'const',value:0}
  expect(()=>wordDigitRangeMachineToLean('bad',changed)).toThrow()
  expect(()=>wordDigitRangeMachineToLean('bad injection',fixture(8,'q'))).toThrow()
})
