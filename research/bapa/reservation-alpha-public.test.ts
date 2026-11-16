// Isolated test: force only the untrusted ordinary pass-one proposer.
// The public entry point, proof construction and final native checker stay real.
import {expect,mock,test} from 'bun:test'
import {nat,proveRule,rule} from '../../core/dsl.ts'
import {countsDump,countedAttempts} from '../../core/counts.ts'
import * as strategies from '../../core/count-strategies.ts'
import {proofOutput,type PublicProofOutput} from '../../core/proof-output.ts'
import {checkCountedLaws} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import type {Law,Machine} from '../../core/machine.ts'
const original={...strategies}
const propose=(m:Machine,context:Law[],target:Law,end:number)=>{
 const out=countedAttempts(m,[target],new Set(context),end).traced(target,context,1,Math.max(0,end-clock()),false)
 return 'proof'in out?out.proof:undefined
}
await mock.module('../../core/count-strategies.ts',()=>({...original,prepareCountStrategyMachine:(m:Machine)=>m,selectedCountStrategies:(_m:Machine,f:Law[])=>f,proposeCountStrategiesForClosing:propose,proveCountStrategies:propose,proposeCountStrategyKindForClosing:(_kind:unknown,...args:Parameters<typeof propose>)=>propose(...args)}))
const v=(name:string)=>({op:'var' as const,name}),n=(value:number)=>({op:'const' as const,value})
test('public seeded count proof freshens a source-bound witness and retains its provenance',()=>{
 const r=rule('reservation alpha public').params({size:nat}).inputs({key:nat}).assume(({key,size})=>key.lt(size)).state({started:0}).maps({Cell:0})
  .counts({Total:({Cell,size})=>({below:size,body:(_j,k)=>Cell.at(k)})}).step(({Cell,key})=>({started:1,Cell:Cell.set(key,1)}))
 const goal:Law={name:'sum of bits bounded',holds:{op:'or',xs:[{op:'=',a:v('started'),b:n(0)},{op:'<=',a:{op:'get',map:'Total',key:n(0)},b:v('size')}]}}
 const seed:Law={name:'bit bound',forall:'w$0',holds:{op:'<=',a:{op:'get',map:'Cell',key:v('w$0')},b:n(1)}}
 const events:any[]=[],outputs:PublicProofOutput[]=[],audits:any[]=[],old=countsDump.on,prior=proofOutput.on
 try{
  countsDump.on=e=>events.push(e);proofOutput.on=e=>outputs.push(e)
  const out=proveRule(r as never,[goal],{search:true,candidateSeeds:{kind:'counted',laws:[seed],report:a=>audits.push(a)}})
  console.log(JSON.stringify({out,audits,events:events.map(e=>({phase:e.phase,law:e.law,goal:e.goal,pass:e.pass,checked:e.checked,reason:e.reason,error:String(e.error??''),renamings:e.renamings})),proof:outputs.map(o=>o.proof?.kind)}))
  expect(out.proven&&out.checked).toBe(true)
  expect(audits[0]).toMatchObject({status:'checked'})
  expect(events.some(e=>e.phase==='reservation-alpha'&&e.renamings.some((r:any)=>r.from==='w$0'&&r.to!=='w$0'&&r.reason==='source-freshness'))).toBe(true)
  expect(outputs).toHaveLength(1)
  let leaf=outputs[0]!.proof;while(leaf?.kind==='derived')leaf=leaf.parents[0]
  if(leaf?.kind!=='counted')throw Error('missing counted leaf')
  expect(checkCountedLaws(leaf.machine,leaf.laws,leaf.proof)).toBe(true)
  expect(Object.values(leaf.proof.certs).some((c:any)=>c.proposalProvenance?.kind==='reservation-alpha')).toBe(true)
  expect(seed.forall).toBe('w$0')
 }finally{countsDump.on=old;proofOutput.on=prior}
},120000)
