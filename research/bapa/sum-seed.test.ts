import {expect, test} from 'bun:test'
import {nat, proveRule, rule} from '../../core/dsl.ts'
import {proofOutput, type PublicProofOutput} from '../../core/proof-output.ts'
import {restateSeeds} from './candidate-seed-restatement.ts'
import type {Machine, Law} from '../../core/machine.ts'
import {checkLaws} from '../../kernel/kernel.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {restateSumSeeds} from './sum-seed.ts'

const native = () => rule('small sum fixture').params({size:nat}).sorts('Node').state({started:0}).maps({HasLock:0}).relations({Message:['Node','Node']}).step(({started})=>({started}))
const bindings = {maps:{OldLock:{target:'HasLock',sorts:['Node'],radix:4},OldMessage:{target:'Message',sorts:['Node','Node'],radix:4}},domains:{Node:'size'}}
const source = (target:Machine):Machine => ({...target, maps:{OldLock:0,OldMessage:0}, relations:undefined, step:{}, sums:{
  'sum$OldLock':{key:'kl',term:{op:'get',map:'OldLock',key:{op:'var',name:'kl'}}},
  'sum$OldMessage':{key:'km',term:{op:'get',map:'OldMessage',key:{op:'var',name:'km'}}},
}})

test('whole unary and tuple cell sums are native declarations and complete checked family',()=>{
  const r=native(), original=r.machine, s=source(original), result=restateSumSeeds(s,original,bindings)
  expect(result.substitutions).toEqual({'sum$OldLock':'sum$HasLock','sum$OldMessage':'sum$Message'})
  expect(result.nativeSums['sum$Message']).toEqual({key:'sum$Message$k',term:{op:'get',map:'Message',key:{op:'var',name:'sum$Message$k'}}})
  expect(original.sums).toBeUndefined()
  const helper:Law={name:'sum helper',holds:{op:'<=',a:{op:'add',a:{op:'var',name:result.substitutions['sum$OldLock']!},b:{op:'var',name:result.substitutions['sum$OldMessage']!}},b:{op:'var',name:'started'}}}
  const publicLaw=r.law('started stays zero',({started})=>started.atMost(0))
  const proofMachine=r.withSumsOf(helper).machine, family=[publicLaw,helper]
  expect(Object.keys(proofMachine.sums ?? {}).sort()).toEqual(['sum$HasLock','sum$Message'])
  const proof=proveLaws(proofMachine,family)
  expect(proof.proven && proof.checked).toBe(true)
  expect(checkLaws(proofMachine,family,proof.proof!)).toBe(true)
  const falseHelper:Law={name:'false helper',holds:{op:'not',x:helper.holds}}
  const bad=proveLaws(proofMachine,[publicLaw,falseHelper])
  expect(bad.proven && bad.checked).toBe(false)
  expect(original.sums).toBeUndefined()
},120000)

test('public proveRule captures original machine and a checked SUM family; false helper is dropped',()=>{
  const r=native(), original=r.machine, result=restateSumSeeds(source(original),original,bindings)
  const old:Law={name:'old sum',holds:{op:'<=',a:{op:'add',a:{op:'var',name:'sum$OldLock'},b:{op:'var',name:'sum$OldMessage'}},b:{op:'var',name:'started'}}}
  const translated=restateSeeds([old],original,bindings,{sumVariables:result.substitutions})[0]!
  expect(translated.status).toBe('candidate')
  if(translated.status!=='candidate') throw Error(translated.reason)
  const helper=translated.law, bad:Law={name:'bad helper',holds:{op:'not',x:helper.holds}}
  const laws=[r.law('started stays zero',({started})=>started.atMost(0))], events:PublicProofOutput[]=[], audits:any[]=[]
  const previous=proofOutput.on
  try {
    proofOutput.on=e=>events.push(e)
    const verdict=proveRule(r as never,laws,{search:true,candidateSeeds:{laws:[helper,bad],report:a=>audits.push(a)}})
    expect(verdict.proven && verdict.checked).toBe(true)
    expect(audits[0]?.status).toBe('checked')
    expect(audits[0]?.kept).toContain(helper.name)
    expect(audits[0]?.dropped.map((d:{name:string})=>d.name)).toContain('bad helper')
    expect(events).toHaveLength(1)
    expect(events[0]!.original.laws).toBe(laws)
    expect(events[0]!.original.machine.sums).toBeUndefined()
    let node=events[0]!.proof
    while(node?.kind==='derived') node=node.parents[0]
    expect(node?.kind).toBe('usual')
    if(node?.kind!=='usual') throw Error('missing checked family')
    expect(Object.keys(node.machine.sums ?? {}).sort()).toEqual(['sum$HasLock','sum$Message'])
    expect(node.laws.map(l=>l.name)).toContain(helper.name)
    expect(checkLaws(node.machine,node.laws,node.proof)).toBe(true)
    expect(original.sums).toBeUndefined()
  } finally {proofOutput.on=previous}
},120000)

test('refuses non-cell terms, bad binding, nonzero initial cells, and input maps',()=>{
  const target=native().machine, s=source(target)
  const bad:Machine={...s,sums:{...s.sums, other:{key:'k',term:{op:'get',map:'OldLock',key:{op:'const',value:0}}}}}
  expect(restateSumSeeds(bad,target,bindings).audit.find(a=>a.source==='other')?.status).toBe('dropped')
  expect(restateSumSeeds({...s,maps:{...s.maps,OldLock:1}},target,bindings).audit[0]?.status).toBe('dropped')
  expect(restateSumSeeds(s,{...target,inputMaps:['Message']},bindings).audit[1]?.status).toBe('dropped')
  expect(restateSumSeeds(s,{...target,relations:{Message:['Node']}},bindings).audit[1]?.status).toBe('dropped')
  expect(restateSumSeeds(s,{...target,relations:undefined},bindings).audit[1]?.status).toBe('candidate')
  expect(restateSumSeeds(s,target,{...bindings,maps:{...bindings.maps,OldMessage:{...bindings.maps.OldMessage,target:'missing'}}}).audit[1]?.status).toBe('dropped')
})
