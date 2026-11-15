import {expect, test} from 'bun:test'
import {nat, proveRule, rule} from '../../core/dsl.ts'
import {proofOutput, type PublicProofOutput} from '../../core/proof-output.ts'
import {restateSeeds} from './candidate-seed-restatement.ts'
import type {C, E, Machine, Law} from '../../core/machine.ts'
import {checkLaws, mapArities, sumMachine} from '../../kernel/kernel.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {restateSumSeeds} from './sum-seed.ts'
import {proposeTupleSumCells} from './tuple-sum-seed.ts'

// A real binary read/write, not an unused relation declaration. The old unary
// Message SUM passed the latter fixture but fails mapArities on this one.
const native = (broken=false) => rule('tuple sum fixture').params({size:nat}).inputs({a:nat,b:nat}).sorts('Node').state({started:0}).maps({HasLock:0}).relations({Message:['Node','Node']}).step(({started,a,b,Message})=>({started,Message:broken?Message.add([a,b]):Message.remove([a,b])}))
const bindings = {maps:{OldLock:{target:'HasLock',sorts:['Node'],radix:4},OldMessage:{target:'Message',sorts:['Node','Node'],radix:4}},domains:{Node:'size'}}
const source = (target:Machine):Machine => ({...target, maps:{OldLock:0,OldMessage:0}, relations:undefined, step:{}, sums:{
  'sum$OldLock':{key:'kl',term:{op:'get',map:'OldLock',key:{op:'var',name:'kl'}}},
  'sum$OldMessage':{key:'km',term:{op:'get',map:'OldMessage',key:{op:'var',name:'km'}}},
}})
const old:Law={name:'old sum',holds:{op:'<=',a:{op:'add',a:{op:'var',name:'sum$OldLock'},b:{op:'var',name:'sum$OldMessage'}},b:{op:'var',name:'started'}}}
const empty:Law={name:'no messages',forall:'u',keys:['v'],holds:{op:'=',a:{op:'get',map:'Message',key:{op:'tup',a:{op:'var',name:'u'},b:{op:'var',name:'v'}}},b:{op:'const',value:0}}}
const translate=(original:Machine)=>{
  const sums=restateSumSeeds(source(original),original,bindings)
  const item=restateSeeds([old],original,bindings,{sumVariables:sums.substitutions,tupleSums:sums.tupleSums})[0]!
  if(item.status!=='candidate')throw Error(item.reason)
  return {sums,item,helper:item.law}
}

test('unary SUM plus full-arity tuple sub-sums form a complete checked family',()=>{
  const r=native(), original=r.machine, {sums,item,helper}=translate(original)
  expect(mapArities(original).Message).toBe(2)
  expect(sums.substitutions).toEqual({'sum$OldLock':'sum$HasLock'})
  expect(Object.keys(sums.nativeSums)).toEqual(['sum$HasLock'])
  expect(sums.audit[1]).toMatchObject({status:'tuple-proposal',arity:2,projection:'finite-subsum',globalTotal:false})
  expect(item.tupleSumProjection).toMatchObject({arity:2,points:2,globalTotal:false})
  expect([helper.forall,...helper.keys!]).toHaveLength(4)
  expect(JSON.stringify(helper)).not.toContain('sum$OldMessage')
  expect(JSON.stringify(helper)).not.toContain('sum$Message')
  expect(original.sums).toBeUndefined()
  const proofMachine=r.withSumsOf(helper).machine, family=[empty,helper]
  expect(Object.keys(proofMachine.sums ?? {})).toEqual(['sum$HasLock'])
  expect(mapArities(sumMachine(proofMachine).machine).Message).toBe(2)
  const proof=proveLaws(proofMachine,family)
  expect(proof.proven && proof.checked).toBe(true)
  expect(checkLaws(proofMachine,family,proof.proof!)).toBe(true)
  const bad=proveLaws(proofMachine,[empty,{...helper,name:'false helper',holds:{op:'not',x:helper.holds}}])
  expect(bad.proven && bad.checked).toBe(false)
  expect(original.sums).toBeUndefined()
},120000)

test('public proveRule checks tuple writes, unchanged source, and a false-helper control',()=>{
  const r=native(), original=r.machine, {helper}=translate(original)
  const bad:Law={...helper,name:'bad helper',holds:{op:'not',x:helper.holds}}
  const laws=[empty], events:PublicProofOutput[]=[], audits:any[]=[]
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
    expect(events[0]!.original.machine).toEqual(original)
    let node=events[0]!.proof
    while(node?.kind==='derived') node=node.parents[0]
    expect(node?.kind).toBe('usual')
    if(node?.kind!=='usual') throw Error('missing checked family')
    expect(Object.keys(node.machine.sums ?? {})).toEqual(['sum$HasLock'])
    expect(node.laws.map(l=>l.name)).toContain(helper.name)
    expect(checkLaws(node.machine,node.laws,node.proof)).toBe(true)
    expect(original.sums).toBeUndefined()
  } finally {proofOutput.on=previous}
},120000)

test('a changed binary write cannot use projected candidates to prove a false public goal',()=>{
  const r=native(true), {helper}=translate(r.machine)
  const verdict=proveRule(r as never,[empty],{search:true,candidateSeeds:{laws:[helper]}})
  expect(verdict.proven && verdict.checked).toBe(false)
},120000)

test('tuple distinctness is disjunctive, and budget-two projection is not a global total',()=>{
  const p=proposeTupleSumCells(old,{'sum$OldMessage':{sourceMap:'OldMessage',targetMap:'Message',arity:2}})
  expect(p.law.holds.op).toBe('and')
  const body=p.law.holds as Extract<C,{op:'and'}>, conditional=body.xs[1] as Extract<C,{op:'or'}>
  const neg=conditional.xs[0] as Extract<C,{op:'not'}>, distinct=neg.x as Extract<C,{op:'or'}>
  expect(distinct.op).toBe('or');expect(distinct.xs).toHaveLength(2)
  expect(distinct.xs.every(c=>c.op==='not'&&c.x.op==='=')).toBe(true)
  expect(p.audit?.globalTotal).toBe(false)
  // Three distinct unit cells satisfy every one-/two-cell bound at budget two,
  // while the total is three. Never advertise this projection as equivalence.
  const cells=[1,1,1], budget=2
  expect(cells.every((x,i)=>x<=budget&&cells.every((y,j)=>i===j||x+y<=budget))).toBe(true)
  expect(cells.reduce((a,b)=>a+b,0)).toBeGreaterThan(budget)
  const term={op:'var',name:'sum$OldMessage'} as E
  for(const holds of [{op:'=',a:term,b:{op:'const',value:0}},{op:'<=',a:{op:'const',value:0},b:term},{op:'<=',a:{op:'sub',a:term,b:{op:'const',value:1}},b:{op:'const',value:0}}] as C[])
    expect(()=>proposeTupleSumCells({...old,holds},{'sum$OldMessage':{sourceMap:'OldMessage',targetMap:'Message',arity:2}})).toThrow()
})

test('refuses non-cell terms, bad binding, nonzero initial cells, and input maps',()=>{
  const target=native().machine, s=source(target)
  const bad:Machine={...s,sums:{...s.sums, other:{key:'k',term:{op:'get',map:'OldLock',key:{op:'const',value:0}}}}}
  expect(restateSumSeeds(bad,target,bindings).audit.find(a=>a.source==='other')?.status).toBe('dropped')
  expect(restateSumSeeds({...s,maps:{...s.maps,OldLock:1}},target,bindings).audit[0]?.status).toBe('dropped')
  expect(restateSumSeeds(s,{...target,inputMaps:['Message']},bindings).audit[1]?.status).toBe('dropped')
  expect(restateSumSeeds(s,{...target,relations:{Message:['Node']}},bindings).audit[1]?.status).toBe('dropped')
  expect(restateSumSeeds(s,{...target,relations:undefined},bindings).audit[1]?.status).toBe('tuple-proposal')
  expect(restateSumSeeds(s,target,{...bindings,maps:{...bindings.maps,OldMessage:{...bindings.maps.OldMessage,target:'missing'}}}).audit[1]?.status).toBe('dropped')
  expect(restateSumSeeds(s,target,{...bindings,maps:{...bindings.maps,OldMessage:{...bindings.maps.OldMessage,sorts:['Node','Node','Node']}}}).audit[1]?.status).toBe('dropped')
})
