import {expect,test} from 'bun:test'
import {nat,proveRule,rule} from '../../core/dsl.ts'
import type {E,Law} from '../../core/machine.ts'
import {proofOutput,type PublicProofOutput} from '../../core/proof-output.ts'
import {checkGhostedLaws} from '../../kernel/kernel.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value}),pair=(a:E,b:E):E=>({op:'tup',a,b})
test('public proveRule retains a checked binary-key ghost witness',()=>{
 const r=rule('binary witness public').inputs({a:nat,b:nat}).state({x:0}).step(()=>({x:0}))
 const law:Law={name:'a witness at every pair',forall:'u',keys:['v'],some:['w'],holds:{op:'=',a:v('w'),b:v('x')}}
 const helper:Law={name:'x stays zero',holds:{op:'=',a:v('x'),b:n(0)}}
 const terms={w:{op:'get' as const,map:'G',key:pair(v('u'),v('v'))}},ghosts={vars:{},maps:{G:{start:0,write:{key:pair(v('a'),v('b')),value:n(0)}}}}
 const events:PublicProofOutput[]=[],audits:any[]=[],prior=proofOutput.on,before=JSON.stringify(r.machine)
 try{
  proofOutput.on=e=>events.push(e)
  const out=proveRule(r as never,[law],{search:true,candidateSeeds:{laws:[helper],witnesses:{[law.name]:{terms}},ghosts,report:a=>audits.push(a)}})
  expect(out.proven&&out.checked).toBe(true);expect(audits[0]).toMatchObject({status:'checked'})
  let node=events[0]!.proof,ctx:any
  while(node?.kind==='derived'){if((node.context as any)?.kind==='skolem')ctx=node.context;node=node.parents[0]}
  if(!ctx||node?.kind!=='usual')throw Error('binary ghost closure not retained')
  expect(checkGhostedLaws(ctx.G,ctx.family,node.proof)).toBe(true)
  expect(ctx.plains[law.name].sub.w).toEqual(terms.w)
  expect(ctx.laws[0]).toBe(law);expect(JSON.stringify(r.machine)).toBe(before)
 }finally{proofOutput.on=prior}
},120000)
