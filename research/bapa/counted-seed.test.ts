import {expect,test} from 'bun:test'
import {nat,proveRule,rule} from '../../core/dsl.ts'
import {proofOutput,type PublicProofOutput} from '../../core/proof-output.ts'
import type {Counted,E,Law,Machine} from '../../core/machine.ts'
import {proveCountedCandidateSeeds} from '../../core/counted-candidate-seeds.ts'
import {checkCountedLaws} from '../../kernel/kernel.ts'
import {restateCountSeeds} from './counted-seed-restatement.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const m:Machine={name:'symbolic counted',params:['size','values'],inputs:[],state:{left:n(0),right:n(0)},maps:{Vote:0},step:{state:{left:v('right'),right:n(0)}}}
const bindings={maps:{Vote:{target:'Vote',sorts:['Node'],radix:64}},domains:{Node:'size',Value:'values'}}
const source:Record<string,Counted>={hits:{j:'j',key:'k',below:v('size'),body:{op:'if',c:{op:'=',a:{op:'get',map:'Vote',key:v('k')},b:v('j')},then:n(1),else:n(0)}}}
const config={hits:{target:'hits',jSort:'Value',keySort:'Node'}}
test('restates fresh unary count; refuses collision and fixed packed slices',()=>{
 const a=restateCountSeeds(source,m,bindings,config)[0]!
 expect(a.status).toBe('candidate')
 expect(restateCountSeeds(source,{...m,maps:{...m.maps,hits:0}},bindings,config)[0]?.status).toBe('dropped')
 expect(restateCountSeeds({...source,hits:{...source.hits!,lo:'z',base:64}},m,bindings,config)[0]?.status).toBe('dropped')
})
test('native admission never treats false helper or false caller as given',()=>{
 const a=restateCountSeeds(source,m,bindings,config)[0]!
 if(a.status!=='candidate')throw Error(a.reason)
 const machine={...m,counts:{hits:a.definition}}
 const publicLaw:Law={name:'left zero',holds:{op:'=',a:v('left'),b:n(0)}}
 const helper:Law={name:'right zero',holds:{op:'=',a:v('right'),b:n(0)}}
 const wrong:Law={name:'wrong',holds:{op:'=',a:v('right'),b:n(1)}}
 const out=proveCountedCandidateSeeds(machine,[publicLaw],[helper,wrong],10000)
 expect(out.status).toBe('checked')
 if(out.status!=='checked')throw Error(out.reason)
 expect(out.kept).toContain(helper);expect(out.dropped).toContain(wrong)
 expect(out.closure.proof && checkCountedLaws(out.closure.m,out.closure.laws,out.closure.proof)).toBe(true)
 expect(proveCountedCandidateSeeds(machine,[wrong],[helper],10000).status).toBe('inconclusive')
})

test('public counted seed call retains the full family and unchanged source',()=>{
 const r=rule('public counted seed').params({size:nat,values:nat}).state({left:0,right:0}).maps({Vote:0}).step(({right})=>({left:right,right:0}))
 const laws=[r.law('left zero',({left})=>left.eq(0))]
 const helper:Law={name:'right zero',holds:{op:'=',a:v('right'),b:n(0)}}
 const wrong:Law={name:'wrong public seed',holds:{op:'=',a:v('right'),b:n(1)}}
 const a=restateCountSeeds(source,r.machine,bindings,config)[0]!
 if(a.status!=='candidate')throw Error(a.reason)
 const events:PublicProofOutput[]=[],audits:any[]=[],before=proofOutput.on
 try{
  proofOutput.on=e=>events.push(e)
  const out=proveRule(r as never,laws,{search:true,candidateSeeds:{kind:'counted',counts:{hits:a.definition},laws:[helper,wrong],report:x=>audits.push(x)}})
  expect(out.proven&&out.checked).toBe(true)
  expect(events).toHaveLength(1);expect(events[0]!.original.laws).toBe(laws)
  expect(Object.keys(events[0]!.original.machine.counts??{})).toEqual([])
  let node=events[0]!.proof;while(node?.kind==='derived')node=node.parents[0]
  expect(node?.kind).toBe('counted');if(node?.kind!=='counted')throw Error('missing counted closure')
  expect(node.machine.counts?.hits).toEqual(a.definition)
  expect(node.laws.map(l=>l.name)).toContain('right zero')
  expect(node.laws.map(l=>l.name)).not.toContain('wrong public seed')
  expect(checkCountedLaws(node.machine,node.laws,node.proof)).toBe(true)
  expect(audits[0]?.kind).toBe('counted')
  expect(audits[0]?.dropped.find((x:{name:string})=>x.name==='wrong public seed')?.stuck).toBeUndefined()
 }finally{proofOutput.on=before}
 expect(()=>proveRule(r as never,laws,{search:true,candidateSeeds:{kind:'counted',counts:{Vote:a.definition},laws:[]}})).toThrow('must not override')
},120000)
