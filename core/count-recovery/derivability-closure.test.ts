import {expect,test} from 'bun:test'
import {type Machine,all,get,ite,less,n,not,plus,same,x} from '../machine.ts'
import {type CountCert,checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {deriveCountClosure} from './derivability-closure.ts'
import {collectConditionalCertificate,hasConditionalProof} from './conditional-proof.ts'

function fixture(disjoint:boolean){
 const member=x('member'),a=same(get('A',member),n(1)),b=same(get('B',member),n(1)),vote=same(get('Vote',member),n(1)),bit=(c:Parameters<typeof ite>[0])=>ite(c,n(1),n(0))
 const d={j:'row',key:'member',below:n(4)},ds=[
  {...d,map:'Remaining',body:bit(all(a,...disjoint?[not(vote)]:[]))},
  {...d,map:'Voters',body:bit(all(b,vote))},
  {...d,map:'Left',body:bit(all(a,not(b)))},
  {...d,map:'Both',body:bit(all(a,b))},
  {...d,map:'Right',body:bit(all(not(a),b))},
 ]
 const reads:CountCert['reads']=ds.map((c,i)=>[`r${i}`,c.map,n(0)]),insts:CountCert['insts']=[{wit:'w',below:n(4),terms:[[1,'r0'],[1,'r1'],[-1,'r2'],[-1,'r3'],[-1,'r4']],unit:0}]
 const value=(map:string)=>get(map,n(0)),claim=less(plus(plus(value('Left'),value('Both')),value('Right')),plus(value('Remaining'),value('Voters'))),cert={reads,insts},g=mcGoal([claim],ds,cert)!
 const m:Machine={name:'disjoint source closure',params:[],inputs:[],state:{},inputMaps:['Vote'],maps:{A:0,B:0,Vote:0},step:{}}
 return {m,ds,g,cert,claim}
}
for(const disjoint of [true,false])test(`closure ${disjoint?'checks a derived union':'does not assume a false union'}`,()=>{
 const f=fixture(disjoint),events:object[]=[],tree=deriveCountClosure(f.m,f.ds,f.g,f.cert,new Map(),clock()+1500,events,{claim:f.claim})
 expect(events.every((e:any)=>e.stage!=='closure-source'||e.scope>=0)).toBe(true)
 if(disjoint&&!tree)console.error(JSON.stringify(events))
 if(disjoint){expect(tree).toBeDefined();if(tree)expect(checkMC([f.claim],f.ds,{...f.cert,tree})).toBe(true);expect(events.some((e:any)=>e.stage==='closure-final'&&e.outcome==='checked')).toBe(true)}
 else expect(tree).toBeUndefined()
})
test('internal closure keeps independent cuts in the final checked certificate',()=>{
 const f=fixture(true),tree=deriveCountClosure(f.m,f.ds,f.g,f.cert,new Map(),clock()+1500,[],{claim:f.claim,conditional:true})
 expect(tree).toBeDefined()
 if(!tree)return
 expect(hasConditionalProof(tree)).toBe(true)
 const combined=collectConditionalCertificate(f.g,tree,performance.now()+2000)
 expect(combined).toBeDefined()
 if(combined){expect(combined.lemmas.length).toBeGreaterThan(0);expect(checkMC([f.claim],f.ds,{...f.cert,...combined})).toBe(true)}
})
test('expired closure leaves no proof and never extends its deadline',()=>{
 const f=fixture(true)
 expect(deriveCountClosure(f.m,f.ds,f.g,f.cert,new Map(),clock()-1,[],{claim:f.claim})).toBeUndefined()
})
