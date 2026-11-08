import {expect,test} from 'bun:test'
import {type Machine,all,get,ite,less,n,not,plus,same,x} from '../machine.ts'
import {type CountCert,type Path,canon,check,checkMC,mcGoal} from '../../kernel/kernel.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {modelSequence} from './ops.ts'
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
test('separately useful inclusions accumulate when a partial violated set remains SAT',()=>{
 const member=x('k'),bit=(c:Parameters<typeof ite>[0])=>ite(c,n(1),n(0)),a=same(get('A',member),n(1)),b=same(get('B',member),n(1)),c=same(get('C',member),n(1)),d=same(get('D',member),n(1)),base={j:'row',key:'k',below:n(4)}
 const ds=[{...base,map:'left',body:bit(a)},{...base,map:'right',body:bit(b)},{...base,map:'leftCover',body:bit({op:'or',xs:[a,c]})},{...base,map:'rightCover',body:bit({op:'or',xs:[b,d]})}]
 const reads:CountCert['reads']=ds.map((v,i)=>[`r${i}`,v.map,n(0)]),insts:CountCert['insts']=[{wit:'u',below:n(4),terms:[[1,'r0'],[-1,'r2']],unit:0},{wit:'v',below:n(4),terms:[[1,'r1'],[-1,'r3']],unit:0},{wit:'identity',below:n(4),terms:[[1,'r0'],[-1,'r0'],[1,'r1'],[-1,'r1']],unit:0}],cert={reads,insts}
 const value=(map:string)=>get(map,n(0)),claim=less(plus(value('leftCover'),value('rightCover')),plus(value('left'),value('right'))),g=mcGoal([claim],ds,cert)!,m:Machine={name:'two inclusions',params:[],inputs:[],state:{},maps:{A:0,B:0,C:0,D:0},step:{}},events:object[]=[]
 const tree=deriveCountClosure(m,ds,g,cert,new Map(),clock()+1500,events,{claim})
 expect(tree).toBeDefined();if(tree)expect(checkMC([claim],ds,{...cert,tree})).toBe(true)
 expect(events.some((e:any)=>e.stage==='closure-batch-core')).toBe(true)
})
test('an empty numeric core closes a contradictory path with a kernel-checked proof',()=>{
 const f=fixture(true),lin={outside:-1},root:Path=new Map([[canon(lin),{lin,holds:false}]])
 const query=modelSequence(root)({name:f.g.name,hyps:[]},clock()+100)
 expect('tree'in query).toBe(false)
 if('tree'in query)return
 expect(query.why).toBe(REFUTED);expect(query.core).toEqual([])
 const events:object[]=[],tree=deriveCountClosure(f.m,f.ds,f.g,f.cert,root,clock()+1500,events,{claim:f.claim})
 expect(tree).toBeDefined()
 if(tree)expect(check(f.g,tree,root)).toBe(true)
 expect(events.some((e:any)=>e.stage==='closure-final'&&e.mode==='model-driven'&&e.outcome==='checked')).toBe(true)
})

test('expired closure leaves no proof and never extends its deadline',()=>{
 const f=fixture(true)
 expect(deriveCountClosure(f.m,f.ds,f.g,f.cert,new Map(),clock()-1,[],{claim:f.claim})).toBeUndefined()
})
