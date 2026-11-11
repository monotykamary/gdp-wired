import {expect,test} from 'bun:test'
import {type Law,type Machine,all,atMost,get,n,same,x} from './machine.ts'
import {countedAttempts,countsDump} from './counts.ts'
import {env} from './solver.ts'
import {type CountDecl,type Goal,checkMC,countedObligations} from '../kernel/kernel.ts'
import {clock,counted,fullRate,withWall} from '../kernel/prove.ts'
import {countFrameConditions,fixedCountFrameCase,ownCountLawInstance,proveCountFrameGoal} from './count-frames.ts'

const choice={name:'action',value:4,values:[0,1,4]}
const declarations:CountDecl[]=[{map:'C',j:'row',key:'k',below:n(2),body:get('Cells',x('k'))},{map:'C#',j:'row',key:'k',below:n(2),body:{op:'if',c:same(x('action'),n(4)),then:get('Cells',x('k')),else:n(0)}}]
const raw:Goal={name:'fixed frame',hyps:[{op:'<',a:get('C',n(0)),b:get('C#',n(0))},same(x('action'),n(4))]}
const request={reads:[['pre','C',n(0)],['post','C#',n(0)]] as [string,string,ReturnType<typeof n>][],insts:[]}
test('fixed-operation detection reads only mandatory equalities, not disjuncts',()=>{
 const m:Machine={name:'generic action',params:[],inputs:['action'],state:{v:n(0)},step:{state:{v:{op:'if',c:same(x('action'),n(0)),then:n(0),else:{op:'if',c:same(x('action'),n(1)),then:n(1),else:{op:'if',c:same(x('action'),n(4)),then:n(4),else:n(2)}}}}},assume:all(atMost(n(0),x('action')),same(x('action'),n(4)))}
 expect(fixedCountFrameCase(m)).toEqual(choice)
 expect(fixedCountFrameCase({...m,assume:{op:'or',xs:[same(x('action'),n(4)),same(x('action'),n(0))]}})).toBeUndefined()
 expect(fixedCountFrameCase({...m,assume:all(same(x('action'),n(4)),same(x('action'),n(0)))})).toBeUndefined()
 expect(new Set(countFrameConditions(choice).map(r=>JSON.stringify(r))).size).toBe(countFrameConditions(choice).length)
})
test('own-key seeding is tuple preserving and idempotent',()=>{
 const law:Law={name:'bound',forall:'a',keys:['b'],holds:atMost(n(0),n(0))},at={bound:[n(1),n(2)]}
 const seeded=ownCountLawInstance(law,at)
 expect(seeded.bound).toEqual([n(1),n(2),x('a#'),x('b')])
 expect(at.bound).toEqual([n(1),n(2)])
 expect(ownCountLawInstance(law,seeded)).toBe(seeded)
})
test('the opt-in attempt retains frames and still checks a false INIT',()=>{
 const before=env.GDP_COUNT_FRAMES,hook=countsDump.on
 env.GDP_COUNT_FRAMES='1'
 try{
  for(const initial of [0,1]){
   const m:Machine={name:'fixed total',params:[],inputs:['action'],state:{},maps:{Cells:initial},counts:{Total:{j:'row',key:'member',below:n(2),body:get('Cells',x('member'))}},assume:same(x('action'),n(4)),step:{maps:{Cells:{each:'cell',value:{op:'if',c:same(x('action'),n(4)),then:get('Cells',x('cell')),else:{op:'if',c:same(x('action'),n(0)),then:n(1),else:{op:'if',c:same(x('action'),n(1)),then:n(0),else:n(0)}}}}}}}
   const law:Law={name:'total stays zero',forall:'r',holds:atMost(get('Total',x('r')),n(0))},phases:string[]=[]
   countsDump.on=e=>{if('phase'in e&&typeof e.phase==='string')phases.push(e.phase)}
   const out=withWall(performance.now()+3000,()=>counted(fullRate,()=>countedAttempts(m,[law],new Set(),clock()+1000).traced(law,[law],1,1000)))
   expect('proof'in out).toBe(initial===0)
   if('proof'in out){
    expect(phases).toContain('frame-proven')
    const goals=countedObligations(m,[law],{[law.name]:out.proof.instances},0)
    for(const g of goals)expect(checkMC(g.goal.hyps,g.decls,out.proof.certs[g.goal.name]!)).toBe(true)
    expect(out.proof.certs[`${law.name} @step`]!.frames?.length).toBeGreaterThan(0)
   }
  }
 }finally{countsDump.on=hook;if(before===undefined)delete env.GDP_COUNT_FRAMES;else env.GDP_COUNT_FRAMES=before}
})

test('a non-equal count uses a checked per-key cut, never an assumed inequality',()=>{
 const ds:CountDecl[]=[declarations[0]!,{...declarations[1]!,body:{op:'if',c:same(x('action'),n(4)),then:n(0),else:get('Cells',x('k'))}}]
 const cert=withWall(performance.now()+3000,()=>counted(fullRate,()=>proveCountFrameGoal(raw,ds,request,choice,new Set(['C']),clock()+1000)))
 expect(cert).toBeDefined()
 expect(cert!.frames).toHaveLength(0)
 expect(cert!.monos).toHaveLength(1)
 expect(checkMC(raw.hyps,ds,cert!)).toBe(true)
 expect(checkMC(raw.hyps,ds,{...cert!,monos:[]})).toBe(false)
 expect(checkMC(raw.hyps,ds,{...cert!,monos:[{...cert!.monos![0]!,tree:{leaf:[]}}]})).toBe(false)
})

test('a returned frame-first tree is checked and fails without its frames',()=>{
 const cert=withWall(performance.now()+3000,()=>counted(fullRate,()=>proveCountFrameGoal(raw,declarations,request,choice,new Set(['C']),clock()+1000)))
 expect(cert).toBeDefined()
 expect(checkMC(raw.hyps,declarations,cert!)).toBe(true)
 expect(checkMC(raw.hyps,declarations,{...cert!,frames:[]})).toBe(false)
 expect(withWall(performance.now()+3000,()=>counted(fullRate,()=>proveCountFrameGoal(raw,declarations,request,choice,new Set(['Other']),clock()+1000)))).toBeUndefined()
})
