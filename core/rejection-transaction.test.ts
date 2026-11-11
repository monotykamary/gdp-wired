import {expect,test} from 'bun:test'
import {type Law,type Machine,n,plus,same,x} from './machine.ts'
import {createRejectionStage,rejectionFamily} from './rejection-stage.ts'
import {BudgetExpired,checkBudget,checkWorkAdmission,counted,fullRate,remainingWork,withBudget,withWork,fullWork} from '../kernel/prove.ts'
import {costs} from './solver.ts'
const H:Law={name:'H',holds:same(x('a'),n(0))},G:Law={name:'G',holds:same(x('b'),n(0))}
const source:Machine={name:'transaction',params:[],inputs:[],state:{a:n(0),b:n(0)},step:{state:{a:x('b')}}}
const pre={scalars:{a:0,b:1},maps:{}}
const increment:Machine={...source,step:{state:{a:plus(x('a'),n(1))}}}
function metered(body:()=>void):void{
 const before=costs.fm
 try{counted(fullRate,body,true)}finally{costs.fm=before}
}
test('local primitive precharge refusal is handled below the charged limit and is sticky',()=>metered(()=>{
 const stage=createRejectionStage(source,source,[],[H],100)
 expect(stage.within(()=>checkWorkAdmission(1e9,'local precharge'))).toBeUndefined()
 expect(stage.work().used).toBeLessThan(100)
 let called=false;stage.within(()=>{called=true});expect(called).toBe(false)
 expect(stage.relative({},pre,{}).status).toBe('ignored')
}))
test('root primitive refusal is never swallowed, including an exhausted local stage',()=>metered(()=>{
 const stage=createRejectionStage(source,source,[],[H],1000)
 expect(()=>withBudget(100,()=>stage.within(()=>checkWorkAdmission(101,'root precharge')))).toThrow(BudgetExpired)
 expect(()=>withBudget(0,()=>{
  try{checkWorkAdmission(1,'root refusal')}catch{}
  return createRejectionStage(source,source,[],[],0).within(()=>true)
 })).toThrow(BudgetExpired)
}))
test('a tighter inherited work cap is not mistaken for the local allowance',()=>metered(()=>{
 const stage=createRejectionStage(source,source,[],[H],1000)
 expect(()=>withWork(fullWork()+100,()=>stage.within(()=>checkWorkAdmission(101,'inherited cap')))).toThrow(BudgetExpired)
 expect(()=>withWork(fullWork()+100,()=>stage.within(()=>{costs.fm+=1e9}))).toThrow(BudgetExpired)
}))
test('an inherited work cap exactly tied with the local cap remains outer cancellation',()=>metered(()=>{
 const stage=createRejectionStage(source,source,[],[H],1)
 expect(()=>withWork(fullWork()+fullRate,()=>stage.within(()=>checkWorkAdmission(fullRate+1,'tied inherited cap')))).toThrow(BudgetExpired)
}))
test('relative and reachable publications roll back on enclosing local expiry',()=>metered(()=>{
 for(const kind of ['relative','reachable'] as const){
  const m=kind==='relative'?source:increment,stage=createRejectionStage(m,m,[],[H],10000)
  const out=stage.within(()=>{
   const attempt=kind==='relative'?stage.relative({},pre,{}):stage.reachable({},[{}])
   expect(attempt.rejected).toEqual([H])
   costs.fm+=1e9
   return attempt
  })
  expect(out).toBeUndefined();expect(stage.active()).toEqual([H]);expect(stage.evidence()).toEqual([])
 }
}))
test('safety status is committed only after the enclosing budget succeeds',()=>metered(()=>{
 for(const kind of ['relative','reachable'] as const){
  const m=kind==='relative'?source:increment,stage=createRejectionStage(m,m,[H],[H],10000)
  expect(stage.within(()=>{
   expect((kind==='relative'?stage.relative({},pre,{}):stage.reachable({},[{}])).status).toBe(kind==='relative'?'weak':'broken')
   checkWorkAdmission(1e12,'after safety validation')
  })).toBeUndefined()
  expect(stage.safety()).toBeUndefined();expect(stage.active()).toEqual([H]);expect(stage.evidence()).toEqual([])
 }
}))
test('expiry after preparing one rejection returns an untouched ignored outcome',()=>metered(()=>{
 const late:Law={name:'late',get holds(){costs.fm+=1e9;return same(x('b'),n(1))}}
 const stage=createRejectionStage(increment,increment,[],[H,late],10000)
 expect(stage.reachable({},[{}])).toEqual({status:'ignored',rejected:[],safety:[]})
 expect(stage.active()).toEqual([H,late]);expect(stage.evidence()).toEqual([])
}))
test('expansion after local expiry conservatively restores all relative witnesses and cascades',()=>metered(()=>{
 const X:Law={name:'X',holds:same(x('z'),n(0))},m:Machine={...source,state:{...source.state,z:n(0)},step:{state:{a:x('b'),z:x('a')}}}
 const stage=createRejectionStage(m,m,[],[H,X],10000)
 expect(stage.relative({}, {scalars:{a:0,b:1,z:0},maps:{}},{}).rejected).toEqual([H])
 expect(stage.relative({}, {scalars:{a:1,b:0,z:0},maps:{}},{}).rejected).toEqual([X])
 stage.within(()=>checkWorkAdmission(1e12,'exhaust local'))
 expect(new Set(stage.addCandidates([G]))).toEqual(new Set([H,X]))
 expect(stage.evidence()).toEqual([])
 expect(rejectionFamily(stage,[G])).toEqual([H,X,G]);expect(rejectionFamily(stage,[G])).toEqual([H,X,G])
}))
test('expiry during expansion validation restores remaining relative witnesses',()=>metered(()=>{
 const X:Law={name:'X',holds:same(x('z'),n(0))},m:Machine={...source,state:{...source.state,z:n(0)},step:{state:{a:x('b'),z:x('a')}}}
 const stage=createRejectionStage(m,m,[],[H,X],10000)
 stage.relative({}, {scalars:{a:0,b:1,z:0},maps:{}},{})
 stage.relative({}, {scalars:{a:1,b:0,z:0},maps:{}},{})
 const late:Law={name:'late G',get holds(){costs.fm+=1e9;return G.holds}}
 expect(new Set(stage.addCandidates([late]))).toEqual(new Set([H,X]))
 expect(stage.evidence()).toEqual([])
 expect(rejectionFamily(stage,[late])).toEqual([H,X,late])
 expect(rejectionFamily(stage,[late])).toEqual([H,X,late])
}))
test('restoration survives an enclosing failed transaction rather than restoring stale evidence',()=>metered(()=>{
 const stage=createRejectionStage(source,source,[],[H],10000)
 stage.relative({},pre,{})
 expect(stage.within(()=>{
  expect(stage.addCandidates([G])).toEqual([H])
  checkWorkAdmission(1e12,'after restoration')
 })).toBeUndefined()
 expect(stage.evidence()).toEqual([]);expect(rejectionFamily(stage,[G])).toEqual([H,G])
}))
test('outer cancellation during expansion restores before propagating',()=>metered(()=>{
 const stage=createRejectionStage(source,source,[],[H],10000)
 stage.relative({},pre,{})
 expect(()=>withBudget(0,()=>{
  try{checkWorkAdmission(1,'cancel parent')}catch{}
  stage.addCandidates([G])
 })).toThrow(BudgetExpired)
 expect(stage.evidence()).toEqual([]);expect(rejectionFamily(stage,[G])).toEqual([H,G])
}))
test('caller identity remains protected even when duplicated in candidates',()=>{
 const stage=createRejectionStage(increment,increment,[H],[H,G],10000)
 expect(stage.reachable({},[{}]).status).toBe('broken')
 expect(stage.active()).toEqual([H,G]);expect(stage.evidence()).toEqual([])
})
test('committed evidence is a detached snapshot, including law and map payloads',()=>{
 const stage=createRejectionStage(source,source,[],[H],10000),input={scalars:{a:0,b:1},maps:{extra:new Map([[7,9]])}},request={unused:new Map([[1,2]])}
 stage.relative({},input,request)
 input.maps.extra.set(7,0);request.unused.set(1,0)
 const first=stage.evidence()[0]!
 expect(first.kind).toBe('relative')
 if(first.kind!=='relative')throw new Error('expected relative')
 expect(first.pre.maps.extra!.get(7)).toBe(9);expect((first.request.unused as Map<number,number>).get(1)).toBe(2)
 first.pre.maps.extra!.set(7,100);first.law.holds=same(n(0),n(1));first.post.scalars.a=0
 const second=stage.evidence()[0]!
 if(second.kind!=='relative')throw new Error('expected relative')
 expect(second.pre.maps.extra!.get(7)).toBe(9);expect(second.post.scalars.a).toBe(1);expect(second.law.holds).toEqual(H.holds)
})
test('an arbitrary BudgetExpired is not treated as proven local exhaustion',()=>metered(()=>{
 const stage=createRejectionStage(source,source,[],[],100)
 expect(()=>stage.within(()=>{throw new BudgetExpired('unrelated')})).toThrow(BudgetExpired)
 expect(stage.within(()=>{checkBudget('still live');return remainingWork()>0})).toBe(true)
}))
