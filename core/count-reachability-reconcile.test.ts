// Real original replay + the same reconciliation function the production
// probe uses. Queue snapshots are untrusted held/committed proposal state.
import {expect,test as profileTest} from 'bun:test'
import {stepWorkProfile} from './step-work.ts'
import {type Law,type Machine,n,plus,x} from './machine.ts'
import {small} from './exists.ts'
import {countReachabilityScreen} from './count-reachability.ts'
import {reconcileReachableRejections,withoutReachableRejections} from './count-reachability-reconcile.ts'
import {countPrerequisiteComponents} from './count-prerequisite-components.ts'
import {clock,counted,fullRate,withBudget,withWall} from '../kernel/prove.ts'
// No-witness screens require the bookkeeping clock; raw legacy OFF omits it.
const test=profileTest.skipIf(!stepWorkProfile.enabled)
const bound=(name:string,amount:number):Law=>({name,holds:{op:'<=',a:x('v'),b:n(amount)}})
const machine:Machine={name:'multi-law replay',params:[],inputs:['amount'],state:{v:n(0)},step:{state:{v:plus(x('v'),x('amount'))}}}
const run=<T>(body:()=>T)=>counted(fullRate,()=>withBudget(4_000_000,()=>withWall(clock()+4_000_000/fullRate,body)),true)
function multi(){
 const a=bound('A',0),b=bound('B',1),funding=new Map<string,{grant:number,used:number}>()
 const screen=countReachabilityScreen(machine,machine,[],100000,undefined,funding)
 const old=screen.screen(a,0,0,clock())
 expect(old.outcome).toBe('exhausted')
 const originalGrant={...funding.get(a.name)!}
 const later=screen.screen(b,1000,0,clock()+10000,{v:0,amount:2})
 expect(later.outcome).toBe('rejected');expect(screen.rejectedNames()).toEqual(['A','B'])
 return {a,b,screen,old,funding,originalGrant}
}
test('an earlier exhausted receipt reflects later incidental rejection without a new grant',()=>run(()=>{
 const {a,screen,old,funding,originalGrant}=multi()
 expect(old.outcome).toBe('rejected')
 const before=clock(),again=screen.screen({holds:a.holds,name:a.name},1e8,1e8,clock()+10000)
 expect(again).toBe(old);expect(again.outcome).toBe('rejected');expect(clock()).toBe(before)
 expect(funding.get(a.name)).toEqual(originalGrant)
 expect(screen.receipts([a])[0]).toMatchObject({outcome:'rejected',used:0,cumulativeUsed:0})
}))
test('same-view fallback removes original candidates even though evidence laws are clones',()=>run(()=>{
 const {a,b,screen}=multi(),kept=bound('kept',10),original=[a,b,kept]
 const evidence=screen.evidence()
 expect(evidence.map(e=>e.law.name)).toEqual(['A','B'])
 expect(evidence[0]!.law).not.toBe(a);expect(evidence[1]!.law).not.toBe(b)
 expect(withoutReachableRejections(original,screen.rejectedNames())).toEqual([kept])
 expect(withoutReachableRejections(original,screen.rejectedNames())[0]).toBe(kept)
}))
for(const committed of [false,true])test('the complete delta invalidates '+(committed?'committed':'held')+' users and rebuilds them',()=>run(()=>{
 const {a,b,screen}=multi(),user='U',names=[a.name,user,b.name]
 const scopes=new Map([[a.name,{premises:[]}],[user,{premises:[a.name]}]])
 const admitted=new Set(committed?[a.name,user]:[])
 const q=countPrerequisiteComponents(names,new Map(),[],[...admitted],{proofGuided:true,held:new Map([[a.name,[]],[user,[a.name]]])})
 const decision=q.next()
 const active=decision?.kind==='attempt'?decision.name:undefined
 const delta=reconcileReachableRejections(q,new Set(names),screen.rejectedNames(),scopes,admitted,active)
 expect(delta.rejected).toEqual(['A','B']);expect(delta.invalidated).toEqual(['U'])
 expect(q.failed()).toEqual(['A','B']);expect(q.failed()).not.toContain(user)
 expect(scopes.size).toBe(0);expect(admitted.size).toBe(0);expect(q.available()).toEqual([])
 expect(q.next()).toMatchObject({kind:'attempt',name:user,context:[user]})
 q.finish(user,[]);q.commit([user]);expect(q.available()).toEqual([user])
 expect(reconcileReachableRejections(q,new Set(names),screen.rejectedNames(),scopes,admitted).rejected).toEqual([])
}))
test('a different target need not be rejected for its replay to invalidate A',()=>run(()=>{
 const source:Machine={name:'incidental only',params:[],inputs:[],state:{v:n(0),w:n(0)},step:{state:{v:n(1),w:n(0)}}}
 const states=small(source,{},1,2,2),hint=states[1]!
 // Tamper only the hint. Original replay reconstructs w=0 and thus refuses B
 // as a rejection, while the very same original path really refutes A.
 hint.scalars.w=1
 const a=bound('A',0),b:Law={name:'B',holds:{op:'<=',a:x('w'),b:n(0)}}
 const screen=countReachabilityScreen(source,source,[],100000,()=>[{p:{},sts:[hint]}])
 const previous=screen.screen(a,0,0,clock())
 const target=screen.screen(b,1000,0,clock()+10000)
 expect(target.outcome).not.toBe('rejected');expect(previous.outcome).toBe('rejected');expect(screen.rejectedNames()).toEqual(['A'])
 const q=countPrerequisiteComponents(['A','B','U'],new Map([['U',['A','B']]]),['U'],[],{proofGuided:true,discoveryFirst:true,discovered:['A','B'],targets:['U']})
 expect(q.next()).toMatchObject({name:'U'})
 const delta=reconcileReachableRejections(q,new Set(['A','B','U']),screen.rejectedNames(),new Map(),new Set(),'U')
 expect(delta.rejected).toEqual(['A']);expect(delta.interrupted).toBe(true)
 expect(q.failed()).toEqual(['A']);expect(q.unknown().some(row=>row.name==='U')).toBe(true)
 // The unaffected, unrun B may precede U's retry; neither may retain A.
 expect(q.next()).toMatchObject({context:['B','U']})
}))
test('all rejected premises are removed before retrying a current promotion',()=>run(()=>{
 const {screen}=multi(),names=['A','B','owner']
 const q=countPrerequisiteComponents(names,new Map([['owner',['A','B']]]),['owner'],[],{proofGuided:true,discoveryFirst:true,discovered:['A','B'],targets:['owner']})
 expect(q.next()).toMatchObject({name:'owner',context:names})
 const delta=reconcileReachableRejections(q,new Set(names),screen.rejectedNames(),new Map(),new Set(),'owner')
 expect(delta.rejected).toEqual(['A','B']);expect(delta.interrupted).toBe(true)
 expect(q.next()).toMatchObject({name:'owner',context:['owner']})
 q.finish('owner',[]);q.commit(['owner']);expect(q.available()).toEqual(['owner'])
}))
