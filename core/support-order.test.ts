import {test, expect} from 'bun:test'
import {type Law, type Machine, n, x, get} from './machine.ts'
import {attemptShare, supportOrder, supportBudget, activeSupport, countSupportContext, searchCounted} from './counts.ts'
import {fullRate, fullWork, withWork, withDeadline, withWall, counted, clock} from '../kernel/prove.ts'
const law=(name:string):Law=>({name,holds:{op:'=',a:n(0),b:n(0)}})
test('support ordering preserves no-support model traversal and original helper order',()=>{
 const caller=law('caller'), noise=law('noise'), support=law('support'), stale=law('stale'), set=[caller,noise,support]
 expect(supportOrder(set,[caller],new Set(),true)).toBe(set)
 expect(supportOrder(set,[caller],new Set([stale]),true)).toBe(set)
 expect(supportOrder(set,[caller],new Set())).toEqual([noise,support,caller])
 expect(supportOrder(set,[caller],new Set([stale]))).toEqual([noise,support,caller])
 expect(supportOrder(set,[caller],new Set([support]),true)).toEqual([support,caller,noise])
 expect(set).toEqual([caller,noise,support])
})
test('per-attempt shares redistribute cheap proofs without reviving tried or carried laws',()=>{
 const pending=new Set(['cheap-a','cheap-b','costly','caller'])
 expect(attemptShare(100,pending)).toBe(25)
 pending.delete('cheap-a')
 expect(attemptShare(96,pending)).toBe(32)
 pending.delete('cheap-b')
 expect(attemptShare(90,pending)).toBe(45)
 pending.delete('costly')
 expect(attemptShare(45,pending)).toBe(45)
 pending.delete('caller')
 expect(attemptShare(0,pending)).toBe(0)
 expect(attemptShare(-1,pending)).toBe(0)
 // Pre-existing kept/carried proofs are absent from the round's pending set.
 expect(attemptShare(90,new Set(['untried']))).toBe(90)
})
test('equal per-attempt spending conserves the total remaining allowance',()=>{
 for(let count=1;count<=40;count++){
  const pending=new Set(Array.from({length:count},(_,i)=>String(i)))
  let remaining=60000,spent=0
  for(const name of [...pending]){
   const allotted=attemptShare(remaining,pending)
   expect(allotted).toBeGreaterThanOrEqual(0);expect(allotted).toBeLessThanOrEqual(remaining)
   const used=allotted/2
   remaining-=used;spent+=used;pending.delete(name)
   expect(Math.abs(remaining+spent-60000)).toBeLessThan(1e-8)
  }
 }
})

test('structural and priority slices never create a budget',()=>{
 for(const remaining of [-1,0,1,845,4999,5000,5001,60000])expect(supportBudget(remaining,845,false,true)).toBe(Math.max(0,Math.min(5000,remaining)))
 expect(supportBudget(90,5,true)).toBe(30);expect(supportBudget(90,5,false)).toBe(5)
 expect(supportBudget(-1,10,true)).toBe(0);expect(supportBudget(9,8,true)).toBe(8)
})
test('stale support cannot grant priority time to unresolved callers',()=>{
 const a=law('caller-a'),b=law('caller-b'),noise=law('helper'),stale=law('dropped'),set=[a,noise,b]
 const support=new Set([stale])
 expect(activeSupport(set,support)).toBe(false)
 expect(supportBudget(60,10,activeSupport(set,support)&&[a,b].includes(a))).toBe(10)
 expect(supportOrder(set,[a,b],support)).toEqual([noise,a,b])
 const active=new Set([noise]);expect(activeSupport(set,active)).toBe(true)
 expect(supportBudget(60,10,activeSupport(set,active)&&[a,b].includes(a))).toBe(20)
})

test('count scheduling requires count or global-state context, not a primitive implication',()=>{
 for(const prefix of ['first_','renamed_']){
  const map=prefix+'cells',count=prefix+'number',caller=law(prefix+'caller'),noise=law(prefix+'noise'),primitive:Law={name:prefix+'primitive',forall:'k',holds:{op:'=',a:get(map,x('k')),b:n(0)}},source:Law={name:prefix+'source',forall:'k',holds:{op:'<=',a:get(count,x('k')),b:n(3)}}
  const m:Machine={name:prefix,params:[],inputs:[],state:{mode:n(0)},maps:{[map]:0},counts:{[count]:{j:'k',key:'q',below:n(3),body:get(map,x('q'))}},step:{}}
  const plain=[caller,noise,primitive],support=new Set([primitive]),a=countSupportContext(m,[caller],plain,support)
  expect(a.laws).toEqual([caller,noise]);expect(a.support.size).toBe(0);expect(plain).toContain(primitive);expect(support.has(primitive)).toBe(true)
  const full=[...plain,source],mixed=new Set([primitive,source]),b=countSupportContext(m,[caller],full,mixed)
  expect(b.laws).toBe(full);expect(b.support).toBe(mixed)
  expect(countSupportContext(m,[primitive],plain,support).laws).toContain(primitive)
  expect(countSupportContext(m,[caller],plain,new Set([primitive,source])).support.size).toBe(0)
  expect(countSupportContext(m,[caller],plain,new Set()).laws).toBe(plain)
  const global:Law={name:prefix+'global context',holds:{op:'=',a:x('mode'),b:n(0)}},withGlobal=[...plain,global],globalSupport=new Set([primitive,global])
  expect(countSupportContext(m,[caller],withGlobal,globalSupport).laws).toBe(withGlobal)
  expect(countSupportContext(m,[caller],withGlobal,globalSupport).support).toBe(globalSupport)
  expect(countSupportContext(m,[caller],[...plain,noise],new Set([primitive,noise])).support.size).toBe(0)
 }
})

test('exhausted outer budget cannot restart in counted search',()=>{
 const m:Machine={name:'budget',params:[],inputs:[],state:{i:n(0)},step:{state:{i:n(0)}}},caller=law('original'),w=fullWork()
 const r=withWall(performance.now()+1000,()=>counted(fullRate,()=>withWork(w,()=>withDeadline(clock(),()=>searchCounted(m,[caller],60000))),true))
 expect(r.proven).toBe(false);expect(r.laws).toContain(caller)
})
