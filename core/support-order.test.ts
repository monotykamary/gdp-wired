import {test, expect} from 'bun:test'
import {type Law, type Machine, n} from './machine.ts'
import {supportOrder, supportBudget, activeSupport, searchCounted} from './counts.ts'
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

test('exhausted outer budget cannot restart in counted search',()=>{
 const m:Machine={name:'budget',params:[],inputs:[],state:{i:n(0)},step:{state:{i:n(0)}}},caller=law('original'),w=fullWork()
 const r=withWall(performance.now()+1000,()=>counted(fullRate,()=>withWork(w,()=>withDeadline(clock(),()=>searchCounted(m,[caller],60000))),true))
 expect(r.proven).toBe(false);expect(r.laws).toContain(caller)
})
