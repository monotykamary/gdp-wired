import {expect,test} from 'bun:test'
import {rule,proveRule} from './dsl.ts'
import {BudgetExpired,workAdmissionSnapshot,withWorkAdmissionTrace,type WorkAdmissionEvent} from './work-admission.ts'
import {compareWork,workAmount,workFromExact,workSub} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'

const full=completeWorkProfile.enabled?test:test.skip
full('public search.work passes the exact original grant, without a default or display round trip',()=>{
 const r=rule('exact public root').state({v:0}).step(({v})=>({v}))
 const law=r.law('zero',({v})=>v.eq(0))
 for(const grant of [workAmount(1n,3n),workAmount(9007199254740993n),workAmount(1n,1n<<1074n)]){
  const roots:WorkAdmissionEvent[]=[]
  const before=workAdmissionSnapshot()
  const result=withWorkAdmissionTrace(event=>{
   if(event.kind==='scope-enter'&&event.activeEndpoints.some(scope=>scope.kind==='root')){
    roots.push(event)
    // Stop before the production body; this test isolates public admission,
    // not proof success, and exercises observer-exception scope cleanup too.
    throw new BudgetExpired('exact public root fixture')
   }
  },()=>proveRule(r,[law],{search:{work:grant}}))
  expect(result.proven).toBe(false);expect(result.checked).toBe(false)
  expect(roots).toHaveLength(1)
  const root=roots[0]!,endpoint=root.activeEndpoints.find(scope=>scope.kind==='root')!
  expect(compareWork(workSub(workFromExact(endpoint.end),workFromExact(root.rootBaseline!.actual)),grant)).toBe(0)
  const after=workAdmissionSnapshot()
  expect(after.activeEndpoints).toHaveLength(0)
  expect(after.actual).toEqual(before.actual)
  expect(after.reserved).toEqual(before.reserved)
 }
})
