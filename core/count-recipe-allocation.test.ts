import {expect,test} from 'bun:test'
import {countRecipeGraph,type CountRecipeMember} from './count-recipe-graph.ts'
import {countRecipeAllocationCohort,countRecipeMemberAllotment,CountRecipePass,runCountRecipeController} from './count-recipe-controller.ts'
import {workAmount,workSub,compareWork} from './work-amount.ts'
import {WorkLedger} from './work-admission.ts'
import {type WorkKey,workKeys} from './work-kinds.ts'
import {completeWorkProfile} from './work-profile.ts'
const a=(n:number)=>workAmount(BigInt(n)),noop=()=>{}
const graph=(wide:boolean,extra=20)=>{
 const members:CountRecipeMember[]=[{name:'target',reference:0,recipes:[{id:'known',required:['a','b'],terminal:false},{id:'alternative',...(wide?{}:{required:[]}),terminal:false}]},
  ...['a','b',...Array.from({length:extra},(_,i)=>'outside'+i)].map((name,i)=>({name,reference:i+1,recipes:[{id:'known',required:[],terminal:false}]}))]
 return {members,graph:countRecipeGraph(members,['target'],noop)}
}
test('46.18: widening changes neither a closure cohort nor its same-headroom ordinary/strategy formula',()=>{
 const narrow=graph(false),wide=graph(true)
 expect(narrow.graph.candidates.size).toBe(3);expect(wide.graph.candidates.size).toBe(23)
 for(const kind of ['ordinary','strategy'] as const){
  const p=countRecipeAllocationCohort(narrow.members.map(m=>m.name),narrow.graph,'a',noop),q=countRecipeAllocationCohort(wide.members.map(m=>m.name),wide.graph,'a',noop)
  expect(p).toBe(3);expect(q).toBe(3)
  expect(countRecipeMemberAllotment(a(120),p,kind,a(1))).toEqual(countRecipeMemberAllotment(a(120),q,kind,a(1)))
 }
})
test('46.18: an outside member adds itself, not twenty unrelated widened candidates',()=>{
 const f=graph(true),p=countRecipeAllocationCohort(f.members.map(m=>m.name),f.graph,'outside0',noop)
 expect(p).toBe(4);expect(countRecipeMemberAllotment(a(120),p,'ordinary',a(1))).toEqual(a(30))
 expect(countRecipeMemberAllotment(a(120),p,'strategy',a(1))).toEqual(a(117))
})
test('46.18: an empty eligible closure gives the selected outside member p=1 and no extra credit',()=>{
 const f=graph(true),empty={...f.graph,usable:new Set(['target','a','b'])}
 const p=countRecipeAllocationCohort(f.members.map(m=>m.name),empty,'outside0',noop)
 expect(p).toBe(1);expect(countRecipeMemberAllotment(a(120),p,'ordinary',a(1))).toEqual(a(120))
 expect(countRecipeMemberAllotment(a(0),p,'strategy',a(1))).toEqual(a(0))
})
test('46.18: terminal widening triggers do not alter Q, and an already fixed amount stays fixed',()=>{
 const f=graph(true),before=countRecipeAllocationCohort(f.members.map(m=>m.name),f.graph,'a',noop),fixed=countRecipeMemberAllotment(a(120),before,'ordinary',a(1))
 const terminal=f.members.map(m=>m.name==='target'?{...m,recipes:m.recipes.map(r=>r.id==='alternative'?{...r,terminal:true}:r)}:m)
 const after=countRecipeGraph(terminal,['target'],noop)
 expect(after.candidates.size).toBe(3);expect(countRecipeAllocationCohort(terminal.map(m=>m.name),after,'a',noop)).toBe(before)
 expect(fixed).toEqual(a(40));expect(countRecipeMemberAllotment(a(90),before,'ordinary',a(1))).toEqual(a(30))
})
const full=completeWorkProfile.enabled?test:test.skip
full('46.18: a widened member stops inside its own allotment and charged use reduces its real ancestors',()=>{
 const b=new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
 b.withBudget(a(100000),()=>{
  const pass=new CountRecipePass<string>([{name:'outside',reference:0,recipes:[{id:'ordinary',kind:'ordinary',required:[]}]},{name:'target',reference:1,recipes:[{id:'ordinary',kind:'ordinary'}]}],'fixed',b)
  let grant=0,spent=0;const events:Record<string,unknown>[]=[]
  const before=b.actual(),out=runCountRecipeController(pass,['target'],{observe:event=>{events.push(event);if(event.phase==='count-recipe-admission'&&event.law==='outside'){const x=event.allotted as {numerator:string,denominator:string};grant=Math.floor(Number(x.numerator)/Number(x.denominator));expect(event.allocationCohort).toBe(2)}},construct:name=>{if(name==='outside'){spent=Math.floor(grant/2);const usedBefore=b.actual(),leftBefore=b.available()!;b.start('ticks',spent);expect(workSub(b.actual(),usedBefore)).toEqual(a(spent));expect(workSub(leftBefore,b.available()!)).toEqual(a(spent));const beforeRefusal=b.actual();try{b.start('ticks',grant)}catch(error){expect(b.actual()).toEqual(beforeRefusal);throw error}}return undefined},close:()=>false})
  expect(out.result).toBeUndefined();expect(spent).toBeGreaterThan(0)
  expect(events.some(e=>e.phase==='count-recipe-result'&&e.law==='outside'&&e.outcome==='hard-cap')).toBe(true)
  expect(compareWork(workSub(b.actual(),before),a(spent))).toBeGreaterThanOrEqual(0)
  expect(compareWork(pass.states[0]!.used,a(spent))).toBeGreaterThanOrEqual(0)
  expect(pass.states[0]!.recipes[0]!.tickets.snapshot()).toMatchObject({started:1,terminal:true})
 })
})
