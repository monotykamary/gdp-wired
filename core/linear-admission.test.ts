import {expect,test} from 'bun:test'
import {add,scale,sub,type Lin} from './solver.ts'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired,admittedWork,workLedger,withAdmittedChunk,withWorkAdmissionTrace} from './work-admission.ts'
import {compareWork,workAdd,workMultiply,workShare,workSub,workAmount} from './work-amount.ts'
import {admittedLinearAdd,admittedLinearCopy,admittedLinearScale,admittedLinearSub} from './linear-admission.ts'

const cell=workLedger.weights.tableCells
const units=(n:bigint)=>workMultiply(cell,workAmount(n))
function attempt(a:Lin,b:Lin,grant:ReturnType<typeof units>){
 const before=admittedWork();let out:Lin|undefined,error:unknown
 try{out=workLedger.withBudget(grant,()=>admittedLinearSub(a,b,'test-sub'))}catch(e){error=e}
 return {out,error,spent:workSub(admittedWork(),before)}
}
test('funded linear operations preserve coefficient values and key order',()=>{
 for(const a of [{x:2,y:0},{x:1,y:-1},Object.assign(Object.create(null),{'1':4}) as Lin] as Lin[])for(const b of [{x:2,z:3},{y:-1},{'1':-4}] as Lin[]){
  for(const [actual,expected]of[[admittedLinearSub(a,b,'sub'),sub(a,b)],[admittedLinearAdd(a,b,'add'),add(a,b)],[admittedLinearScale(a,-2,'scale'),scale(a,-2)]]){
   expect(Object.entries(actual!)).toEqual(Object.entries(expected!))
  }
 }
})
test.skipIf(!completeWorkProfile.enabled)('discovery charges zero and cancelled cells, distinct from emission',()=>{
 const out=attempt({x:1,y:0},{x:1,z:2},units(8n))
 expect(out.error).toBeUndefined();expect(out.out).toEqual({z:-2});expect(compareWork(out.spent,units(8n))).toBe(0)
 const cancelled=attempt({x:1},{x:1},units(3n))
 expect(cancelled.out).toEqual({});expect(compareWork(cancelled.spent,units(3n))).toBe(0)
 const before=admittedWork();expect(admittedLinearCopy({x:0},'zero-copy')).toEqual({x:0})
 expect(compareWork(workSub(admittedWork(),before),units(2n))).toBe(0)
})
test.skipIf(!completeWorkProfile.enabled)('zero fractional and short grants never emit a partial row',()=>{
 for(const grant of [units(0n),workShare(cell,1n,2n),units(6n),workShare(cell,15n,2n)]){
  const out=attempt({x:1,y:0},{x:1,z:2},grant)
  expect(out.error).toBeInstanceOf(BudgetExpired);expect(out.out).toBeUndefined();expect(compareWork(out.spent,grant)).toBeLessThanOrEqual(0)
  expect(workLedger.reserved().num).toBe(0n)
 }
 // One emission unit short of a two-cell row: all discovery stays charged.
 const short=attempt({x:2,y:3},{},units(5n))
 expect(short.error).toBeInstanceOf(BudgetExpired);expect(compareWork(short.spent,units(4n))).toBe(0)
})
test.skipIf(!completeWorkProfile.enabled)('owned output is not an alias and accessors cannot execute',()=>{
 const input={x:4,y:0},out=admittedLinearCopy(input,'copy');input.x=99
 expect(out.x).toBe(4);expect(Object.hasOwn(out,'y')).toBe(true)
 let reads=0;const getter=Object.defineProperty({},'x',{enumerable:true,get(){reads++;return 1}}) as Lin
 expect(()=>admittedLinearCopy(getter,'getter')).toThrow(TypeError);expect(reads).toBe(0)
})
test.skipIf(!completeWorkProfile.enabled)('discovery and emission observer failures retain F and retire R',()=>{
 for(const phase of ['input','select','emit']){
  const before=admittedWork()
  expect(()=>workLedger.withBudget(units(100n),()=>withWorkAdmissionTrace(e=>{
   if(e.kind==='start'&&e.site===`failure:${phase}`)throw new Error('probe failure')
  },()=>admittedLinearSub({x:2},{x:1},'failure')))).toThrow('probe failure')
  expect(compareWork(admittedWork(),before)).toBeGreaterThan(0);expect(workLedger.reserved().num).toBe(0n)
 }
})
test.skipIf(!completeWorkProfile.enabled)('discovery invalidates foreign unused credit without revival',()=>{
 workLedger.withBudget(workAdd(units(20n),workLedger.weights.ticks),()=>withAdmittedChunk('ticks',1,old=>{
  expect(admittedLinearSub({x:2},{x:1},'nested')).toEqual({x:1})
  expect(()=>old.start()).toThrow(BudgetExpired)
 }))
 expect(workLedger.reserved().num).toBe(0n)
})
