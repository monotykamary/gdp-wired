import {expect,test} from 'bun:test'
import {coreMeter,observeTableCells,observeLinearRows,observeConstraintRows} from './meter.ts'
import {rawWork,workKeys} from './work-meter.ts'
import {Reader,type Trail} from '../kernel/reader.ts'
import {BudgetExpired,withBudget} from './wall.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {withTableAdmission} from './table-admission.ts'
import {tableAdmissionHook} from './table-admission-hook.ts'
import {admittedWork,startWork,withAdmittedChunk,withWorkAdmissionTrace,workLedger} from './work-admission.ts'
import {compareWork,workAdd,workSub,workMultiply,workAmount,workShare} from './work-amount.ts'
const full=completeWorkProfile.enabled?test:test.skip
const cell=workLedger.weights.tableCells,units=(n:bigint)=>workMultiply(cell,workAmount(n))
const trail:Trail={get:()=>undefined,stamp:()=>0,size:()=>0,lin:()=>{throw Error('empty trail')}}
test('unscoped and ample scoped tables keep all raw observations',()=>{
 const run=()=>{observeTableCells(7);observeLinearRows([{x:1,y:2},{}]);observeConstraintRows([{lin:{z:1}}],0)}
 const before=rawWork();run();const plain=rawWork();withBudget(100000,()=>withTableAdmission(run));const scoped=rawWork()
 for(const key of workKeys)expect(scoped[key]-plain[key],key).toBe(plain[key]-before[key])
 expect(scoped.tableCells-plain.tableCells).toBe(completeWorkProfile.enabled?10:0)
 expect(tableAdmissionHook.admit).toBeUndefined()
})
full('ample scoped reader decisions preserve results and all 26 raw buckets',()=>{
 const run=()=>{const r=new Reader({name:'paired reader',hyps:[]},trail),lin={row_key:1,other_key:-1};return[r.dec(lin),r.dec(lin),r.dec({third_key:1,'1':-2})]}
 run() // warm shared immutable key caches equally for both measurements
 const before=rawWork(),plain=run(),middle=rawWork(),scoped=withBudget(100000,()=>withTableAdmission(run)),after=rawWork()
 expect(scoped).toEqual(plain)
 for(const key of workKeys)expect(after[key]-middle[key],key).toBe(middle[key]-before[key])
})
full('1024 visits use exact starts and no retired numeric side-credit hook',()=>{
 const prior=runtimeWall.admit;let calls=0,starts=0
 runtimeWall.admit=(amount,phase)=>{calls++;prior?.(amount,phase)}
 const before=admittedWork(),counter=workLedger.counter('tableCells')
 try{withBudget(units(1024n),()=>withWorkAdmissionTrace(e=>{if(e.kind==='start'&&e.sink==='tableCells')starts++},()=>withTableAdmission(()=>{for(let i=0;i<1024;i++)observeTableCells()})))}finally{runtimeWall.admit=prior}
 expect(calls).toBe(0);expect(starts).toBe(1024)
 expect(workLedger.counter('tableCells')-counter).toBe(1024n)
 expect(compareWork(workSub(admittedWork(),before),units(1024n))).toBe(0)
})
full('zero fractional and oversized atomic requests never start an unaffordable unit',()=>{
 for(const count of [0n,2n,9n]){
  const before=admittedWork(),counter=workLedger.counter('tableCells')
  expect(()=>withBudget(units(count),()=>withTableAdmission(()=>{if(count===9n)observeTableCells(10);else for(let i=0;i<3;i++)observeTableCells()}))).toThrow(BudgetExpired)
  expect(compareWork(workSub(admittedWork(),before),units(count))).toBeLessThanOrEqual(0)
  expect(workLedger.counter('tableCells')-counter).toBe(count===2n?2n:0n)
 }
 const before=admittedWork()
 expect(()=>withBudget(workShare(cell,1n,2n),()=>observeTableCells())).toThrow(BudgetExpired)
 expect(compareWork(admittedWork(),before)).toBe(0)
})
full('every foreign raw bucket invalidates unused table permission',()=>{
 for(const key of workKeys.filter(key=>key!=='tableCells')){
  const before=admittedWork(),grant=workAdd(units(2n),workLedger.weights[key])
  withBudget(grant,()=>withAdmittedChunk('tableCells',2,lease=>{
   lease.start();startWork(key,1,'foreign table control')
   expect(()=>lease.start()).toThrow(BudgetExpired)
  }))
  expect(compareWork(workSub(admittedWork(),before),workAdd(cell,workLedger.weights[key])),key).toBe(0)
  expect(workLedger.reserved().num).toBe(0n)
 }
})
full('direct table writes are refused before mutation and smaller scopes retain no credit',()=>{
 const before=workLedger.counter('tableCells')
 expect(()=>withBudget(1000,()=>withTableAdmission(()=>{observeTableCells();coreMeter.tableCells+=999;observeTableCells()}))).toThrow('unadmitted work counter mutation')
 expect(workLedger.counter('tableCells')-before).toBe(1n)
 const next=workLedger.counter('tableCells')
 withBudget(1000,()=>withTableAdmission(()=>{
  observeTableCells();expect(()=>withBudget(0,()=>observeTableCells())).toThrow(BudgetExpired);observeTableCells()
 }))
 expect(workLedger.counter('tableCells')-next).toBe(2n)
})
full('refusal and exceptional nested scopes retire credit without poisoning legal remaining work',()=>{
 const hook=tableAdmissionHook.admit,admit=runtimeWall.admit
 withBudget(1000,()=>withTableAdmission(()=>{
  observeTableCells();expect(()=>withTableAdmission(()=>{observeTableCells();throw Error('unwind')})).toThrow('unwind');observeTableCells()
  expect(()=>runtimeWall.admit!(1001,'refusal')).toThrow(BudgetExpired)
  const before=workLedger.counter('tableCells');observeTableCells();expect(workLedger.counter('tableCells')-before).toBe(1n)
 }))
 expect(tableAdmissionHook.admit).toBe(hook);expect(runtimeWall.admit).toBe(admit)
 expect(workLedger.reserved().num).toBe(0n)
 expect(()=>withBudget(0,()=>withTableAdmission(()=>observeTableCells()))).toThrow(BudgetExpired)
})
full('the reader canonicalizer stops before exceeding an exact tight allowance',()=>{
 for(const W of [0,1,5,17,31]){
  const r=new Reader({name:'canonical bound',hyps:[]},trail),before=admittedWork(),grant=workAmount(BigInt(W))
  expect(()=>withBudget(grant,()=>withTableAdmission(()=>r.dec({long_variable_name:1,other_variable:-1})))).toThrow(BudgetExpired)
  expect(compareWork(workSub(admittedWork(),before),grant)).toBeLessThanOrEqual(0)
 }
})
