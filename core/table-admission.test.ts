import {expect,test} from 'bun:test'
import {costs} from './solver.ts'
import {coreMeter,observeTableCells,observeLinearRows,observeConstraintRows} from './meter.ts'
import {rawWork,workKeys,legacyWeights} from './work-meter.ts'
import {eprMeter} from '../kernel/epr.ts'
import {Reader,type Trail} from '../kernel/reader.ts'
import {BudgetExpired,withBudget} from './wall.ts'
import {fullWork} from '../kernel/prove.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {withTableAdmission} from './table-admission.ts'
import {tableAdmissionHook} from './table-admission-hook.ts'
const full=completeWorkProfile.enabled?test:test.skip
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
 const before=rawWork(),plain=run(),middle=rawWork(),scoped=withBudget(100000,()=>withTableAdmission(run)),after=rawWork()
 expect(scoped).toEqual(plain)
 for(const key of workKeys)expect(after[key]-middle[key],key).toBe(middle[key]-before[key])
})
full('table admission batches 1024 visits without adding raw units',()=>{
 const prior=runtimeWall.admit;let calls=0
 runtimeWall.admit=(units,phase)=>{calls++;prior?.(units,phase)}
 const start=fullWork(),before=rawWork()
 try{withBudget(100000,()=>withTableAdmission(()=>{for(let i=0;i<1024;i++)observeTableCells()}))}finally{runtimeWall.admit=prior}
 expect(calls).toBeLessThan(20);expect(calls).toBeGreaterThan(0)
 expect(rawWork().tableCells-before.tableCells).toBe(1024)
 expect(fullWork()-start).toBeCloseTo(1024*completeWorkProfile.weights.tableCells,5)
})
full('zero, near-endpoint and oversized table batches never charge an unaffordable visit',()=>{
 const weight=completeWorkProfile.weights.tableCells
 for(const allowance of [0,2*weight,9*weight]){
  const before=coreMeter.tableCells,start=fullWork()
  expect(()=>withBudget(allowance,()=>withTableAdmission(()=>{if(allowance===9*weight)observeTableCells(10);else for(let i=0;i<3;i++)observeTableCells()}))).toThrow(BudgetExpired)
  expect(fullWork()-start).toBeLessThanOrEqual(allowance+0.00001)
  expect(coreMeter.tableCells-before).toBe(allowance===2*weight?2:0)
 }
})
full('every other raw bucket invalidates cached permission',()=>{
 const weights=Object.fromEntries([...legacyWeights,...Object.entries(completeWorkProfile.weights)])
 for(const key of workKeys.filter(key=>key!=='tableCells')){
  const scale=Math.ceil(512/weights[key]!),start=fullWork(),before=coreMeter.tableCells,W=completeWorkProfile.weights.tableCells+weights[key]!*scale+0.25
  expect(()=>withBudget(W,()=>withTableAdmission(()=>{
   observeTableCells()
   if(key==='epr')eprMeter.n+=scale
   else if(key in coreMeter)(coreMeter as Record<string,number>)[key]!+=scale
   else (costs as Record<string,number>)[key]!+=scale
   observeTableCells()
  }))).toThrow(BudgetExpired)
  expect(coreMeter.tableCells-before,key).toBe(1);expect(fullWork()-start,key).toBeLessThanOrEqual(W)
 }
})
full('direct table writes and a smaller nested budget cannot reuse cached permission',()=>{
 let before=coreMeter.tableCells
 expect(()=>withBudget(1000,()=>withTableAdmission(()=>{observeTableCells();coreMeter.tableCells+=999;observeTableCells()}))).toThrow(BudgetExpired)
 expect(coreMeter.tableCells-before).toBe(1000)
 before=coreMeter.tableCells
 withBudget(1000,()=>withTableAdmission(()=>{
  observeTableCells();expect(()=>withBudget(0,()=>observeTableCells())).toThrow(BudgetExpired);observeTableCells()
 }))
 expect(coreMeter.tableCells-before).toBe(2)
})
full('primitive refusal and exceptional nested scopes discard permission and restore the hooks',()=>{
 const hook=tableAdmissionHook.admit,admit=runtimeWall.admit
 expect(()=>withBudget(1000,()=>withTableAdmission(()=>{
  observeTableCells();expect(()=>withTableAdmission(()=>{observeTableCells();throw Error('unwind')})).toThrow('unwind');observeTableCells()
  expect(()=>runtimeWall.admit!(1001,'refusal')).toThrow(BudgetExpired)
  const before=coreMeter.tableCells;expect(()=>observeTableCells()).toThrow(BudgetExpired);expect(coreMeter.tableCells).toBe(before)
 }))).toThrow(BudgetExpired)
 expect(tableAdmissionHook.admit).toBe(hook);expect(runtimeWall.admit).toBe(admit)
 expect(()=>withBudget(0,()=>withTableAdmission(()=>observeTableCells()))).toThrow(BudgetExpired)
})
full('the unchanged reader canonicalizer stops before exceeding a tight allowance',()=>{
 for(const W of [0,1,5,17,31]){
  const r=new Reader({name:'canonical bound',hyps:[]},trail),start=fullWork()
  expect(()=>withBudget(W,()=>withTableAdmission(()=>r.dec({long_variable_name:1,other_variable:-1})))).toThrow(BudgetExpired)
  expect(fullWork()-start).toBeLessThanOrEqual(W)
 }
})
