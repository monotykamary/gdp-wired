import {expect,test} from 'bun:test'
import {countGenerationPhase} from './count-generation-phase.ts'
import {BudgetExpired,checkBudget,checkWorkAdmission,clock,counted,fullRate,fullWork,withBudget,withWork} from '../kernel/prove.ts'
const full=(run:()=>void)=>counted(fullRate,run,true)
function refusal(){try{checkWorkAdmission(2,'T279 native pre-admission')}catch(error){expect(error).toBeInstanceOf(BudgetExpired);throw error}}
test('bare inherited withWork cap propagates the native parent refusal',()=>{
 let returned:unknown,error:unknown,inner=false,parentCheck=false
 full(()=>withWork(fullWork()+1,()=>{
  try{returned=countGenerationPhase(clock()+100,()=>{inner=true;refusal()})}catch(caught){error=caught}
  try{checkBudget('T279 bare parent after return');parentCheck=true}catch{}
 }))
 console.log('T279_BARE_WORK '+JSON.stringify({inner,returned,escaped:error instanceof BudgetExpired,parentCheck}))
 expect(inner).toBe(true)
 expect(error).toBeInstanceOf(BudgetExpired)
})
test('a strictly smaller generation child still returns partial under bare withWork',()=>{
 let returned:unknown,parentAlive=false
 full(()=>withWork(fullWork()+1000,()=>{
  returned=countGenerationPhase(clock()+1/fullRate,refusal)
  checkBudget('T279 live bare parent');parentAlive=true
 }))
 console.log('T279_LOCAL_CHILD '+JSON.stringify({returned,parentAlive}))
 expect(returned).toEqual({complete:false})
 expect(parentAlive).toBe(true)
})
test('an explicit outer withBudget preserves the native parent refusal',()=>{
 let error:unknown,returned:unknown
 try{full(()=>withBudget(1,()=>{returned=countGenerationPhase(clock()+100,refusal)}))}catch(caught){error=caught}
 console.log('T279_OUTER_BUDGET '+JSON.stringify({returned,escaped:error instanceof BudgetExpired}))
 expect(error).toBeInstanceOf(BudgetExpired)
 expect(returned).toBeUndefined()
})
