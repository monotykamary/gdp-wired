import {expect,test} from 'bun:test'
import {countGenerationPhase} from './count-generation-phase.ts'
import {BudgetExpired,checkBudget,checkWorkAdmission,clock,counted,fullRate,withBudget} from '../kernel/prove.ts'
const full=(run:()=>void)=>counted(fullRate,run,true)
test('generation keeps successful return values unchanged',()=>{
 full(()=>withBudget(1000,()=>{
  const value={tag:'same'}
  expect(countGenerationPhase(clock()+1,()=>value)).toEqual({complete:true,value})
 }))
})
test('a local pre-charge refusal preserves the enclosing allowance',()=>{
 full(()=>withBudget(1000,()=>{
  const result=countGenerationPhase(clock()+1/fullRate,()=>checkWorkAdmission(2,'local test'))
  expect(result).toEqual({complete:false})
  expect(()=>checkBudget('parent survives')).not.toThrow()
 }))
})
test('a shared outer refusal cannot become partial-generation success',()=>{
 expect(()=>full(()=>withBudget(1,()=>{
  countGenerationPhase(clock()+100,()=>checkWorkAdmission(2,'outer test'))
 }))).toThrow(BudgetExpired)
})
test('an exhausted generation phase does not run or hide ordinary errors',()=>{
 full(()=>withBudget(1000,()=>{
  let called=false
  expect(countGenerationPhase(clock(),()=>{called=true})).toEqual({complete:false})
  expect(called).toBe(false)
  expect(()=>countGenerationPhase(clock()+1,()=>{throw new Error('ordinary')})).toThrow('ordinary')
 }))
})
