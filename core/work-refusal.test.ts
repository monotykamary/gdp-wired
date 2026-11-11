import {expect,test} from 'bun:test'
import {BudgetExpired,WorkLedger} from './work-admission.ts'
import {type WorkKey,workKeys} from './work-kinds.ts'
import {workAmount} from './work-amount.ts'
const ledger=()=>new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
function failure(run:()=>void):unknown{try{run()}catch(error){return error}throw Error('expected capacity refusal')}
test('genuine child capacity refusal retains the exact limiting scope after exit',()=>{
 const bank=ledger();let child=0
 const error=failure(()=>bank.withBudget(workAmount(10n),()=>bank.withBudget(workAmount(2n),()=>{
  child=bank.currentScope()!.id;bank.start('ticks',2);bank.start('ticks')
 })))
 expect(error).toBeInstanceOf(BudgetExpired)
 const receipt=bank.capacityRefusal(error)!
 expect(receipt.reason).toBe('quantum');expect(receipt.limiting.map(scope=>scope.id)).toEqual([child])
 expect(receipt.actual).toEqual({numerator:'2',denominator:'1'});expect(bank.bounded()).toBe(false)
 expect(Object.isFrozen(receipt)).toBe(true);expect(Object.isFrozen(receipt.limiting)).toBe(true)
})
test('tied child and ancestor endpoints remain explicit rather than being relabelled soft',()=>{
 const bank=ledger();let root=0,child=0
 const error=failure(()=>bank.withBudget(workAmount(2n),()=>{
  root=bank.currentScope()!.id
  bank.withBudget(workAmount(2n),()=>{child=bank.currentScope()!.id;bank.start('ticks',3)})
 }))
 expect(bank.capacityRefusal(error)!.limiting.map(scope=>scope.id)).toEqual([root,child])
 expect(bank.actual().num).toBe(0n);expect(bank.reserved().num).toBe(0n)
})
test('atomic partial grants identify the boundary without starting or retaining work',()=>{
 const bank=ledger(),error=failure(()=>bank.withBudget(workAmount(2n),()=>bank.start('ticks',3)))
 expect(bank.capacityRefusal(error)!.requested).toEqual({numerator:'3',denominator:'1'})
 expect(bank.counter('ticks')).toBe(0n);expect(bank.reserved().num).toBe(0n)
})
test('lookalike errors, stale leases and another ledger cannot forge capacity provenance',()=>{
 const bank=ledger();expect(bank.capacityRefusal(new BudgetExpired('ticks'))).toBeUndefined()
 const other=ledger(),error=failure(()=>other.withBudget(workAmount(0n),()=>other.start('ticks')))
 expect(bank.capacityRefusal(error)).toBeUndefined()
 let stale:()=>void=()=>{};bank.withBudget(workAmount(2n),()=>bank.withChunk('ticks',1,lease=>{stale=()=>lease.start()}))
 const expired=failure(stale);expect(bank.capacityRefusal(expired)).toBeUndefined()
})
