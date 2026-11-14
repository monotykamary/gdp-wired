import {expect,test} from 'bun:test'
import {CountRecipePass} from './count-recipe-controller.ts'
import {WorkLedger} from './work-admission.ts'
import {workKeys,type WorkKey} from './work-kinds.ts'
import {workAmount,workFromExact,workSub,workAdd,compareWork,zeroWork} from './work-amount.ts'
import {CountRecipeContexts,countRecipeInventorySnapshot,countRecipeInventoryDifference,countRecipeContextDecision,countRecipeContextDifference,countRecipeContextSnapshot,type CountRecipeContextEvent} from './count-recipe-context.ts'
test('G2: independent contexts get fresh passes, four maximum, with the existing fifth-key refusal',()=>{
 const registry=new CountRecipeContexts<{context:string,states:{recipes:{terminal:boolean}[]}[],held:string[],fuel:number}>(),events:CountRecipeContextEvent[]=[]
 const start=countRecipeInventorySnapshot();let made=0
 const make=(context:string)=>()=>{made++;return {context,states:[{recipes:[{terminal:false}]}],held:[] as string[],fuel:7}}
 const first=registry.acquire('first',false,make('first'))!
 first.held.push('proof citing removed law');first.fuel=0;first.states[0]!.recipes[0]!.terminal=true
 const second=registry.acquire('second',false,make('second'))!
 expect(second).not.toBe(first);expect(second.held).toEqual([]);expect(second.fuel).toBe(7);expect(second.states[0]!.recipes[0]!.terminal).toBe(false)
 expect(registry.acquire('first',false,make('first'))).toBe(first);expect(first.fuel).toBe(0)
 registry.acquire('third',false,make('third'));registry.acquire('fourth',false,make('fourth'))
 expect(registry.acquire('fifth',true,make('fifth'),event=>events.push(event))).toBeUndefined()
 expect(registry.size).toBe(4);expect(made).toBe(4)
 expect(events).toEqual([{phase:'count-recipe-context',outcome:'refused',reason:'fixed-inventory-context-changed',structured:true}])
 expect(countRecipeInventoryDifference(countRecipeInventorySnapshot(),start)).toEqual({passesCreated:4,sameContextReentries:1,capRefusals:1})
 expect(first.held).toEqual(['proof citing removed law'])
})
test('G2: native passes carry no held proof, terminal state, spent allocation or ancestor credit across keys',()=>{
 const bank=new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>),registry=new CountRecipeContexts<CountRecipePass<string>>()
 const make=(context:string)=>()=>new CountRecipePass<string>([{name:'target',reference:0,recipes:[{id:'row',kind:'strategy'}]}],context,bank)
 bank.withBudget(workAmount(1000n),()=>bank.withBudget(workAmount(800n),()=>{
  const first=registry.acquire('with removed law',false,make('with removed law'))!,state=first.states[0]!,recipe=state.recipes[0]!
  state.held={payload:'certificate citing absent law',premises:['removed'],checkedReduced:true,checkCost:workAmount(2n),recipeId:'row'}
  state.allotted=workAmount(20n);state.allocationRemaining=workAmount(3n);state.used=workAmount(17n)
  expect(recipe.tickets.start()).toBe(true);recipe.tickets.finish('decline');recipe.terminal=true;first.supplierRepairUsed=true
  bank.start('ticks',7,'spent work before context change')
  const before=bank.snapshot(),second=registry.acquire('without removed law',false,make('without removed law'))!,after=bank.snapshot(),fresh=second.states[0]!
  expect(second).not.toBe(first);expect(second.bank).toBe(bank);expect(second.rootEpoch).toBe(first.rootEpoch);expect(second.rootEnd).toEqual(first.rootEnd)
  expect(second.held().size).toBe(0);expect(fresh.held).toBeUndefined();expect(fresh.allotted).toBeUndefined();expect(fresh.allocationRemaining).toBeUndefined();expect(fresh.used).toEqual(zeroWork)
  expect(fresh.recipes[0]!.terminal).toBe(false);expect(fresh.recipes[0]!.keys).toEqual([]);expect(fresh.recipes[0]!.tickets.snapshot()).toEqual({remaining:7,started:0,active:false,terminal:false});expect(second.supplierRepairUsed).toBe(false)
  expect(after.rootEpoch).toBe(before.rootEpoch);expect(after.activeEndpoints).toEqual(before.activeEndpoints)
  const spent=workSub(workFromExact(after.actual),workFromExact(before.actual));expect(compareWork(spent,zeroWork)).toBeGreaterThan(0)
  for(const end of before.activeEndpoints){
   const beforeFree=workSub(workFromExact(end.end),workAdd(workFromExact(before.actual),workFromExact(before.reserved)))
   const afterFree=workSub(workFromExact(end.end),workAdd(workFromExact(after.actual),workFromExact(after.reserved)))
   expect(afterFree).toEqual(workSub(beforeFree,spent))
  }
 }))
})
test('G2: a terminal structured re-entry is visible, retains the same states, and grants nothing',()=>{
 const recipes=[{terminal:true},{terminal:true}],pass={context:'fixed',states:[{recipes}]},events:CountRecipeContextEvent[]=[],start=countRecipeContextSnapshot()
 expect(countRecipeContextDecision(pass,'fixed',false,true,event=>events.push(event))).toBe(true)
 expect(pass.states[0]!.recipes).toBe(recipes);expect(recipes).toEqual([{terminal:true},{terminal:true}])
 expect(events).toEqual([{phase:'count-recipe-context',outcome:'reused',reason:'same-inventory-structured-reentry',structured:true,previousStructured:false,terminalRecipes:2,totalRecipes:2}])
 expect(countRecipeContextDifference(countRecipeContextSnapshot(),start)).toEqual({contextChanges:0,structuredReentries:1,terminalStructuredReentries:1})
})
test('G2: unstarted recipes remain distinguishable from a wholly terminal re-entry',()=>{
 const start=countRecipeContextSnapshot(),events:CountRecipeContextEvent[]=[]
 expect(countRecipeContextDecision({context:'same',states:[{recipes:[{terminal:true},{terminal:false}]}]},'same',false,true,event=>events.push(event))).toBe(true)
 expect(events[0]).toMatchObject({terminalRecipes:1,totalRecipes:2});expect(countRecipeContextDifference(countRecipeContextSnapshot(),start)).toEqual({contextChanges:0,structuredReentries:1,terminalStructuredReentries:0})
})
