import {expect,test} from 'bun:test'
import {countRecipeContextDecision,countRecipeContextDifference,countRecipeContextSnapshot,type CountRecipeContextEvent} from './count-recipe-context.ts'
test('G2: changed context emits a typed refusal without altering the fixed inventory',()=>{
 const pass={context:'old bytes',states:[{recipes:[{terminal:true}]}]},before=JSON.stringify(pass),events:CountRecipeContextEvent[]=[],start=countRecipeContextSnapshot()
 expect(countRecipeContextDecision(pass,'changed bytes',false,false,event=>events.push(event))).toBe(false)
 expect(events).toEqual([{phase:'count-recipe-context',outcome:'refused',reason:'fixed-inventory-context-changed',structured:false}])
 expect(JSON.stringify(pass)).toBe(before);expect(countRecipeContextDifference(countRecipeContextSnapshot(),start)).toEqual({contextChanges:1,structuredReentries:0,terminalStructuredReentries:0})
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
