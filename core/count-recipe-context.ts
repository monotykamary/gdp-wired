// Diagnostics for the existing fixed-inventory policy, never authority to
// regenerate a pass or accept a proof. Counters do not affect control flow.
import {workLedger} from './work-admission.ts'
export type CountRecipeContextEvent={phase:'count-recipe-context',outcome:'refused',reason:'fixed-inventory-context-changed',structured:boolean}|{phase:'count-recipe-context',outcome:'reused',reason:'same-inventory-structured-reentry',structured:boolean,previousStructured:boolean,terminalRecipes:number,totalRecipes:number}
export type CountRecipeContextCounts={contextChanges:number,structuredReentries:number,terminalStructuredReentries:number}
const totals:CountRecipeContextCounts={contextChanges:0,structuredReentries:0,terminalStructuredReentries:0}
export const countRecipeContextSnapshot=():Readonly<CountRecipeContextCounts>=>({...totals})
export const countRecipeContextDifference=(after:Readonly<CountRecipeContextCounts>,before:Readonly<CountRecipeContextCounts>):CountRecipeContextCounts=>({contextChanges:after.contextChanges-before.contextChanges,structuredReentries:after.structuredReentries-before.structuredReentries,terminalStructuredReentries:after.terminalStructuredReentries-before.terminalStructuredReentries})
type FixedInventory={context:string,states:readonly {recipes:readonly {terminal:boolean}[]}[]}
export function countRecipeContextDecision(pass:FixedInventory,context:string,previousStructured:boolean|undefined,structured:boolean,observe?:(event:CountRecipeContextEvent)=>void):boolean{
 workLedger.start('ticks',1,'count recipe context decision')
 if(context!==pass.context){
  totals.contextChanges++
  observe?.({phase:'count-recipe-context',outcome:'refused',reason:'fixed-inventory-context-changed',structured})
  return false
 }
 if(previousStructured!==undefined&&previousStructured!==structured){
  let terminalRecipes=0,totalRecipes=0
  for(const state of pass.states){workLedger.start('ticks',1,'count recipe context member');for(const recipe of state.recipes){workLedger.start('ticks',1,'count recipe context recipe');totalRecipes++;if(recipe.terminal)terminalRecipes++}}
  totals.structuredReentries++;if(terminalRecipes===totalRecipes)totals.terminalStructuredReentries++
  observe?.({phase:'count-recipe-context',outcome:'reused',reason:'same-inventory-structured-reentry',structured,previousStructured,terminalRecipes,totalRecipes})
 }
 return true
}
