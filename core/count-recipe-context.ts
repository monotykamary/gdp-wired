// Bounded per-context recipe inventories; no proof acceptance authority.
// Counters are observations only and do not affect control flow.
import {workLedger} from './work-admission.ts'
export type CountRecipeContextEvent={phase:'count-recipe-context',outcome:'refused',reason:'fixed-inventory-context-changed',structured:boolean}|{phase:'count-recipe-context',outcome:'reused',reason:'same-inventory-structured-reentry',structured:boolean,previousStructured:boolean,terminalRecipes:number,totalRecipes:number}
export type CountRecipeContextCounts={contextChanges:number,structuredReentries:number,terminalStructuredReentries:number}
const totals:CountRecipeContextCounts={contextChanges:0,structuredReentries:0,terminalStructuredReentries:0}
// Observation only: these integers neither charge nor control any allowance.
export type CountRecipeInventoryCounts={passesCreated:number,sameContextReentries:number,capRefusals:number}
const inventoryTotals:CountRecipeInventoryCounts={passesCreated:0,sameContextReentries:0,capRefusals:0}
export const countRecipeInventorySnapshot=():Readonly<CountRecipeInventoryCounts>=>({...inventoryTotals})
export const countRecipeInventoryDifference=(after:Readonly<CountRecipeInventoryCounts>,before:Readonly<CountRecipeInventoryCounts>):CountRecipeInventoryCounts=>({passesCreated:after.passesCreated-before.passesCreated,sameContextReentries:after.sameContextReentries-before.sameContextReentries,capRefusals:after.capRefusals-before.capRefusals})
export const countRecipeContextSnapshot=():Readonly<CountRecipeContextCounts>=>({...totals})
export const countRecipeContextDifference=(after:Readonly<CountRecipeContextCounts>,before:Readonly<CountRecipeContextCounts>):CountRecipeContextCounts=>({contextChanges:after.contextChanges-before.contextChanges,structuredReentries:after.structuredReentries-before.structuredReentries,terminalStructuredReentries:after.terminalStructuredReentries-before.terminalStructuredReentries})
type FixedInventory={context:string,states:readonly {recipes:readonly {terminal:boolean}[]}[]}
// A fixed pass never changes its inventory. Distinct contexts get fresh passes
// under the same caller-owned allowance, with no held state or credit copied.
export const countRecipeContextCap=4
export class CountRecipeContexts<T extends FixedInventory>{
 private readonly entries=new Map<string,{pass:T,structured:boolean}>()
 private last:T|undefined
 get size():number{return this.entries.size}
 acquire(context:string,structured:boolean,create:()=>T,observe?:(event:CountRecipeContextEvent)=>void):T|undefined{
  const entry=this.entries.get(context)
  if(entry){
   // Keep the existing same-context comparison and diagnostic charges exactly.
   workLedger.start('tableCells',Math.min(context.length,entry.pass.context.length),'count recipe inventory context')
   if(!countRecipeContextDecision(entry.pass,context,entry.structured,structured,observe))return undefined
   inventoryTotals.sameContextReentries++
   entry.structured=structured;this.last=entry.pass
   return entry.pass
  }
  if(this.entries.size>=countRecipeContextCap){
   // Fifth distinct key: no inventory construction, search or new allowance.
   // The existing comparison/refusal event remains the only attempted work.
   const last=this.last!
   workLedger.start('tableCells',Math.min(context.length,last.context.length),'count recipe inventory context')
   countRecipeContextDecision(last,context,undefined,structured,observe)
   inventoryTotals.capRefusals++
   return undefined
  }
  const pass=create()
  if(pass.context!==context)throw Error('count recipe context factory mismatch')
  this.entries.set(context,{pass,structured});this.last=pass
  inventoryTotals.passesCreated++
  return pass
 }
}
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
