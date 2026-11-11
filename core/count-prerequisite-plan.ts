// Pre-execution citations from the same structural selectors as the emitters.
// Conservative offers are scheduling only; returned certificate scopes remain
// authoritative, and an unattempted surprise citation is never published.
import {type Law,type Machine,all,n,same,walk,x} from './machine.ts'
import {type CountComponentRecipe} from './count-prerequisite-components.ts'
import {finiteCountChoice} from './count-cases.ts'
import {discoverRowAgreement} from './row-agreement-shape.ts'
import {rowCountSupport} from './count-row-support.ts'
import {countStrategyKind} from './count-strategies.ts'
import {prepareGuardCountContext} from './count-guard-context.ts'
import {countLeaderPremise} from './count-leader.ts'
import {discoverCountThresholdWrite} from './count-write-shape.ts'
import {discoverLiftedCountGuard} from './count-lifted-shape.ts'
import {discoverLiftedCountPrerequisites} from './count-lifted-prerequisite.ts'
import {discoverCountRowLoad} from './count-load-shape.ts'
const shapeSize=(value:unknown):number=>value&&typeof value==='object'?1+Object.values(value).reduce<number>((sum,item)=>sum+shapeSize(item),0):0
export function countPrerequisiteSchedule(m:Machine,family:Law[],selected:ReadonlySet<Law>,until:number){
 const out=new Map<string,readonly string[]>(),recipes=new Map<string,readonly CountComponentRecipe[]>(),costs=new Map<string,number>()
 for(const owner of family){
  const ordinary:CountComponentRecipe={id:'ordinary',kind:'ordinary'}
  recipes.set(owner.name,[ordinary])
  const shape=(owner.keys?.length??0)*1000+shapeSize(owner.holds)
  let countRead=false
  walk(owner.holds,node=>{if(node.op==='get'&&typeof node.map==='string'&&m.counts?.[node.map])countRead=true})
  costs.set(owner.name,shape+(countRead?100000:0))
  if(!selected.has(owner))continue
  const offered=new Set<Law>(),kind=countStrategyKind(m,family,owner),choice=finiteCountChoice(m)
  if(kind==='row'){
   const row=discoverRowAgreement(m,owner)!
   // The generic row instantiation pool is optional, not a required edge.
   // Actual ordinary/row scopes can add dependencies without admitting them.
   if(choice)for(const value of choice[1]){
    const fixed={...m,assume:all(...(m.assume?[m.assume]:[]),same(x(choice[0]),n(value)))},support=rowCountSupport(fixed,family,owner,row,until)
    for(const name of Object.keys(support?.options.seedInstances??{})){const law=family.find(l=>l.name===name);if(law)offered.add(law)}
   }
  }else if(kind==='guard'){
   const context=prepareGuardCountContext(m,owner,family)
   for(const law of context?.shape.phase?.laws??[])offered.add(law)
   if(context&&choice&&[...choice[1]].some(value=>discoverCountThresholdWrite(m,context.shape,{name:choice[0],value})?.increment===1)){
    const pair=countLeaderPremise(m,context.shape,family);if(pair)offered.add(pair.law)
   }
  }else if(kind==='lifted'){
   const shape=discoverLiftedCountGuard(m,owner,family)
   if(shape){
    if(shape.rowAgreements[0])offered.add(shape.rowAgreements[0].law)
    const prerequisites=discoverLiftedCountPrerequisites(m,owner,family)
    // Emitters try the offered candidates in this order. Limit the first
    // attempt to this citation; a failed premise cannot be assumed instead.
    if(prerequisites[0])offered.add(prerequisites[0].law)
    for(const law of shape.countShape.phase?.laws??[])offered.add(law)
    if(choice)for(const value of choice[1]){
     const load=discoverCountRowLoad(m,shape,family,{name:choice[0],value})
     if(load){offered.add(load.law);for(const law of load.phaseLaws)offered.add(law)}
    }
   }
  }
  offered.delete(owner)
  const required=Object.freeze(family.filter(l=>offered.has(l)).map(l=>l.name))
  out.set(owner.name,required)
  if(kind){
   recipes.set(owner.name,[{id:kind,kind:'strategy',required},ordinary])
   costs.set(owner.name,1000000+({guard:1,row:2,lifted:3}[kind])*10000+shape)
  }
 }
 return {requirements:out,recipes,costs}
}
export function countPrerequisitePlan(m:Machine,family:Law[],selected:ReadonlySet<Law>,until:number):Map<string,readonly string[]>{
 return countPrerequisiteSchedule(m,family,selected,until).requirements
}
