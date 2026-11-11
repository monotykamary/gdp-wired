// A strategy may use only this admitted view, never the raw captured roster.
// Rejection is conservative scheduling, not a proof of the remaining family.
// The caller supplies the rejected laws for its exact machine/context; final
// INIT/STEP and composed certificates still require the ordinary kernel check.
import {type Law,type Machine} from './machine.ts'
import {type Instances} from '../kernel/kernel.ts'
import {checkWall} from './wall.ts'

// Ignore display labels and alpha-renaming, not free names, constants, maps,
// quantifier kinds or structure. Local all-binders shadow the outer binders.
export function strategyLawKey(law:Law):string {
 const names=[law.forall,...law.keys??[],...law.some??[]].filter((name):name is string=>name!==undefined)
 if(new Set(names).size!==names.length)throw new Error('duplicate strategy law binder')
 const visit=(value:unknown,scope:readonly string[]):unknown=>{
  checkWall('strategy premise identity')
  if(!value||typeof value!=='object')return value
  if(Array.isArray(value))return value.map(v=>visit(v,scope))
  const object=value as Record<string,unknown>
  if(object.op==='var'&&typeof object.name==='string'){
   const index=scope.lastIndexOf(object.name)
   return index<0?['free',object.name]:['bound',scope.length-index-1]
  }
  if(object.op==='all'&&typeof object.key==='string'){
   const local=[object.key,...((object.keys as string[]|undefined)??[])]
   return ['all',local.length,visit(object.c,[...scope,...local])]
  }
  return Object.keys(object).sort().map(key=>[key,visit(object[key],scope)])
 }
 return JSON.stringify([law.forall!==undefined,law.keys?.length??0,law.some?.length??0,visit(law.holds,names)])
}
export function strategyPremiseSelector(machine:Machine,family:readonly Law[],rejected:readonly Law[]){
 const rows=family.map(law=>({law,name:law.name,key:strategyLawKey(law)}))
 if(new Set(family.map(law=>law.name)).size!==family.length)throw new Error('ambiguous strategy law name')
 const denied=new Set(rejected.map(strategyLawKey)),allowed=rows.filter(row=>!denied.has(row.key))
 const names=new Set(allowed.map(row=>row.law.name)),familyNames=new Set(family.map(law=>law.name))
 const flags=new Set(Object.keys(machine.step.flags??{}).map(name=>'?'+name).filter(name=>!familyNames.has(name)))
 const unchanged=()=>{
  for(const row of rows)if(row.law.name!==row.name||strategyLawKey(row.law)!==row.key)throw new Error('strategy family changed after selection')
 }
 const assertInstances=(instances:Instances)=>{
  unchanged()
  for(const name of Object.keys(instances))if(!names.has(name)&&!flags.has(name))throw new Error('rejected or unknown strategy premise: '+name)
 }
 return Object.freeze({
  find(predicate:(law:Law)=>boolean):Law|undefined{
   unchanged()
   const matches=allowed.filter(row=>predicate(row.law))
   unchanged()
   if(matches.length>1)throw new Error('ambiguous strategy premise')
   return matches[0]?.law
  },
  assertInstances,
  run<T>(instances:Instances,attempt:(laws:readonly Law[],instances:Instances)=>T):T{
   assertInstances(instances)
   // The same filtered family must build the goal; excluding a scalar's tuple
   // alone would not exclude its automatically assumed state-law premise.
   const result=attempt(Object.freeze(allowed.map(row=>row.law)),instances)
   assertInstances(instances)
   return result
  },
 })
}
