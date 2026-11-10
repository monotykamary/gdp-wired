// Untrusted family instances demanded by a model of a count-witness source.
// Count-read keys retain the kernel's freshness rule. Returned tuples are only
// ordinary candidates: rebuild the obligation and check the complete family.
import {type Law,type Machine,walkOnce} from '../machine.ts'
import {type Goal,type Instances} from '../../kernel/kernel.ts'
import {modelInstances} from '../../kernel/prove.ts'
import {independentCountInstances} from '../count-focused.ts'
export function sourceWitnessInstances(m:Machine,laws:Law[],at:Instances,goal:Goal,model:Record<string,number>,witnesses:ReadonlySet<string>):Instances|undefined{
 // Select proposal keys from the queried witness body, not unrelated flag
 // witnesses that happen to share its model value. This weak slice proposes
 // terms only; the rebuilt, complete obligation remains the proof target.
 const hyps=goal.hyps.filter(c=>{let reads=false;walkOnce(c,(o:any)=>{if(o.op==='var'&&witnesses.has(o.name))reads=true});return reads})
 if(!hyps.length)return undefined
 const proposed=modelInstances(m,laws,at,{...goal,hyps},model,32)
 const valid=proposed&&independentCountInstances(m,laws,at,proposed,[...witnesses])
 if(!valid)return undefined
 let out=at,added=0
 for(const law of laws){
  if(!law.forall)continue
  const before=at[law.name]??[],next=valid[law.name]??before,arity=1+(law.keys?.length??0),extra:typeof before=[]
  for(let i=before.length;i+arity<=next.length&&added<8;i+=arity){extra.push(...next.slice(i,i+arity));added++}
  if(extra.length){if(out===at)out={...at};out[law.name]=[...before,...extra]}
 }
 return out===at?undefined:out
}
