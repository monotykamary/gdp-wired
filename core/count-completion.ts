// One bounded completion of assumed count-reading laws at the goal's own terms.
// Every tuple retains the entire original premise; the ordinary kernel checks it.
import {type E,type Law} from './machine.ts'
import {type Instances} from '../kernel/kernel.ts'
export function completeCountLawInstances(laws:Law[],at:Instances,terms:E[],readsCount:(law:Law)=>boolean,more:()=>boolean=()=>true):{at:Instances,added:{law:string,tuple:E[]}[]}{
 const keys=[...new Map(terms.map(t=>[JSON.stringify(t),t])).values()].slice(0,4),added:{law:string,tuple:E[]}[]=[]
 let next=at
 for(const law of laws){
  if(!law.forall||!readsCount(law))continue
  const arity=1+(law.keys?.length??0),old=at[law.name]??[]
  if(arity>2||old.length%arity)continue
  const seen=new Set(Array.from({length:old.length/arity},(_,i)=>JSON.stringify(old.slice(i*arity,(i+1)*arity)))),fresh:E[]=[]
  const tuples=arity===1?keys.map(t=>[t]):keys.flatMap(a=>keys.map(b=>[a,b]))
  for(const tuple of tuples){
   if(added.length>=48||!more())return{at:next,added}
   const id=JSON.stringify(tuple);if(seen.has(id))continue
   seen.add(id);fresh.push(...tuple);added.push({law:law.name,tuple})
   if(next===at)next={...at}
   next[law.name]=[...old,...fresh]
  }
 }
 return{at:next,added}
}
