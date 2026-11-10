// Untrusted, bounded instances of existing field laws at source rows.
// The ordinary counted-obligation checker reconstructs every premise.
import {type E,type Law,type Machine,walkOnce} from '../machine.ts'
import {type Instances} from '../../kernel/kernel.ts'
import {fieldLawBridges,rowKeyNames} from '../count-focused.ts'

export function instantiateRowPremises(m:Machine,laws:Law[],target:Law,at:Instances,own:E[],request:E[],cap:number,more:()=>boolean=()=>true){
 const added:{law:string,tuple:E[]}[]=[]
 const result=()=>({at:next,added})
 let next=at
 if(cap<=0||own.length!==3||!target.forall||!laws.includes(target)||!more())return result()
 let counted=false
 walkOnce(target.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])counted=true})
 const names=[target.forall,...target.keys??[]],rowNames=rowKeyNames(m,target)
 const rows=own.filter((_,i)=>rowNames.has(names[i]!))
 if(counted||rows.length!==2||rowNames.has(names[2]!))return result()
 const ordered=[target,...laws.filter(l=>l!==target)].filter(l=>!l.some?.length)
 const bridges=fieldLawBridges(m,ordered,at,rows,request.slice(0,4),own[2])
 for(const law of ordered){
  if(added.length>=cap||!more())break
  if(!law.forall)continue
  const width=1+(law.keys?.length??0),old=at[law.name]??[]
  if(width>3||old.length%width)continue
  const proposed=law===target?[...own,...bridges[law.name]??[]]:bridges[law.name]??[]
  const seen=new Set(Array.from({length:old.length/width},(_,i)=>JSON.stringify(old.slice(i*width,(i+1)*width))))
  for(let i=0;i+width<=proposed.length;i+=width){
   if(added.length>=cap||seen.size>=4||!more())break
   const tuple=proposed.slice(i,i+width),key=JSON.stringify(tuple)
   if(seen.has(key))continue
   seen.add(key)
   if(next===at)next={...at}
   next[law.name]=[...next[law.name]??[],...tuple]
   added.push({law:law.name,tuple})
  }
 }
 return result()
}
