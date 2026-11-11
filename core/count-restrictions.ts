// Fresh conservative count definitions for opt-in proof strategies.
// Pure definitions only: original fields, transitions and counts are unchanged.
import {type Counted,type Machine,get,n,not,x} from './machine.ts'
import {substE} from '../kernel/kernel.ts'
export type Restriction={base:string,input:string,positive:string,negative:string}
export function restrictedCounts(m:Machine,selected:readonly string[]=Object.keys(m.counts??{}),cap=32,memberKey?:string):{machine:Machine,entries:Restriction[]}{
 if(!Number.isSafeInteger(cap)||cap<0||cap>128)throw Error('invalid restricted-count cap')
 const entries:Restriction[]=[],added:Record<string,Counted>={},occupied=new Set([...Object.keys(m.counts??{}),...Object.keys(m.maps??{}),...(m.inputMaps??[]),...Object.keys(m.state)])
 for(const base of new Set(selected)){
  const source=m.counts?.[base];if(!source)continue
  if(memberKey&&memberKey!==source.key&&JSON.stringify(source).includes(JSON.stringify(memberKey)))throw Error('restricted-count binder capture')
  const definition=memberKey&&memberKey!==source.key?{...source,key:memberKey,body:substE(source.body,{vars:{[source.key]:x(memberKey)},maps:{},flags:{}})}:source
  for(const input of new Set(m.inputMaps??[])){
   if(entries.length>=cap)break
   const positive=`${base}$restricted$${input}`,negative=`${positive}$not`
   if(occupied.has(positive)||occupied.has(negative))throw Error('restricted-count name collision')
   occupied.add(positive);occupied.add(negative)
   const guard={op:'<' as const,a:n(0),b:get(input,x(definition.key))}
   added[positive]={...definition,body:{op:'if',c:guard,then:definition.body,else:n(0)}}
   added[negative]={...definition,body:{op:'if',c:not(guard),then:definition.body,else:n(0)}}
   entries.push({base,input,positive,negative})
  }
 }
 return {machine:entries.length?{...m,counts:{...m.counts,...added}}:m,entries}
}
