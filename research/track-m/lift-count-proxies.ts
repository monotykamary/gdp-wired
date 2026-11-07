// Untrusted linear recipe transport through explicit count-read equalities.
// Unlike widen's fallback this never launches a fresh whole-goal search.
import {type E,walkOnce} from '../../core/machine.ts'
import {type Lin,type Step,add,scale,solve,sub} from '../../core/solver.ts'
import {type CountCert,type Goal,type Path,type Tree,canon,check,columnTerm,linear,substE} from '../../kernel/kernel.ts'
import {rowsAt} from '../../kernel/prove.ts'

export function liftCountProxies(part:Goal,whole:Goal,tree:Tree,reads:CountCert['reads'],pp:Path=new Map(),wp:Path=new Map(),diagnose?:(event:object)=>void):Tree|undefined{
 const aliases=new Map<string,E>(reads.map(([id,map,key])=>[id,{op:'get',map,key}]))
 const substitutions=Object.fromEntries(aliases),terms=new Map<string,E|undefined>()
 const remapTerm=(name:string):E|undefined=>{
  if(terms.has(name))return terms.get(name)
  const term=columnTerm(name);let uses=false
  if(term)walkOnce(term,(o:any)=>{if(o.op==='var'&&aliases.has(o.name))uses=true})
  const mapped=term&&uses?substE(term,{vars:substitutions,maps:{},flags:{}}):undefined
  terms.set(name,mapped);return mapped
 }
 const replace=(lin:Lin,path:Path):Lin|undefined=>{
  let out:Lin={}
  for(const [name,coefficient] of Object.entries(lin)){
   const e=aliases.get(name)??remapTerm(name),value=e?linear(e,path):{[name]:1}
   if(!value||!e&&[...aliases.keys()].some(id=>name.includes(id)))return undefined
   out=add(out,scale(value,coefficient))
  }
  return out
 }
 const go=(t:Tree,source:Path,target:Path):Tree|undefined=>{
  if(!('leaf'in t)){
   const split=replace(t.split,target);if(!split)return undefined
   const id=canon(split),known=target.get(id)?.holds
   if(known!==undefined)return go(known?t.yes:t.no,new Map(source).set(canon(t.split),{lin:t.split,holds:known}),target)
   const yes=go(t.yes,new Map(source).set(canon(t.split),{lin:t.split,holds:true}),new Map(target).set(id,{lin:split,holds:true}))
   const no=yes&&go(t.no,new Map(source).set(canon(t.split),{lin:t.split,holds:false}),new Map(target).set(id,{lin:split,holds:false}))
   return yes&&no?{split,yes,no}:undefined
  }
  if(t.products?.length||t.squares?.length)return undefined
  const rp=rowsAt(part,source),rw=rowsAt(whole,target),exact=new Map<string,number>(),normalized=new Map<string,number>(),columns=new Map<string,string>()
  for(const [id,e] of aliases){const l=linear(e,target);if(!l)return undefined;const entries=Object.entries(l);if(entries.length!==1||entries[0]![1]!==1)return undefined;columns.set(entries[0]![0],id)}
  const normalize=(lin:Lin):Lin=>{let out:Lin={};for(const [name,c]of Object.entries(lin))out=add(out,{[columns.get(name)??name]:c});return out}
  rw.forEach((r,i)=>{const id=canon(r.lin),norm=canon(normalize(r.lin));if(!exact.has(id))exact.set(id,i);if(!normalized.has(norm))normalized.set(norm,i)})
  const steps:Step[]=[],indices:number[]=[]
  const input=(index:number)=>{steps.push({kind:'input',index});return steps.length-1}
  for(const s of t.leaf){
   if(s.kind==='input'){
    const row=rp[s.index];if(!row)return undefined
    const desired=replace(row.lin,target);if(!desired)return undefined
    const direct=exact.get(canon(desired))
    if(direct!==undefined){indices.push(input(direct));continue}
    const base=normalized.get(canon(row.lin));if(base===undefined){diagnose?.({reason:'missing-row',row:row.lin,desired});return undefined}
    let at=input(base),value=rw[base]!.lin
    for(const [id,e]of aliases){
     const c=value[id]??0;if(!c)continue
     const l=linear(e,target);if(!l)return undefined
     const bridge=sub(l,{[id]:1}),signed=c>0?bridge:scale(bridge,-1),r=exact.get(canon(signed));if(r===undefined){diagnose?.({reason:'missing-binding',id,row:signed});return undefined}
     const b=input(r);steps.push({kind:'combine',a:at,b,ma:1,mb:Math.abs(c)});at=steps.length-1
     value=add(value,scale(bridge,c))
    }
    if(canon(value)!==canon(desired))return undefined
    indices.push(at)
   }else if(s.kind==='combine'){
    const a=indices[s.a],b=indices[s.b];if(a===undefined||b===undefined)return undefined
    steps.push({...s,a,b});indices.push(steps.length-1)
   }else{
    const of=indices[s.of];if(of===undefined)return undefined
    steps.push({...s,of});indices.push(steps.length-1)
   }
  }
  return {leaf:steps}
 }
 const guards=new Map<string,Lin>()
 walkOnce(whole.hyps,(c:any)=>{
  if(c.op!=='or'||c.xs.length!==2)return
  const eq=c.xs.find((x:any)=>x.op==='='&&x.a.op==='var'&&aliases.has(x.a.name)),guard=c.xs.find((x:any)=>x!==eq)
  if(!eq||guard?.op!=='<=')return
  const a=linear(guard.a,wp),b=linear(guard.b,wp);if(!a||!b)return
  const lin=sub(a,b)
  if(Object.keys(lin).every(k=>k==='1')&&(lin['1']??0)>0)return
  guards.set(canon(lin),lin)
 })
 const all=[...guards.values()]
 const open=(i:number,path:Path):Tree|undefined=>{
  if(i===all.length)return go(tree,pp,path)
  const split=all[i]!,id=canon(split),known=path.get(id)?.holds
  if(known===false)return open(i+1,path)
  const badPath=new Map(path).set(id,{lin:split,holds:true}),out=solve(rowsAt(whole,badPath),2000)
  if(out.kind!=='refuted'){diagnose?.({reason:'domain-not-refuted',split});return undefined}
  const yes:Tree={leaf:out.steps};if(!check(whole,yes,badPath))return undefined
  if(known===true)return yes
  const no=open(i+1,new Map(path).set(id,{lin:split,holds:false}))
  return no?{split,yes,no}:undefined
 }
 const out=open(0,wp),checked=!!out&&check(whole,out,wp)
 diagnose?.({reason:'complete',guards:all.length,checked})
 return checked?out:undefined
}
