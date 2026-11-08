// Untrusted carried-set inclusions. Flag equalities suggest substitutions;
// ordinary count witnesses and independent conditional cuts prove every result.
import {type C,type E,type Machine,n,same,walkOnce,x} from '../machine.ts'
import {type CountCert,type CountDecl,substC,substE} from '../../kernel/kernel.ts'
import {countsForReads} from '../count-facts.ts'
import {bounded} from './scalar-guards.ts'
export type MemberInclusion={positive:string,negative:string,carried:string,below:E,guards:C[]}
const text=(v:unknown)=>JSON.stringify(v)
const member=(c:C):Extract<E,{op:'get'}>|undefined=>{
 if(c.op==='='&&c.a.op==='get'&&c.b.op==='const'&&c.b.value===1)return c.a
 if(c.op==='='&&c.b.op==='get'&&c.a.op==='const'&&c.a.value===1)return c.b
 if(c.op==='<'&&c.a.op==='const'&&c.a.value===0&&c.b.op==='get')return c.b
 if(c.op==='<='&&c.a.op==='const'&&c.a.value===1&&c.b.op==='get')return c.b
 return undefined
}
const predicate=(e:E):C|undefined=>e.op==='if'&&e.then.op==='const'&&e.then.value===1&&e.else.op==='const'&&e.else.value===0?e.c:e.op==='get'?same(e,n(1)):undefined
const parts=(c:C):C[]=>c.op==='and'?c.xs.flatMap(parts):[c]
export function memberInclusions(m:Machine,ds:CountDecl[],reads:CountCert['reads']):MemberInclusion[]{
 const picked=reads.filter(([,map])=>!map.endsWith('#')),names=new Set(picked.map(r=>r[1])),decls=ds.filter(d=>names.has(d.map))
 if(!m.inputMaps?.length||!bounded([m.step.flags,decls,picked]))return []
 const counts=countsForReads(decls,picked);if(!counts)return []
 const used=new Set<string>();walkOnce([m.step.flags,decls,picked],(o:any)=>{if(o.op==='var')used.add(o.name)})
 let key='inclusion$member';while(used.has(key))key+='$'
 const mentions=(v:unknown)=>{let found=false;walkOnce(v,(o:any)=>{if(o.op==='var'&&o.name===key)found=true});return found}
 const inputs=new Set(m.inputMaps),facts=new Map<string,{known:Set<string>,anchors:Map<string,E>}>()
 for(const q of Object.values(m.step.flags??{})){
  if(q.op!=='all'||q.keys?.length)continue
  const c=substC(q.c,{vars:{[q.key]:x(key)},maps:{},flags:{}})
  if(c.op!=='or'||c.xs.length!==2)continue
  for(let i=0;i<2;i++){
   const a=c.xs[i]!,source=a.op==='not'?member(a.x):undefined
   if(!source||!inputs.has(source.map)||source.key.op!=='var'||source.key.name!==key)continue
   const entry=facts.get(source.map)??{known:new Set<string>(),anchors:new Map<string,E>()}
   for(const consequent of parts(c.xs[1-i]!)){
    const membership=member(consequent);if(membership)entry.known.add(text(membership))
    if(consequent.op!=='=')continue
    for(const [from,to]of [[consequent.a,consequent.b],[consequent.b,consequent.a]]){
     if(from!.op==='get'&&to!.op==='get'&&mentions(from!.key)&&!mentions(to)&&!entry.anchors.has(text(from)))entry.anchors.set(text(from),to!)
    }
   }
   facts.set(source.map,entry)
  }
 }
 const out:MemberInclusion[]=[],seen=new Set<string>();let work=20000
 for(const a of counts){
  const body=substE(a.body,{vars:{[a.key]:x(key)},maps:{},flags:{}}),p=predicate(body),source=p&&member(p)
  if(!source||!inputs.has(source.map)||source.key.op!=='var'||source.key.name!==key)continue
  const entry=facts.get(source.map);if(!entry?.anchors.size)continue
  const known=new Set([...entry.known,text(source)])
  for(const b of counts){
   if(--work<0||out.length>=128)return out
   if(a.v===b.v||text(a.below)!==text(b.below))continue
   const target=predicate(substE(b.body,{vars:{[b.key]:x(key)},maps:{},flags:{}}));if(!target)continue
   let changed=false
   const maps=Object.fromEntries([...new Set([...entry.anchors.keys()].map(k=>(JSON.parse(k) as Extract<E,{op:'get'}>).map))].map(map=>[map,(at:E):E=>{
    const from={op:'get' as const,map,key:at},to=entry.anchors.get(text(from));if(to){changed=true;return to}return from
   }]))
   const rewritten=substC(target,{vars:{},maps,flags:{}})
   if(!changed)continue
   const simplify=(c:C):C|boolean=>{
    const view=member(c);if(view&&known.has(text(view)))return true
    if(c.op==='and'||c.op==='or'){
     const xs=c.xs.map(simplify),and=c.op==='and'
     if(xs.includes(!and))return !and
     const rest=xs.filter(v=>typeof v!=='boolean') as C[]
     return !rest.length?and:rest.length===1?rest[0]!:{op:c.op,xs:rest}
    }
    if(c.op==='not'){const v=simplify(c.x);return typeof v==='boolean'?!v:{op:'not',x:v}}
    if(c.op==='='||c.op==='<'||c.op==='<='){
     if(text(c.a)===text(c.b))return c.op!=='<'
     if(c.a.op==='const'&&c.b.op==='const')return c.op==='='?c.a.value===c.b.value:c.op==='<'?c.a.value<c.b.value:c.a.value<=c.b.value
    }
    return c
   }
   const reduced=simplify(rewritten);if(reduced===false||typeof reduced!=='boolean'&&mentions(reduced))continue
   const guards=reduced===true?[]:parts(reduced)
   if(guards.some(c=>!['=','<','<='].includes(c.op)))continue
   const id=text([a.v,b.v,guards]);if(seen.has(id))continue;seen.add(id)
   out.push({positive:a.v,negative:b.v,carried:source.map,below:a.below,guards})
  }
 }
 return out
}
