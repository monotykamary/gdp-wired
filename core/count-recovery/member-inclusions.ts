// Untrusted carried-set inclusions. Flag equalities suggest substitutions;
// upper bounds suggest sufficient scalar guards, not substitutions. Ordinary
// count witnesses and independent conditional cuts prove every result.
import {type C,type E,type Machine,n,same,walkOnce,x} from '../machine.ts'
import {type CountCert,type CountDecl,type CountInst,substC,substE} from '../../kernel/kernel.ts'
import {countsForReads} from '../count-facts.ts'
import {bounded} from './scalar-guards.ts'
export type MemberInclusion={positive:string,negative:string,carried:string,below:E,guards:C[]}
type UpperBound={bound:E,strict:boolean}
// The ordinary pool already contains many pairs, but model-driven selection can
// miss a useful inclusion when its target count is otherwise unconstrained.
// Prefer only existing witness instances suggested by the flag syntax. Their
// scalar guards are not asserted: mcGoal must still prove every witness branch.
export function preferMemberInclusions<T extends Pick<CountCert,'reads'|'insts'> & Partial<Pick<CountCert,'picks'>>>(m:Machine,ds:CountDecl[],full:T,picked:T,cap=10,more?:()=>boolean):T {
 const room=cap-(picked.picks?.length??0)
 if(room<=0||picked.insts.length>room||!m.inputMaps?.length||!full.insts.length)return picked
 const vector=(q:Pick<CountInst,'terms'|'unit'|'below'>)=>text([q.unit,q.below,[...q.terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0])])
 const available=new Map(full.insts.map(q=>[vector(q),q])),preferred:CountInst[]=[]
 for(const p of memberInclusions(m,ds,full.reads,more)){
  const q=available.get(vector({unit:0,below:p.below,terms:[[1,p.positive],[-1,p.negative]]}))
  if(q)preferred.push(q)
 }
 if(!preferred.length)return picked
 const seen=new Set<string>(),insts=[...preferred,...picked.insts].filter(q=>{const k=vector(q);if(seen.has(k))return false;seen.add(k);return true}).slice(0,room)
 return {...picked,insts}
}
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
export function memberInclusions(m:Machine,ds:CountDecl[],reads:CountCert['reads'],more?:()=>boolean):MemberInclusion[]{
 if(more&&!more())return []
 const picked=reads.filter(([,map])=>!map.endsWith('#')),names=new Set(picked.map(r=>r[1])),decls=ds.filter(d=>names.has(d.map))
 if(!m.inputMaps?.length||!bounded([m.step.flags,decls,picked]))return []
 const counts=countsForReads(decls,picked);if(!counts)return []
 const used=new Set<string>();walkOnce([m.step.flags,decls,picked],(o:any)=>{if(o.op==='var')used.add(o.name)})
 let key='inclusion$member';while(used.has(key))key+='$'
 const mentions=(v:unknown)=>{let found=false;walkOnce(v,(o:any)=>{if(o.op==='var'&&o.name===key)found=true});return found}
 const inputs=new Set(m.inputMaps),facts=new Map<string,{known:Set<string>,conditions:Set<string>,anchors:Map<string,E>,upper:Map<string,UpperBound>}>()
 for(const q of Object.values(m.step.flags??{})){
  if(more&&!more())return []
  if(q.op!=='all'||q.keys?.length)continue
  const c=substC(q.c,{vars:{[q.key]:x(key)},maps:{},flags:{}})
  if(c.op!=='or'||c.xs.length!==2)continue
  for(let i=0;i<2;i++){
   const a=c.xs[i]!,source=a.op==='not'?member(a.x):undefined
   if(!source||!inputs.has(source.map)||source.key.op!=='var'||source.key.name!==key)continue
   const entry=facts.get(source.map)??{known:new Set<string>(),conditions:new Set<string>(),anchors:new Map<string,E>(),upper:new Map<string,UpperBound>()}
   for(const consequent of parts(c.xs[1-i]!)){
    entry.conditions.add(text(consequent))
    const membership=member(consequent);if(membership)entry.known.add(text(membership))
    if((consequent.op==='<'||consequent.op==='<=')&&consequent.a.op==='get'&&mentions(consequent.a.key)&&!mentions(consequent.b)&&!entry.upper.has(text(consequent.a)))entry.upper.set(text(consequent.a),{bound:consequent.b,strict:consequent.op==='<'})
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
  const entry=facts.get(source.map);if(!entry||!entry.anchors.size&&!entry.upper.size)continue
  const known=new Set([...entry.known,text(source)])
  for(const b of counts){
   if(--work<0||out.length>=128||more&&!more())return out
   if(a.v===b.v||text(a.below)!==text(b.below))continue
   const target=predicate(substE(b.body,{vars:{[b.key]:x(key)},maps:{},flags:{}}));if(!target)continue
   let changed=false
   const maps=Object.fromEntries([...new Set([...entry.anchors.keys()].map(k=>(JSON.parse(k) as Extract<E,{op:'get'}>).map))].map(map=>[map,(at:E):E=>{
    const from={op:'get' as const,map,key:at},to=entry.anchors.get(text(from));if(to){changed=true;return to}return from
   }]))
   const rewritten=substC(target,{vars:{},maps,flags:{}})
   const simplify=(c:C,positive=true):C|boolean=>{
    if(entry.conditions.has(text(c)))return true
    const view=member(c);if(view&&known.has(text(view)))return true
    if(c.op==='and'||c.op==='or'){
     const xs=c.xs.map(q=>simplify(q,positive)),and=c.op==='and'
     if(xs.includes(!and))return !and
     const rest=xs.filter(v=>typeof v!=='boolean') as C[]
     return !rest.length?and:rest.length===1?rest[0]!:{op:c.op,xs:rest}
    }
    if(c.op==='not'){const v=simplify(c.x,!positive);return typeof v==='boolean'?!v:{op:'not',x:v}}
    // An upper bound is not an equality substitution. In a positive
    // comparison only, its scalar bound gives a sufficient guard. A strict
    // source bound u < U only needs U <= B to prove the strict target u < B.
    if(positive&&(c.op==='<'||c.op==='<=')){const upper=entry.upper.get(text(c.a));if(upper){c={...c,op:upper.strict?'<=':c.op,a:upper.bound};changed=true}}
    if(c.op==='='||c.op==='<'||c.op==='<='){
     if(text(c.a)===text(c.b))return c.op!=='<'
     if(c.a.op==='const'&&c.b.op==='const')return c.op==='='?c.a.value===c.b.value:c.op==='<'?c.a.value<c.b.value:c.a.value<=c.b.value
    }
    return c
   }
   const reduced=simplify(rewritten);if(!changed||reduced===false||typeof reduced!=='boolean'&&mentions(reduced))continue
   const guards=reduced===true?[]:parts(reduced)
   if(guards.some(c=>!['=','<','<='].includes(c.op)))continue
   const id=text([a.v,b.v,guards]);if(seen.has(id))continue;seen.add(id)
   out.push({positive:a.v,negative:b.v,carried:source.map,below:a.below,guards})
  }
 }
 return out
}
