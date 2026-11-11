// Structural proposals only: existing count declarations, no protocol names,
// operation values, trusted facts, or synthesized count declarations.
import {type C,type E,all,atMost,n,not,same,walkOnce,x} from './machine.ts'
import {type Count,type CountDecl,type MapRead,type Path,simpE} from '../kernel/kernel.ts'
import type {GuardBodyProposal,GuardCountProposal} from './count-guard-facts.ts'
const text=(t:unknown)=>JSON.stringify(t)
const has=(t:E|C,p:(v:any)=>boolean)=>{let yes=false;walkOnce(t,(v:any)=>{if(p(v))yes=true});return yes}
const keyed=(t:E|C,key:string)=>has(t,v=>v.op==='var'&&v.name===key)
const atoms=(c:C):C[]=>c.op==='and'?c.xs.flatMap(atoms):[c]
function negativeMap(c:C,map:string,negative=false):boolean{
 if(c.op==='not')return negativeMap(c.x,map,!negative)
 if(c.op==='and'||c.op==='or')return c.xs.some(v=>negativeMap(v,map,negative))
 return negative&&has(c,v=>v.op==='get'&&v.map===map)
}
function rowOf(read:MapRead,decl:CountDecl):E|undefined{
 const e=read[2];return decl.base?e.op==='add'&&e.a.op==='mul'&&e.a.k===decl.base?e.a.a:undefined:e
}
export function guardRegionProposals(rawCounts:Count[],reads:MapRead[],decls:CountDecl[],inputMaps:readonly string[],operation:C,path:Path=new Map()):{counts:GuardCountProposal[],bodies:GuardBodyProposal[]}{
 // Simplification guides discovery only. Returned body goals retain original expressions.
 const counts=rawCounts.map(c=>({...c,body:simpE(c.body,path,c.key)}))
 const out:GuardCountProposal[]=[],bodies:GuardBodyProposal[]=[],seen=new Set<string>()
 const add=(proposal:GuardCountProposal)=>{
  const when=[...proposal.when]
  // A packed read is tied to its certificate label only while its low part is in range.
  for(const [,name]of proposal.terms){
   const r=reads.find(r=>r[0]===name),d=r&&decls.find(d=>d.map===r[1]);if(!r||!d)return
   if(d.base){
    const key=r[2];if(key.op!=='add'||key.a.op!=='mul'||key.a.k!==d.base)return
    const bound:C={op:'<',a:key.b,b:n(d.base)}
    if(!when.some(c=>text(c)===text(bound)))when.push(bound)
   }
  }
  const p={...proposal,when},id=text([p.when,p.terms]);if(!seen.has(id)){seen.add(id);out.push(p)}
 }
 for(const post of counts){
  const read=reads.find(r=>r[0]===post.v),decl=read&&decls.find(d=>d.map===read[1])
  if(!read||!decl||!read[1].endsWith('#'))continue
  const preRead=reads.find(r=>r[1]===read[1].slice(0,-1)&&text(r[2])===text(read[2])),pre=preRead&&counts.find(c=>c.v===preRead[0]),row=rowOf(read,decl)
  if(!pre||!row)continue
  // A row which is unchanged is still a checked count fact, not a name test.
  if(text(pre.body)===text(post.body))for(const sign of [1,-1])add({name:`unchanged ${post.v} ${sign}`,kind:'row-frame',when:[operation],terms:[[sign,post.v],[-sign,pre.v]]})
  const comparisons:{op:'<',a:E,b:E}[]=[]
  walkOnce(post.body,(v:any)=>{if(v.op==='<'&&keyed(v.a,post.key)&&!keyed(v.b,post.key))comparisons.push(v)})
  for(const comparison of comparisons){
   const updates:Extract<E,{op:'if'}>[]=[]
   walkOnce(comparison.a,(v:any)=>{if(v.op==='if'&&!keyed(v.then,post.key)&&v.else?.op==='get'&&keyed(v.else.key,post.key))updates.push(v)})
   for(const update of updates){
    const parts=atoms(update.c),guard=parts.find(c=>keyed(c,post.key)&&has(c,v=>v.op==='get'&&inputMaps.includes(v.map))),active=parts.filter(c=>!keyed(c,post.key))
    if(!guard||update.else.op!=='get')continue
    const raisedMap=update.else.map,sources:E[]=[]
    walkOnce(update.then,(v:any)=>{if(v.op==='get'&&v.map===raisedMap&&!keyed(v.key,post.key))sources.push(v.key)})
    const source=sources[0];if(!source)continue
    const guardMap=inputMaps.find(map=>has(guard,v=>v.op==='get'&&v.map===map));if(!guardMap)continue
    const preComparisons:{op:'<',a:E,b:E}[]=[]
    walkOnce(pre.body,(v:any)=>{if(v.op==='<'&&has(v.a,z=>z.op==='get'&&z.map===raisedMap&&keyed(z.key,pre.key))&&!keyed(v.b,pre.key))preComparisons.push(v)})
    for(const restricted of counts){
     const rr=reads.find(r=>r[0]===restricted.v)
     if(!rr||rr[1].endsWith('#')||restricted.body.op!=='if'||!has(restricted.body,v=>v.op==='get'&&v.map===guardMap))continue
     const rd=decls.find(d=>d.map===rr[1]),restrictedRow=rd&&rowOf(rr,rd)
     // A global/input count has no row parameter. Do not pretend its read key identifies a row.
     if(!rd||!restrictedRow||!has(rd.body,v=>v.op==='var'&&(v.name===rd.j||v.name===(rd.lo??rd.j))))continue
     if(negativeMap(restricted.body.c,guardMap))add({name:`guard complement ${post.v} <= ${restricted.v}`,kind:'guard-complement-upper',when:[operation,all(...active),same(row,restrictedRow),atMost(comparison.b,update.then)],terms:[[1,post.v],[-1,restricted.v]]})
     else for(const bound of preComparisons)add({name:`guard intersection ${restricted.v} <= ${pre.v}`,kind:'guard-intersection-lower',when:[operation,all(...active),same(row,restrictedRow),atMost(update.then,bound.b)],terms:[[1,restricted.v],[-1,pre.v]]})
    }
    // On the complement of the member guard and away from every changed
    // key-free field read, both per-member predicates must be identical.
    const exclusions:C[]=[operation,{op:'<',a:x(post.key),b:post.below},not(guard),not(same(x(post.key),source))]
    walkOnce(pre.body,(v:any)=>{if(v.op==='get'&&!keyed(v.key,pre.key))exclusions.push(not(same(v.key,source)))})
    const unique=[...new Map(exclusions.map(c=>[text(c),c])).values()]
    bodies.push({name:`guard-excluded body ${post.v}`,kind:'excluded-body-frame',when:unique,pre:rawCounts.find(c=>c.v===pre.v)!.body,post:rawCounts.find(c=>c.v===post.v)!.body})
   }
  }
 }
 return {counts:out,bodies}
}
