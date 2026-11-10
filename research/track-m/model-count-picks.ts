// Untrusted C3 proposals from a sparse arithmetic model. Constants identify the
// model's members; prefer the existing witness term at that value so later
// models cannot evade the proposal merely by renaming a witnessed member.
import {type E,type Machine,evalE,x} from '../../core/machine.ts'
import {countsForReads,proposeCountPicks} from '../../core/count-facts.ts'
import {type CountCert,type CountDecl,plainOf} from '../../kernel/kernel.ts'
import {keyValue} from '../../kernel/prove.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>
export function modelCountPicks(m:Machine,decls:CountDecl[],cert:Proposal,w:Record<string,number>):[string,E[]][] {
 const pm=plainOf(m),names=new Set([...Object.keys(pm.maps??{}),...Object.keys(pm.fns??{}),...pm.inputMaps??[],...decls.map(d=>d.map)])
 const mm:Machine={...pm,fns:undefined,maps:{...pm.maps,...Object.fromEntries([...names].filter(n=>!(n in (pm.maps??{}))).map(n=>[n,0]))}}
 const maps:Record<string,Map<number,number>>=Object.fromEntries([...names].map(n=>[n,new Map<number,number>()]))
 for(const [cell,value] of Object.entries(w)){
  const br=cell.indexOf('['),map=cell.slice(0,br)
  if(br<0||!cell.endsWith(']')||!maps[map])continue
  const at=keyValue(cell,w);if(at!==undefined)maps[map]!.set(at,value)
 }
 const env=new Proxy(w,{get:(at,key:string)=>at[key]??0}),state={scalars:{},maps}
 const value=(e:E):number=>{try{return evalE(e,env,state,mm)}catch{return NaN}}
 const counts=countsForReads(decls,cert.reads);if(!counts)return []
 const proposed=proposeCountPicks(counts,value,{maxKeys:8})
 // Stored-row cardinalities and pre-state subsets are the premises that
 // constrain a bad transition. Do not spend the small proposal window first
 // on every post-state and request count merely because they occur first.
 const rank=(id:string):number=>{
  const r=cert.reads.find(r=>r[0]===id),c=counts.find(c=>c.v===id)
  if(!r||!c)return 4
  if(r[1].endsWith('#'))return 3
  const src=JSON.stringify(c.body),request=(m.inputMaps??[]).some(map=>src.includes(`"map":${JSON.stringify(map)}`))
  if(request)return 2
  const simple=c.body.op==='get'||c.body.op==='if'&&c.body.c.op==='='&&[c.body.c.a,c.body.c.b].some(e=>e.op==='get')
  return simple?0:1
 }
 return proposed.picks.sort((a,b)=>rank(a[0])-rank(b[0])).slice(0,6).map(([id,terms])=>{
  const witnesses=cert.insts.filter(i=>i.terms.some(t=>t[1]===id)).map(i=>i.wit)
  return [id,terms.map(term=>{const n=value(term),name=witnesses.find(name=>w[name]===n);return name?x(name):term})]
 })
}
