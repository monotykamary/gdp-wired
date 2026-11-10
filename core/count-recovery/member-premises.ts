// Ordinary member-count witnesses and instances of existing universal premises.
// Nothing here asserts a scalar guard or a flag body. The machine checker
// reconstructs every added tuple from the original law/flag declaration.
import {type E,type Law,type Machine,walkOnce} from '../machine.ts'
import {type CountCert,type CountDecl,type CountInst,type Instances} from '../../kernel/kernel.ts'
import {countsForReads} from '../count-facts.ts'
import {fieldLawBridges} from '../count-focused.ts'
import {seedCountWitnessFlags} from '../count-witness-flags.ts'
import {memberInclusions,type MemberInclusion} from './member-inclusions.ts'

type Packet=Pick<CountCert,'reads'|'insts'>
export type MemberHint=MemberInclusion&{instance:CountInst,reads:CountCert['reads']}
export function memberPremiseState(source:unknown){
 const used=new Set<string>();walkOnce(source,(o:any)=>{for(const [key,value]of Object.entries(o)){used.add(key);if(typeof value==='string')used.add(value)}})
 return {used,witnesses:new Map<string,string>(),admissions:new Map<string,number>(),serial:0}
}
type State=ReturnType<typeof memberPremiseState>
const text=(value:unknown)=>JSON.stringify(value)
const vector=(q:Pick<CountInst,'terms'|'unit'|'below'>)=>text([q.unit,q.below,[...q.terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0])])
const nodeCount=(body:unknown)=>{let n=0;walkOnce(body,(o:any)=>{if(o.op)n++});return n}

// Put the strongest-shaped target bodies first; this is ordering, not a proof
// of implication. All entries remain ordinary CInsts under the existing cap.
export function memberHints(m:Machine,decls:CountDecl[],cert:Packet,more?:()=>boolean):MemberHint[]{
 const bodies=new Map((countsForReads(decls,cert.reads)??[]).map(c=>[c.v,nodeCount(c.body)])),available=new Map(cert.insts.map(q=>[vector(q),q]))
 return memberInclusions(m,decls,cert.reads,more).sort((a,b)=>(bodies.get(b.negative)??0)-(bodies.get(a.negative)??0)).flatMap(p=>{
  const instance=available.get(vector({unit:0,below:p.below,terms:[[1,p.positive],[-1,p.negative]]}))
  return instance?[{...p,instance,reads:cert.reads.filter(r=>r[0]===p.positive||r[0]===p.negative)}]:[]
 })
}
export function admitMemberWitnesses<T extends Packet>(m:Machine,decls:CountDecl[],cert:T,state:State,cap:number,more:()=>boolean=()=>true):{cert:T,hints:MemberHint[]}{
 const candidates=memberInclusions(m,decls,cert.reads,more)
 if(!candidates.length||cap<=0)return {cert,hints:[]}
 const bodies=new Map((countsForReads(decls,cert.reads)??[]).map(c=>[c.v,nodeCount(c.body)])),reads=new Map(cert.reads.map(r=>[r[0],r])),ds=new Map(decls.map(d=>[d.map,d]))
 candidates.sort((a,b)=>(bodies.get(b.negative)??0)-(bodies.get(a.negative)??0))
 walkOnce([decls,cert],(o:any)=>{if(o.op==='var')state.used.add(o.name)})
 for(const r of cert.reads)state.used.add(r[0]);for(const q of cert.insts)state.used.add(q.wit)
 const hints:MemberHint[]=[]
 for(const p of candidates){
  if(hints.length>=Math.min(cap,10)||!more())break
  const a=reads.get(p.positive)!,b=reads.get(p.negative)!,key=text([a.slice(1),b.slice(1),p.below,ds.get(a[1]),ds.get(b[1])])
  let wit=state.witnesses.get(key)
  if(!wit){do{wit=`member$${state.serial++}`}while(state.used.has(wit));state.used.add(wit);state.witnesses.set(key,wit)}
  hints.push({...p,reads:[a,b],instance:{wit,unit:0,below:p.below,terms:[[1,p.positive],[-1,p.negative]]}})
 }
 const seen=new Set<string>(),insts=[...hints.map(h=>h.instance),...cert.insts].filter(q=>{const k=vector(q);if(seen.has(k))return false;seen.add(k);return true}).slice(0,cap)
 return {cert:{...cert,insts,...('wits'in cert?{wits:insts.map(q=>q.wit)}:{})},hints:hints.filter(h=>insts.includes(h.instance))}
}

// An empty scalar-law proposal list seeds only member flags and preserves
// every previously learned tuple; model-driven field instantiation is separate.
export function instantiateMemberPremises(m:Machine,laws:Law[],at:Instances,decls:CountDecl[],hints:MemberHint[],state:State,cap:number,more:()=>boolean=()=>true){
 let next=at
 const added:{law:string,tuple:E[],kind:'flag'|'law'}[]=[]
 const add=(name:string,tuple:E[],kind:'flag'|'law')=>{
  if(!tuple.length||added.length>=cap||(state.admissions.get(name)??0)>=4||!more())return
  const old=next[name]??[],width=tuple.length
  if(old.length%width||Array.from({length:old.length/width},(_,i)=>text(old.slice(i*width,(i+1)*width))).includes(text(tuple)))return
  if(next===at)next={...at};next[name]=[...old,...tuple];state.admissions.set(name,(state.admissions.get(name)??0)+1);added.push({law:name,tuple,kind})
 }
 for(const hint of hints){
  if(added.length>=cap||!more())break
  // Supplying the declaration-backed reads preserves packed bounds and source
  // membership. seedCountWitnessFlags excludes recursive count-bearing flags.
  const packetReads=hint.reads
  if(packetReads.length!==2)continue
  const seeded=seedCountWitnessFlags(m,next,[{decls,cert:{reads:packetReads,insts:[hint.instance]}}],true,{carriedOnly:true})
  for(const [name,terms]of Object.entries(seeded))for(const term of terms.slice((next[name]??[]).length))add(name,[term],'flag')
  const maps=new Set<string>(),keys=new Map<string,E>()
  walkOnce(hint.guards,(o:any)=>{if(o.op==='get'){maps.add(o.map);keys.set(text(o.key),o.key)}})
  const sourceLaws=laws.filter(l=>{if(!l.forall||l.some?.length||(l.keys?.length??0)>1)return false;let counted=false,overlap=0;const seen=new Set<string>();walkOnce(l.holds,(o:any)=>{if(o.op==='get'){if(m.counts?.[o.map])counted=true;if(maps.has(o.map)&&!seen.has(o.map)){seen.add(o.map);overlap++}}});return !counted&&overlap>0}).sort((a,b)=>{const score=(l:Law)=>{const seen=new Set<string>();walkOnce(l.holds,(o:any)=>{if(o.op==='get'&&maps.has(o.map))seen.add(o.map)});return seen.size};return score(b)-score(a)})
  const terms=[...keys.values()].slice(0,4),bridged=fieldLawBridges(m,sourceLaws,next,terms,terms)
  for(const law of sourceLaws){const width=1+(law.keys?.length??0),old=next[law.name]??[],all=bridged[law.name]??[];for(let i=old.length;i<all.length;i+=width)add(law.name,all.slice(i,i+width),'law')}
 }
 return {at:next,added}
}
