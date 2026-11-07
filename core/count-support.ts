// Private untrusted count-candidate scheduling. Every emitted tuple instantiates a whole
// original PRE law; every CountInst is reified by mcGoal and the final closed family is
// checked by checkCountedLaws. No coordinate projection is an equality premise.
import {type C, type E, type Law, type Machine, x} from './machine.ts'
import {linOfE, canon} from './solver.ts'
import {substC, substE, mcGoal, type CountDecl, type CountInst, type CountCert, type Goal, type MapRead, type Instances, countedObligations} from '../kernel/kernel.ts'
import {certFor} from './counts.ts'
import {wallAt} from '../kernel/prove.ts'
export class UnsupportedCountProposal extends Error {}
const json = (v: unknown) => JSON.stringify(v)
const sourceNames = (v: unknown, check?: () => void): Set<string> => {
  const out = new Set<string>()
  const visit = (v: unknown): void => {
    check?.()
    if (typeof v === 'string') { out.add(v); return }
    if (!v || typeof v !== 'object') return
    for (const [k, x] of Object.entries(v)) { out.add(k); visit(x) }
  }
  visit(v); return out
}
const names = (v: unknown, check?: () => void): Set<string> => {
  const out = new Set<string>()
  const visit = (v: unknown): void => { check?.(); if (!v || typeof v !== 'object') return; const o = v as Record<string, unknown>; if (o.op === 'var') out.add(String(o.name)); for (const x of Object.values(o)) visit(x) }
  visit(v); return out
}
const mentions = (v: unknown, n: string) => names(v).has(n)
const vars = (l: Law) => [l.forall, ...(l.keys ?? [])].filter((n): n is string => !!n)
const keyless = (d: CountDecl) => genuinelyKeyless(d)

// Only commutativity is used here. Keep the original full premise in the
// certificate; this key merely avoids spending source slots twice on it.
const premiseKey=(c:C):string=>c.op==='and'||c.op==='or'
 ? json([c.op,c.xs.map(premiseKey).sort((a,b)=>a.localeCompare(b))])
 : c.op==='not'?json(['not',premiseKey(c.x)])
 : c.op==='='?json(['=',[json(c.a),json(c.b)].sort((a,b)=>a.localeCompare(b))]):json(c)
const duplicateTerm=(law:Law|undefined,old:E[],tuple:E[]):boolean=>{
 if(!law||!tuple.length||old.length%tuple.length)return false
 const ns=vars(law),key=(ts:E[])=>premiseKey(substC(law.holds,{vars:Object.fromEntries(ns.map((n,i)=>[n,ts[i]!])),maps:{},flags:{}})),wanted=key(tuple)
 for(let i=0;i<old.length;i+=tuple.length)if(key(old.slice(i,i+tuple.length))===wanted)return true
 return false
}

// Instance changes matter to a count-read pool only when their law/flag can
// introduce a count read. Follow flag references to a fixed point, including
// reads under quantified flags; primitive flags must not invalidate the pool.
// A proposal cache depends on exact raw count-read spellings and definitions,
// not on which PRE tuple first exposed an already-present read. A hit never
// reuses a verdict: reservation and reification still inspect the current goal.
export function countPoolKey(goal:Goal,decls:CountDecl[]){
 const maps=new Set(decls.map(d=>d.map)),reads=readTuples(goal.hyps).filter(([map])=>maps.has(map)).map(read=>json(read)).sort()
 return json([decls,reads,goal.hyps.at(-1)])
}

export function countedInstanceSources(m:Machine,laws:Law[]):Set<string>{
 const analyze=(value:unknown)=>{
  let count=false;const flags=new Set<string>()
  const visit=(v:unknown):void=>{
   if(!v||typeof v!=='object')return
   const o=v as Record<string,unknown>
   if(o.op==='get'&&typeof o.map==='string'&&Object.hasOwn(m.counts??{},o.map))count=true
   if(o.op==='flag'&&typeof o.name==='string')flags.add(o.name)
   for(const x of Object.values(o))visit(x)
  }
  visit(value);return {count,flags}
 }
 const defs=Object.entries(m.step.flags??{}).map(([name,c])=>({name,...analyze(c)})),counted=new Set<string>()
 let changed=true
 while(changed){changed=false;for(const d of defs)if(!counted.has(d.name)&&(d.count||[...d.flags].some(f=>counted.has(f)))){counted.add(d.name);changed=true}}
 const out=new Set([...counted].map(f=>'?'+f))
 for(const l of laws){const d=analyze(l.holds);if(d.count||[...d.flags].some(f=>counted.has(f)))out.add(l.name)}
 return out
}

export function readTuples(value: unknown, more?: () => boolean): [string, E][] {
 const found = new Map<string, [string, E]>()
 const walk = (o: unknown): boolean => {
  if (more && !more()) return false
  if (!o || typeof o !== 'object') return true
  const p = o as Record<string, unknown>
  if (p.op === 'all') return true // No reads under an uninstantiated local binder.
  if (p.op === 'get') found.set(json([p.map, p.key]), [p.map as string, p.key as E])
  for (const v of Object.values(p)) if (!walk(v)) return false
  return true
 }
 walk(value); return [...found.values()]
}

export const keyId=(e:E)=>{const l=linOfE(e);return l?'lin:'+canon(l):json(e)}
const readKey = (map: string, key: E) => json([map, keyId(key)])
function bodyAt(d:CountDecl,r:MapRead):{body:E,below:E}|undefined{
 let vars:Record<string,E>
 if(d.base){if(r[2].op!=='add'||r[2].a.op!=='mul'||r[2].a.k!==d.base||!d.lo)return;vars={[d.j]:r[2].a.a,[d.lo]:r[2].b}}
 else vars={[d.j]:r[2]}
 vars[d.key]={op:'var',name:'$body-witness'} // canonical binder, never emitted into a goal
 return {body:substE(d.body,{vars,maps:{},flags:{}}),below:substE(d.below,{vars,maps:{},flags:{}})}
}
// A proposal-work ceiling, not additional proof/search time. The real wall is
// checked because pure JS enumeration does not advance the counted clock.
// Laws are immutable during one attempt. Only fully traversed patterns are cached;
// a hit is still metered, and a different meter never inherits another attempt's work.
const patternIndices=new WeakMap<()=>boolean,{laws:WeakMap<Law,[string,E][]>}>()
function lawReads(l:Law,more?:()=>boolean):[string,E][]{
 const cache=more&&patternIndices.get(more)?.laws,cached=cache?.get(l)
 if(cached)return more!()?cached:[]
 let complete=true
 const reads=readTuples(l.holds,more?()=>{const ok=more();if(!ok)complete=false;return ok}:undefined)
 if(complete)cache?.set(l,reads)
 return reads
}
export function candidateWork() {
  const state = {work: 0, limit: 65_536, exhausted: false, deadline: false, phases:[] as {phase:string,work:number}[], omittedPhases:0}
  const tick = () => {
    if (state.exhausted || state.deadline) return false
    if (performance.now() >= wallAt()) { state.deadline = true; return false }
    if (state.work >= state.limit) { state.exhausted = true; return false }
    state.work++; return true
  }
  const mark=(phase:string)=>{if(state.phases.length<128)state.phases=[...state.phases,{phase,work:state.work}];else state.omittedPhases++}
  patternIndices.set(tick,{laws:new WeakMap()})
  return {state,tick,mark}
}
export function grammarPool(goal:Goal,decls:CountDecl[],cap=1000,budget=candidateWork()){
 const more=budget.tick;budget.mark('pool:begin')
 const base=certFor(goal,decls,true,cap,more),byMap=new Map(decls.map(d=>[d.map,d])),byRead=new Map(base.reads.map(r=>[r[0],r])),insts=[...base.insts],wits=[...base.wits]
 const added:{instance:CountInst,reason:string,links?:unknown}[]=[],proposed:unknown[]=[]
 let omittedProvenance=0
 const semantic=(i:CountInst)=>json([i.terms.map(([k,r])=>[k,byRead.get(r)?.slice(1)]),i.unit,keyId(i.below)]),had=new Set(insts.map(semantic)),taken=names([goal,decls,insts]);let serial=insts.length
 const add=(i:CountInst,reason:string,links?:()=>unknown)=>{
  if(insts.length>=cap||!more())return
  const id=semantic(i);if(had.has(id))return
  const detail=proposed.length<128?links?.():undefined
  if(proposed.length<128)proposed.push({candidate:i,reason,links:detail,capped:false});else omittedProvenance++
  let wit:string;do{wit='w$'+serial++}while(taken.has(wit));taken.add(wit)
  const instance={...i,wit};insts.push(instance);wits.push(wit);had.add(id);added.push({instance,reason,...(detail===undefined?{}:{links:detail})})
 }
 budget.mark('pool:base')
 // No post-cap enumeration is needed: selected entries absent from this bounded
 // prefix can still be reinserted by reservePool from their exact prior definitions.
 // Narrow triples require an actual POST read; without one that pass cannot
 // add anything, so do not rescan the entire immutable hypothesis context.
 if(insts.length<cap&&base.reads.some(r=>r[1].endsWith('#'))&&more()){
  const narrow=certFor(goal,decls,false,cap,more)
  for(const i of narrow.insts){if(insts.length>=cap||!more())break;if(i.terms.length===3)add(i,'preserved narrow triple')}
 }
 budget.mark('pool:narrow')
 const checkedDefinitions=new Set<string>(),eligible:MapRead[]=[],at=new Map<string,{body:E,below:E,foot:Set<string>}>()
 if(insts.length<cap)for(const r of base.reads){
  if(!more())break;if(r[1].endsWith('#'))continue
  const d=byMap.get(r[1]);if(!d)continue
  if(!checkedDefinitions.has(r[1])){readTuples([d.body,d.below],more);if(budget.state.exhausted||budget.state.deadline)break;checkedDefinitions.add(r[1])}
  const b=bodyAt(d,r);if(!b)continue
  const foot=new Set(readTuples(b.body,more).map(([mp,k])=>json([mp,keyId(k)])))
  if(budget.state.exhausted||budget.state.deadline)break
  eligible.push(r);at.set(r[0],{...b,foot})
 }
 const fixed:MapRead[]=[],keyed:MapRead[]=[],classes=new Map<string,boolean>()
 for(const r of eligible){if(!more())break;let fixedClass=classes.get(r[1]);if(fixedClass===undefined){fixedClass=genuinelyKeyless(byMap.get(r[1])!);classes.set(r[1],fixedClass)};(fixedClass?fixed:keyed).push(r)}
 triples: for(const a of fixed)for(const d of fixed){
  if(insts.length>=cap||!more())break triples
  if(a===d)continue;const aa=at.get(a[0])!,dd=at.get(d[0])!
  if(!aa.foot.size||aa.foot.size>=dd.foot.size||![...aa.foot].every(x=>dd.foot.has(x)))continue
  for(const c of keyed){
   if(insts.length>=cap||!more())break triples
   const cc=at.get(c[0])!;if(keyId(aa.below)!==keyId(dd.below)||keyId(aa.below)!==keyId(cc.below))continue
   const bridge=[...dd.foot].filter(x=>!aa.foot.has(x)&&cc.foot.has(x));if(!bridge.length)continue
   add({wit:'',below:aa.below,terms:[[1,a[0]],[-1,d[0]],[-1,c[0]]],unit:0},'definition-linked PRE triple',()=>({a:[a[1],a[2]],d:[d[1],d[2]],c:[c[1],c[2]],aReads:[...aa.foot],dReads:[...dd.foot],cReads:[...cc.foot],bridge}))
  }
 }
 budget.mark('pool:end')
 return {full:{...base,insts,wits},base,added,proposed,oldEntriesPreserved:json(insts.slice(0,base.insts.length))===json(base.insts),freshWitnesses:new Set(insts.map(i=>i.wit)).size===insts.length,
  work:{...budget.state,capReached:insts.length>=cap,provenanceLimit:128,omittedProvenance,truncated:budget.state.exhausted||budget.state.deadline||insts.length>=cap||omittedProvenance>0}}
}
export function smallSelection(goal:Goal,decls:CountDecl[],full:ReturnType<typeof certFor>,ownKeys:E[],previous:Pick<CountCert,'reads'|'picks'>,budget=candidateWork()){
 const more=budget.tick;budget.mark('selection:begin')
 const rootReads=readTuples(goal.hyps.at(-1),more)
 const byRead=new Map(full.reads.map(r=>[r[0],r])),byMap=new Map(decls.map(d=>[d.map,d])),own=new Set([...ownKeys,...rootReads.map(([,key])=>key)].map(keyId)),direct=new Set(rootReads.map(([mp])=>mp))
 const insts=full.insts.filter(i=>{
  if(!more())return false
  if(i.unit!==0)return false
  if(i.terms.length===3)return true
  if(i.terms.length!==2||i.terms[0]![0]!==1||i.terms[1]![0]!==-1)return false
  const a=byRead.get(i.terms[0]![1])!,b=byRead.get(i.terms[1]![1])!;if(a[1].endsWith('#')||b[1].endsWith('#'))return false
  const da=byMap.get(a[1])!,db=byMap.get(b[1])!
  return keyless(da)&&keyless(db)&&(direct.has(a[1])||direct.has(b[1]))||!keyless(da)&&!keyless(db)&&keyId(a[2])===keyId(b[2])&&own.has(keyId(a[2]))
 })
 // Cover each concrete root key before another difference at an already covered
 // key or a keyless residual. No new instance, read, or witness is constructed.
 const keyed=new Map<string,CountInst[]>(),residual:CountInst[]=[]
 for(const i of insts){
  if(!more())break
  const rs=i.terms.map(([,id])=>byRead.get(id)!),key=rs[0]?.[2]
  const exact=i.terms.length===2&&key&&rs.every(r=>!keyless(byMap.get(r[1])!)&&keyId(r[2])===keyId(key)&&keyId(byMap.get(r[1])!.below)===keyId(i.below))&&own.has(keyId(key))
  if(exact){const id=keyId(key),rows=keyed.get(id)??[];rows.push(i);keyed.set(id,rows)}else residual.push(i)
 }
 // A definition-linked PRE overlap lifts an already-relevant difference. Keep
 // that difference and its existing lift ahead of mirror pairs, but never ahead
 // of first coverage at any distinct current root key. Match actual read IDs and
 // bounds; footprint links only rank candidates, never assert a source equality.
 const pairId=(i:Pick<CountInst,'below'|'unit'|'terms'>)=>json([keyId(i.below),i.unit,[...i.terms].sort((a,b)=>a[1].localeCompare(b[1]))])
 const pairs=new Map<string,CountInst>(),footprints=new Map<string,Set<string>|undefined>()
 for(const i of insts){if(!more())break;if(i.terms.length===2)pairs.set(pairId(i),i)}
 const footprint=(id:string,below:E)=>{
  const cacheKey=json([id,keyId(below)])
  if(footprints.has(cacheKey))return footprints.get(cacheKey)
  const r=byRead.get(id),d=r&&byMap.get(r[1]),b=d&&r&&!r[1].endsWith('#')?bodyAt(d,r):undefined
  const foot=b&&keyId(b.below)===keyId(below)?new Set(readTuples(b.body,more).map(([mp,k])=>readKey(mp,k))):undefined
  if(budget.state.exhausted||budget.state.deadline)return
  footprints.set(cacheKey,foot);return foot
 }
 const liftedPairs:CountInst[]=[],overlaps:CountInst[]=[]
 for(const i of residual){
  if(!more())break;if(i.terms.length!==3)continue
  for(let extra=0;extra<i.terms.length;extra++){
   if(!more())break
   const pair=pairs.get(pairId({...i,terms:i.terms.filter((_,j)=>j!==extra)})),r=byRead.get(i.terms[extra]![1])
   if(!pair||!r||keyless(byMap.get(r[1])!))continue
   if(!pair.terms.every(([,id])=>keyless(byMap.get(byRead.get(id)![1])!)))continue
   const a=footprint(pair.terms[0]![1],i.below),b=footprint(pair.terms[1]![1],i.below),c=footprint(r[0],i.below)
   if(!a||!b||!c)continue
   const [small,large]=a.size<b.size?[a,b]:[b,a]
   if(!small.size||small.size>=large.size||![...small].every(x=>large.has(x))||![...large].some(x=>!small.has(x)&&c.has(x)))continue
   liftedPairs.push(pair);overlaps.push(i);break
  }
 }
 const ordered:CountInst[]=[...[...keyed.values()].map(rows=>rows[0]!),...liftedPairs,...overlaps]
 for(let round=1;round<10;round++)for(const rows of keyed.values())if(rows[round])ordered.push(rows[round]!)
 const seen = new Set<string>(), unique = [...ordered,...residual].filter(i=>{const id=instId(i,full.reads);if(seen.has(id))return false;seen.add(id);return true}).slice(0,10)
 const used=new Set(unique.flatMap(i=>i.terms.map(([,r])=>r))),oldReads=new Map(previous.reads.map(r=>[r[0],r.slice(1)])),oldPicks=new Set((previous.picks??[]).map(p=>json([oldReads.get(p[0]),p[1]])))
 const seenPicks=new Set<string>(),picks:typeof full.picks=[]
 for(const p of full.picks){if(!more()||picks.length+unique.length>=10)break;const id=json([byRead.get(p[0])?.slice(1),p[1].map(keyId)]);if(!seenPicks.has(id)&&used.has(p[0])&&oldPicks.has(json([byRead.get(p[0])!.slice(1),p[1]]))){seenPicks.add(id);picks.push(p)}}
 budget.mark('selection:end')
 return {...full,insts:unique,picks}
}

export function genuinelyKeyless(d:Pick<CountDecl,'j'|'lo'|'base'|'body'|'below'>){
 if((d.base===undefined)!==(d.lo===undefined)||d.base!==undefined&&(!Number.isInteger(d.base)||d.base<=0))return false
 return [d.j,...(d.lo?[d.lo]:[])].every(n=>!mentions([d.body,d.below],n))
}
export function vacuousCountBinder(m:Machine,l:Law,more:()=>boolean=()=>true){
 const ns=[l.forall,...(l.keys??[])].filter((n):n is string=>!!n);if(ns.length!==1)return false
 const n=ns[0]!;let ignored=false
 const visit=(v:unknown):boolean=>{
  if(!more())return false
  if(Array.isArray(v))return v.every(visit)
  if(!v||typeof v!=='object')return true
  const o=v as Record<string,unknown>
  if(o.op==='var'&&o.name===n)return false
  if(o.op==='all'&&(o.key===n||(o.keys as unknown[]|undefined)?.includes(n)))return false
  if(o.op==='get'&&typeof o.map==='string'){const d=m.counts?.[o.map];if(d&&genuinelyKeyless(d)){if(mentions(o.key,n))ignored=true;return true}}
  return Object.values(o).every(visit)
 }
 return visit(l.holds)&&ignored
}
export function seedVacuousCounts(m:Machine,laws:Law[],initial:Instances,cap:number,more:()=>boolean=candidateWork().tick){
 const at={...initial},added:{law:string,tuple:E[]}[]=[]
 for(const l of laws){if(added.length>=cap||!more())break;if(!vacuousCountBinder(m,l,more)||(at[l.name]?.length??0)>=4)continue;const zero:E={op:'const',value:0};if((at[l.name]??[]).some(t=>json(t)===json(zero)))continue;at[l.name]=[...(at[l.name]??[]),zero];added.push({law:l.name,tuple:[zero]})}
 return {at,added}
}

type Direction='lower'|'upper'
export function postDirections(raw:C,decls:CountDecl[]){
 const post=new Set(decls.filter(d=>d.map.endsWith('#')).map(d=>d.map)),out=new Map<string,{map:string,key:E,directions:Set<Direction>,evidence:unknown[]}>()
 const record=(map:string,key:E,directions:Direction[],evidence:unknown)=>{const id=readKey(map,key),r=out.get(id)??{map,key,directions:new Set<Direction>(),evidence:[]};directions.forEach(d=>r.directions.add(d));r.evidence.push(evidence);out.set(id,r)}
 const coefficients=(e:E):Map<string,{map:string,key:E,k:number}>|undefined=>{
  if(e.op==='var'||e.op==='const')return new Map()
  if(e.op==='get')return post.has(e.map)?new Map([[readKey(e.map,e.key),{map:e.map,key:e.key,k:1}]]):new Map()
  if(e.op==='mul'){const a=coefficients(e.a);if(!a)return;return new Map([...a].map(([id,r])=>[id,{...r,k:r.k*e.k}]))}
  if(e.op==='add'){const a=coefficients(e.a),b=coefficients(e.b);if(!a||!b)return;for(const [id,r]of b)a.set(id,{...r,k:r.k+(a.get(id)?.k??0)});return a}
  return readTuples(e).some(([mp])=>post.has(mp))?undefined:new Map()
 }
 const walk=(c:C,positive:boolean,path:string):void=>{
  if(c.op==='not'){walk(c.x,!positive,path+'/not');return}
  if(c.op==='and'||c.op==='or'){c.xs.forEach((x,i)=>walk(x,positive,path+'/'+c.op+i));return}
  if(c.op==='all'){walk(c.c,positive,path+'/all');return}
  if(c.op==='flag')return
  const a=coefficients(c.a),b=coefficients(c.b)
  if(c.op==='='||!a||!b){for(const [mp,key]of readTuples(c))if(post.has(mp))record(mp,key,['lower','upper'],{path,op:c.op,positive,ambiguous:c.op==='='?'equality':'unsupported expression'});return}
  for(const [id,r]of b)a.set(id,{...r,k:(a.get(id)?.k??0)-r.k})
  for(const r of a.values()){const k=r.k*(positive?1:-1);record(r.map,r.key,k>0?['lower']:k<0?['upper']:['lower','upper'],{path,op:c.op,positive,coefficient:k,...(k===0?{ambiguous:'cancelled coefficient'}:{})})}
 }
 walk(raw,true,'raw');return [...out.values()].map(r=>({...r,directions:[...r.directions]}))
}
export function polaritySelection(goal:Goal,decls:CountDecl[],pool:ReturnType<typeof grammarPool>,budget=candidateWork(),sourceMaps?:ReadonlySet<string>){
 const full=pool.full,ordinary=certFor(goal,decls,false,10,budget.tick),rawNarrow=certFor(goal,decls,false,1000,budget.tick),narrow=json(rawNarrow.reads)===json(full.reads)?rawNarrow:{...full,insts:[]},byMap=new Map(decls.map(d=>[d.map,d])),byRead=new Map(full.reads.map(r=>[r[0],r])),directions=postDirections(goal.hyps.at(-1)!,decls)
 if(json(full.reads)!==json(narrow.reads))throw Error('selector read context changed')
 const candidates=new Map<string,{instance:CountCert['insts'][number],source:'wide'|'narrow'}>()
 for(const [source,rows]of [['wide',full.insts],['narrow',narrow.insts]] as const)for(const i of rows){if(!budget.tick())break;const id=instId(i,full.reads);if(!candidates.has(id))candidates.set(id,{instance:i,source})}
 const feet=(name:string)=>{const d=byMap.get(name)!;return new Set(readTuples(substE(d.body,{vars:{[d.key]:{op:'var',name:'$priority-witness'}},maps:{},flags:{}}),budget.tick).map(([mp,key])=>readKey(mp,key)))}
 const preferred:{id:string,instance:CountCert['insts'][number],source:string,rank:number,reasons:unknown[]}[]=[]
 for(const [id,{instance:i,source}]of candidates){if(!budget.tick())break;const reasons:unknown[]=[];let rank=99
  if(i.unit===-1&&i.terms.length===2&&i.terms.every(([k])=>k===1))for(const target of directions)if(target.directions.includes('upper')){
   const twin=i.terms.find(([,n])=>{const r=byRead.get(n)!;return r[1]===target.map.slice(0,-1)&&keyId(r[2])===keyId(target.key)}),other=i.terms.find(t=>t!==twin)
   if(twin&&other){const r=byRead.get(other[1])!;if(!r[1].endsWith('#')&&genuinelyKeyless(byMap.get(r[1])!)&&(!sourceMaps||sourceMaps.has(r[1]))){rank=1;reasons.push({direction:'upper',kind:'existing keyless PRE/target-twin meet',target,keyless:r.slice(1)})}}
  }
  if(i.unit!==0){if(rank<99)preferred.push({id,instance:i,source,rank,reasons});continue}
  for(const target of directions){const postTerm=i.terms.find(([,n])=>{const r=byRead.get(n);return r&&readKey(r[1],r[2])===readKey(target.map,target.key)});if(!postTerm)continue
   const others=i.terms.filter(t=>t!==postTerm)
   for(const direction of target.directions){const sign=direction==='lower'?-1:1;if(postTerm[0]!==sign)continue
    if(i.terms.length===2&&others[0]?.[0]===-sign){
     const r=byRead.get(others[0][1])!,before=byMap.get(r[1])!,after=byMap.get(target.map)!
     if(r[1]===target.map.slice(0,-1)&&(keyId(r[2])===keyId(target.key)||keyless(before)&&keyless(after))){rank=Math.min(rank,0);reasons.push({direction,kind:'same-key pre/post',target})}
     // A keyless source read whose exact cells occur in the POST definition is
     // a candidate copy bound. This only orders an existing counting instance;
     // the unchanged counting lemma still has to establish the relation.
     if(direction==='lower'&&!r[1].endsWith('#')&&keyless(before)){
      const source=feet(r[1]),destination=feet(target.map)
      if(source.size&&[...source].every(cell=>destination.has(cell))){rank=Math.min(rank,1);reasons.push({direction,kind:'definition-linked source/post',source:r.slice(1),target})}
     }
    }
    if(direction==='lower'&&i.terms.length===3){const plus=others.find(t=>t[0]===1),minus=others.find(t=>t[0]===-1);if(!plus||!minus)continue;const a=byRead.get(plus[1])!,d=byRead.get(minus[1])!,ad=byMap.get(a[1])!,dd=byMap.get(d[1])!;if(a[1].endsWith('#')||d[1].endsWith('#')||!keyless(ad)||!keyless(dd))continue
     const af=feet(a[1]),df=feet(d[1]),postMaps=new Set(readTuples(byMap.get(target.map)!.body).map(([mp])=>mp)),bridge=[...df].filter(x=>!af.has(x)&&postMaps.has((JSON.parse(x) as [string,string])[0]))
     if(af.size&&af.size<df.size&&[...af].every(x=>df.has(x))&&bridge.length){rank=Math.min(rank,1);reasons.push({direction,kind:'existing keyless-difference/post triple',a:a.slice(1),d:d.slice(1),target,bridge})}
    }
   }
  }
  if(rank<99)preferred.push({id,instance:i,source,rank,reasons})
 }
 preferred.sort((a,b)=>a.rank-b.rank)
 const selected:CountCert['insts']=[],seen=new Set<string>()
 const initialPriorityOnly=!!sourceMaps?.size&&preferred.length>0
 for(const i of [...preferred.map(p=>p.instance),...(initialPriorityOnly?[]:json(ordinary.reads)===json(full.reads)?ordinary.insts:full.insts.slice(0,10))]){const id=instId(i,full.reads);if(!seen.has(id)&&selected.length<10){seen.add(id);selected.push(candidates.get(id)?.instance??i)}}
 const pick={...full,insts:selected,wits:selected.map(i=>i.wit),picks:[] as NonNullable<CountCert['picks']>}
 return {pick,record:{directions,preferred:preferred.map(({instance,...p})=>({...p,instance,selected:seen.has(p.id),presentBeforeCap:true})),selected:selected.map(i=>instId(i,full.reads)),selectedCount:selected.length,initialPriorityOnly,activePoolCap:1000,newGrammar:false,work:budget.state}}
}

export const instId=(i:CountCert['insts'][number],rs:CountCert['reads'])=>{const rd=new Map(rs.map(r=>[r[0],[r[1],keyId(r[2])]]));return json([i.terms.map(([n,r])=>[n,rd.get(r)]).sort((a,b)=>json(a).localeCompare(json(b))),i.unit,keyId(i.below)])}
export const ids=(c:Pick<CountCert,'reads'|'insts'|'picks'>)=>{const rd=new Map(c.reads.map(r=>[r[0],[r[1],keyId(r[2])]]));return [...(c.picks??[]).map(p=>'p'+json([rd.get(p[0]),p[1].map(keyId)])),...c.insts.map(i=>'i'+instId(i,c.reads))]}

function requireValue<T>(x:T|undefined,message:string):T{if(x===undefined)throw new UnsupportedCountProposal('unresolved reservation: '+message);return x}
const reservationOpen=()=>{if(performance.now()>=wallAt())throw new UnsupportedCountProposal('reservation deadline')}
// A lexical free-variable walk, not sourceNames: local quantified binders and a
// declaration's formal parameters do not grant scope to a retained read key.
function reservationFree(value:unknown,bound:ReadonlySet<string>=new Set(),out=new Set<string>()):Set<string>{
 reservationOpen()
 if(!value||typeof value!=='object')return out
 if(Array.isArray(value)){for(const v of value)reservationFree(v,bound,out);return out}
 const o=value as Record<string,unknown>
 if(o.op==='var'){if(!bound.has(String(o.name)))out.add(String(o.name));return out}
 if(o.op==='all'){
  reservationFree(o.c,new Set([...bound,String(o.key),...((o.keys??[]) as string[])]),out)
  if(o.witness)reservationFree(o.witness,bound,out)
  return out
 }
 for(const v of Object.values(o))reservationFree(v,bound,out)
 return out
}
// Only the actual selected certificate's closure (<=10 entries, <=3 reads each),
// never the old optional pool. This validates before optional generation and is
// revalidated on insertion. No candidate fuel is created or consumed by replay.
export function reservationReadClosure(goal:Goal,decls:CountDecl[],previous:Pick<CountCert,'reads'|'insts'|'picks'>,previousDecls:CountDecl[],chosen:Set<string>,globals:Iterable<string>=[]){
 reservationOpen()
 if(chosen.size>10)throw new UnsupportedCountProposal('selected cap')
 if(!chosen.size)return {reads:[] as MapRead[],scope:new Set(globals)}
 const scope=new Set(globals),needed=new Set<string>(),oldIds=ids(previous),picked:NonNullable<CountCert['picks']>=[],insts:CountCert['insts']=[]
 for(const n of reservationFree(goal.hyps))scope.add(n)
 for(const d of decls)for(const n of reservationFree([d.body,d.below],new Set([d.j,d.key,...(d.lo?[d.lo]:[])])))scope.add(n)
 for(const key of chosen){
  reservationOpen()
  const at=oldIds.indexOf(key);if(at<0)throw new UnsupportedCountProposal('unresolved reservation: selected entry absent from previous pool')
  if(at<(previous.picks?.length??0)){const p=previous.picks![at]!;picked.push(p);needed.add(p[0])}
  else {const i=previous.insts[at-(previous.picks?.length??0)]!;if(i.terms.length>3)throw new UnsupportedCountProposal('reservation read closure cap');insts.push(i);for(const [,r]of i.terms)needed.add(r)}
 }
 if(needed.size>30)throw new UnsupportedCountProposal('reservation read closure cap')
 const reads:MapRead[]=[],byRead=new Map(previous.reads.map(r=>[r[0],r])),oldDecls=new Map(previousDecls.map(d=>[d.map,d])),nowDecls=new Map(decls.map(d=>[d.map,d])),oldWits=new Set(previous.insts.map(i=>i.wit)),selectedWits=new Set(insts.map(i=>i.wit))
 if(byRead.size!==previous.reads.length||oldDecls.size!==previousDecls.length||nowDecls.size!==decls.length)throw new UnsupportedCountProposal('reservation ambiguous read/definition')
 for(const id of needed){
  reservationOpen()
  const r=requireValue(byRead.get(id),'previous read '+id),od=requireValue(oldDecls.get(r[1]),'old definition '+r[1]),nd=requireValue(nowDecls.get(r[1]),'new definition '+r[1])
  if(json(od)!==json(nd)||insts.some(i=>i.terms.some(([,x])=>x===id)&&keyId(i.below)!==keyId(nd.below)))throw new UnsupportedCountProposal('unresolved reservation: changed bound/definition '+r[1])
  for(const n of reservationFree(r[2]))if(!scope.has(n)||oldWits.has(n)||decls.some(d=>d.key===n))throw new UnsupportedCountProposal('reservation read key out of scope/captured')
  reads.push(r)
 }
 for(const [,terms]of picked)for(const n of reservationFree(terms))if(oldWits.has(n)?!selectedWits.has(n):!scope.has(n))throw new UnsupportedCountProposal('reservation pick dependency/scope')
 for(const i of insts)if(reads.some(r=>r[0]===i.wit||names(r[2]).has(i.wit))||decls.some(d=>[d.j,d.lo,d.key].includes(i.wit)||names([d.body,d.below]).has(i.wit)))throw new UnsupportedCountProposal('reservation witness capture')
 reservationOpen()
 if(!mcGoal(goal.hyps,decls,{reads,insts,picks:picked}))throw new UnsupportedCountProposal('unresolved reservation: selected reification rejected')
 reservationOpen()
 return {reads,scope}
}
type WitnessLease={wit:string,identity:string}
// A cache spelling is not ownership. This state is created once per goal within
// one attempt; only validated actual selections can acquire its <=10 live leases.
export function reservationState(goal:Goal,rawSource:unknown,next:number){
 reservationOpen()
 return {next,inserted:new Map<string,string>(),ownership:{goal:json([goal.name,goal.hyps.at(-1)]),reserved:sourceNames(rawSource,reservationOpen),leases:new Map<string,WitnessLease>()}}
}
function reservationIdentity(i:CountInst,reads:MapRead[],decls:CountDecl[]):string{
 const rs=new Map(reads.map(r=>[r[0],r])),ds=new Map(decls.map(d=>[d.map,d]))
 return json([i.below,i.unit,i.terms.map(([co,id])=>{const r=requireValue(rs.get(id),'owned read');return [co,r[1],r[2],requireValue(ds.get(r[1]),'owned definition')]}).sort((a,b)=>json(a).localeCompare(json(b)))])
}
// Only free variable occurrences in HYPS are exempt. In particular map names,
// lexical binder declarations and all non-HYPS fields keep their ordinary names.
function reservationHypNames(value:unknown,out=new Set<string>()):Set<string>{
 reservationOpen()
 if(typeof value==='string'){out.add(value);return out}
 if(!value||typeof value!=='object')return out
 const o=value as Record<string,unknown>
 for(const [k,v]of Object.entries(o)){out.add(k);if(o.op==='var'&&k==='name')continue;reservationHypNames(v,out)}
 return out
}
export function reservePool(goal:Goal,decls:CountDecl[],pool:ReturnType<typeof grammarPool>,previous:Pick<CountCert,'reads'|'insts'|'picks'>,previousDecls:CountDecl[],chosen:Set<string>,state:{next:number,inserted:Map<string,string>,ownership?:ReturnType<typeof reservationState>['ownership']},cap=1000,reservation?:ReturnType<typeof reservationReadClosure>){
 const closure=reservationReadClosure(goal,decls,previous,previousDecls,chosen,reservation?.scope)
 const owner=state.ownership,leases=new Map<string,WitnessLease>()
 if(owner&&owner.goal!==json([goal.name,goal.hyps.at(-1)]))throw new UnsupportedCountProposal('reservation goal/attempt changed')
 const reads=[...pool.full.reads],fresh=sourceNames([goal,decls,pool.full],reservationOpen),preserved:MapRead[]=[];let serial=reads.length
 for(const r of closure.reads){
  reservationOpen()
  let current=reads.find(x=>x[1]===r[1]&&json(x[2])===json(r[2]))
  if(!current){let id:string;do{reservationOpen();id='r$'+serial++}while(fresh.has(id));fresh.add(id);current=[id,r[1],r[2]];reads.push(current)}
  if(names([goal.hyps,decls.map(d=>[d.body,d.below]),reads.map(r=>r[2])],reservationOpen).has(current[0])||decls.some(d=>[d.j,d.lo,d.key].includes(current![0])))throw new UnsupportedCountProposal('reservation read capture')
  preserved.push(current)
 }
 const full={...pool.full,reads,insts:[...pool.full.insts]},oldReads=new Map(previous.reads.map(r=>[r[0],r])),nowReads=new Map(full.reads.map(r=>[json([r[1],keyId(r[2])]),r])),oldDecls=new Map(previousDecls.map(d=>[d.map,d])),nowDecls=new Map(decls.map(d=>[d.map,d])),fullIds=ids(full),currentIds=new Set(fullIds),oldIds=ids(previous),pending:CountCert['insts']=[],rebindings:unknown[]=[]
 for(const r of preserved)nowReads.set(json([r[1],keyId(r[2])]),r)
 const renamed:{key:string,from:string,to:string}[]=[],quarantined:{index:number,instance:CountInst}[]=[]
 if(owner){
  // Regenerated representatives do not own selected binder names. Restore
  // those entries from the prior checked semantic selection below instead.
  full.insts=full.insts.filter((_,i)=>{const key=fullIds[(full.picks?.length??0)+i]!;if(!chosen.has(key))return true;currentIds.delete(key);return false})
  const protectedWits=new Map<string,string>(),protect=(key:string,wit:string)=>{const old=protectedWits.get(wit);if(old!==undefined&&old!==key)throw new UnsupportedCountProposal('reservation different witness owner');protectedWits.set(wit,key)}
  for(const [key,lease]of owner.leases)protect(key,lease.wit)
  for(const key of chosen)if(key.startsWith('i')){const at=oldIds.indexOf(key)-(previous.picks?.length??0);protect(key,requireValue(previous.insts[at],'selected owner').wit)}
  for(const wit of protectedWits.keys())fresh.add(wit)
  for(const name of owner.reserved)fresh.add(name)
  let dependencies:Set<string>|undefined
  // Regeneration may assign an old owner's spelling to a different cold entry.
  // Rename only that independent binder, never a live owner or a referenced term.
  for(const [at,i]of full.insts.entries()){
   reservationOpen();const owned=protectedWits.get(i.wit)
   if(owned===undefined)continue
   const key='i'+instId(i,full.reads);if(owned===key)continue
   dependencies??=sourceNames([full.reads,full.picks,full.insts.map(j=>j.below)],reservationOpen)
   if(dependencies.has(i.wit)){
    if(chosen.has(key)||owner.leases.has(key))throw new UnsupportedCountProposal('reservation cold witness dependency')
    // A dependent cold proposal cannot be renamed. Drop only that unselected
    // entry; live owners and every read/pick term retain their exact spelling.
    quarantined.push({index:at,instance:i});continue
   }
   let wit:string;do{reservationOpen();wit='w$'+state.next++}while(fresh.has(wit));fresh.add(wit)
   full.insts[at]={...i,wit};renamed.push({key,from:i.wit,to:wit})
  }
  if(quarantined.length){const removed=new Set(quarantined.map(q=>q.index));full.insts=full.insts.filter((_,i)=>!removed.has(i))}
 }
 for(const key of chosen){
  reservationOpen()
  if(!key.startsWith('i')){if(!currentIds.has(key))throw new UnsupportedCountProposal('unresolved reservation: selected pick missing');continue}
  const oi=oldIds.indexOf(key)-(previous.picks?.length??0),old=requireValue(previous.insts[oi],key+' not in previous actual pool')
  const terms=old.terms.map(([coefficient,id]):[number,string]=>{const r=requireValue(oldReads.get(id),'previous read '+id),next=requireValue(nowReads.get(json([r[1],keyId(r[2])])),'current exact map/key '+json(r.slice(1))),od=requireValue(oldDecls.get(r[1]),'old definition '+r[1]),nd=requireValue(nowDecls.get(r[1]),'new definition '+r[1]);if(json(od)!==json(nd)||keyId(od.below)!==keyId(old.below))throw new UnsupportedCountProposal('unresolved reservation: changed bound/definition '+r[1]);return [coefficient,next[0]]})
  const rebound={...old,terms};if('i'+instId(rebound,full.reads)!==key)throw new UnsupportedCountProposal('unresolved reservation: semantic change')
  rebindings.push({key,oldTerms:old.terms,newTerms:terms,allReadsAndDefinitionsPresent:true})
  let wit:string|undefined
  if(owner){
   const identity=reservationIdentity(old,previous.reads,decls),prior=owner.leases.get(key)
   if(prior&&(prior.identity!==identity||prior.wit!==old.wit))throw new UnsupportedCountProposal('reservation stale owned identity/witness')
   wit=prior?.wit??old.wit
   const forbidden=sourceNames([{...goal,hyps:undefined},decls,full.reads,[...previous.insts,...full.insts].map(i=>i.below)],reservationOpen)
   for(const n of reservationHypNames(goal.hyps))forbidden.add(n)
   if(owner.reserved.has(wit)||forbidden.has(wit))throw new UnsupportedCountProposal('reservation owned witness capture/source')
   if([...owner.leases,...leases].some(([id,l])=>id!==key&&l.wit===wit)||full.insts.some(i=>i.wit===wit&&'i'+instId(i,full.reads)!==key))throw new UnsupportedCountProposal('reservation different witness owner')
   if(reservationIdentity(rebound,full.reads,decls)!==identity)throw new UnsupportedCountProposal('reservation owned read/definition changed')
   leases.set(key,{wit,identity})
  }
  if(!currentIds.has(key))pending.push({...rebound,...(wit?{wit}:{})})
  else for(const [at,i]of full.insts.entries())if('i'+instId(i,full.reads)===key){
   if(wit&&i.wit!==wit&&sourceNames([goal,decls,full.reads,full.insts.map(j=>j.below),full.picks],reservationOpen).has(i.wit))throw new UnsupportedCountProposal('reservation renamed pool witness dependency')
   full.insts[at]=wit?{...rebound,wit}:{...i,terms}
  }
 }
 // Several raw aliases can denote one selected semantic entry. Align exactly
 // one FULL representative with the live view, not multiple copies of its lease.
 if(owner){const seen=new Set<string>();full.insts=full.insts.filter(i=>{const key='i'+instId(i,full.reads);if(!chosen.has(key))return true;if(seen.has(key))return false;seen.add(key);return true})}
 const taken=new Set([...full.insts.map(i=>i.wit),...sourceNames([goal,decls,full.reads],reservationOpen)]),inserted:CountCert['insts']=[]
 for(const old of pending){reservationOpen();const key='i'+instId(old,full.reads);let wit=leases.get(key)?.wit??state.inserted.get(key)
  if(!leases.has(key)&&(!wit||taken.has(wit))){do{reservationOpen();wit='w$'+state.next++}while(taken.has(wit))}
  wit=requireValue(wit,'allocated witness');state.inserted.set(key,wit);taken.add(wit)
  const i={...old,wit};if(!mcGoal(goal.hyps,decls,{reads:full.reads,insts:[i],picks:[]}))throw new UnsupportedCountProposal('unresolved reservation: CountInst reification rejected');inserted.push(i)
 }
 let need=Math.max(0,full.insts.length+inserted.length-cap);const evicted:CountCert['insts']=[],kept=[...full.insts],protectedNames=names((previous.picks??[]).filter((_,i)=>chosen.has(oldIds[i]!)))
 for(let i=kept.length-1;i>=0&&need;i--){reservationOpen();const v=kept[i]!;if(chosen.has('i'+instId(v,full.reads))||protectedNames.has(v.wit))continue;evicted.push(v);kept.splice(i,1);need--}
 if(need)throw new UnsupportedCountProposal('unresolved reservation: no unselected tail space')
 const insts=[...kept,...inserted],next={...full,insts,wits:insts.map(i=>i.wit)}
 reservationOpen()
 const selected=chosenView(next,chosen),selectedWits=new Set(selected.insts.map(i=>i.wit)),allWits=new Set([...insts,...previous.insts].map(i=>i.wit))
 for(const [,terms]of selected.picks)for(const n of names(terms))if(allWits.has(n)&&!selectedWits.has(n))throw new UnsupportedCountProposal('reservation pick dependency')
 if(!mcGoal(goal.hyps,decls,selected))throw new UnsupportedCountProposal('unresolved reservation: selected reification rejected')
 reservationOpen()
 if(insts.length>cap||new Set(next.wits).size!==insts.length||![...chosen].every(k=>ids(next).includes(k)))throw new UnsupportedCountProposal('reservation postcondition')
 if(owner){
  if(leases.size>10||!mcGoal(goal.hyps,decls,next))throw new UnsupportedCountProposal('reservation full alignment rejected')
  owner.leases=leases
  for(const key of state.inserted.keys())if(!chosen.has(key))state.inserted.delete(key)
 }
 return {full:next,record:{cap,chosen:chosen.size,renamed,quarantined:quarantined.map(q=>q.instance),baseSize:full.insts.length,finalSize:insts.length,preservedReads:preserved,rebindings,inserted:inserted.map(i=>({key:'i'+instId(i,full.reads),instance:i})),evicted:evicted.map(i=>({key:'i'+instId(i,full.reads),instance:i})),reified:inserted.length,unselectedTailOnly:true}}
}

const canonJSON=(v:unknown):string=>JSON.stringify(v,(_k,x)=>x&&typeof x==='object'&&!Array.isArray(x)?Object.fromEntries(Object.entries(x).sort(([a],[b])=>a.localeCompare(b))):x)

export function stableState(rawSource:unknown){return {reserved:sourceNames(rawSource),bySemantic:new Map<string,{wit:string,definition:string}>(),used:new Set<string>()}}
export function stableSelected(goal:Goal,decls:CountDecl[],view:Pick<CountCert,'reads'|'insts'|'picks'>,state:ReturnType<typeof stableState>,context:{lazyRoom:boolean,fullPoolUsed:boolean}){
 if(context.lazyRoom||context.fullPoolUsed||(view.picks?.length??0)>0)throw new UnsupportedCountProposal('stable selected view cannot cross full-pool model/pick view')
 if(new Set(view.reads.map(r=>r[0])).size!==view.reads.length)throw new UnsupportedCountProposal('duplicate/aliased count read identifiers')
 const needed=new Set([...view.insts.flatMap(i=>i.terms.map(([,r])=>r)),...(view.picks??[]).map(([r])=>r)]),projectedReads=view.reads.filter(([r])=>needed.has(r));if(projectedReads.length!==needed.size)throw new UnsupportedCountProposal('missing referenced count read')
 const reads=new Map(projectedReads.map(r=>[r[0],r])),ds=new Map(decls.map(d=>[d.map,d])),updates:unknown[]=[]
 const insts=view.insts.map(i=>{const semantic=instId(i,view.reads),definition=canonJSON({below:i.below,defs:i.terms.map(([coefficient,id])=>{const r=reads.get(id),d=r&&ds.get(r[1]);if(!r||!d)throw new UnsupportedCountProposal('unresolved stable read/definition');return {coefficient,map:r[1],definition:d}}).sort((a,b)=>canonJSON(a).localeCompare(canonJSON(b)))})
  let prior=state.bySemantic.get(semantic)
  if(prior){if(prior.definition!==definition)throw new UnsupportedCountProposal('unresolved stable definition/bound changed')}
  else {if(state.reserved.has(i.wit)||state.used.has(i.wit))throw new UnsupportedCountProposal('stable witness source collision/nonunique');prior={wit:i.wit,definition};state.bySemantic.set(semantic,prior);state.used.add(prior.wit)}
  if(state.reserved.has(prior.wit))throw new UnsupportedCountProposal('stable witness no longer fresh from source')
  updates.push({semantic,poolWitness:i.wit,selectedWitness:prior.wit,exactDefinitions:true,sourceFresh:true});return {...i,wit:prior.wit}
 })
 if(new Set(insts.map(i=>i.wit)).size!==insts.length)throw new UnsupportedCountProposal('nonunique stable selected witnesses')
 for(const i of insts)if(projectedReads.some(r=>r[0]===i.wit||names(r[2]).has(i.wit))||decls.some(d=>names([d.below,d.body]).has(i.wit)))throw new UnsupportedCountProposal('stable witness captured by count read/definition')
 const cert={...view,reads:projectedReads,insts,picks:view.picks??[],wits:insts.map(i=>i.wit)};if(!mcGoal(goal.hyps,decls,cert))throw new UnsupportedCountProposal('stable selected reification failed')
 return {cert,record:{stable:true,selectedCount:insts.length,updates,fullPoolModelUsed:false,picksUsed:false,sourceReadCount:view.reads.length,selectedReadCount:projectedReads.length,referencedReadIds:[...needed],omittedReadIds:view.reads.filter(([r])=>!needed.has(r)).map(([r])=>r)}}
}

export type Projection={binding:Record<string,E>,kind:'coordinate-projection',unmatchedFixed:{name:string,coefficient:number}[],sourceCoordinates:{name:string,coefficient:number}[],boundCoordinate:{name:string,coefficient:number}}
export function fixedStateCoordinates(m:Machine,key:E,binder:string){
 const a=linOfE(key);if(!a||!a[binder])return []
 return Object.entries(a).filter(([n,c])=>n!==binder&&n!=='1'&&c!==0&&Object.hasOwn(m.state,n)).map(([name,coefficient])=>({name,coefficient}))
}
export function projectBoundCoordinate(m:Machine,pattern:E,actual:E,binder:string):Projection|undefined{
 const a=linOfE(pattern),b=linOfE(actual),unmatchedFixed=fixedStateCoordinates(m,pattern,binder)
 if(!a||!b||!unmatchedFixed.length)return
 // A unique coefficient position is a coordinate; no fixed coordinate is rebound or equated.
 const coefficient=a[binder]!,bound=Object.entries(b).filter(([n,c])=>n!=='1'&&c===coefficient)
 if(bound.length!==1||Object.entries(a).some(([n,c])=>n!==binder&&n!=='1'&&c===coefficient))return
 const name=bound[0]![0]
 return {binding:{[binder]:{op:'var',name}},kind:'coordinate-projection',unmatchedFixed,sourceCoordinates:Object.entries(b).filter(([n,c])=>n!=='1'&&c!==0&&n!==name).map(([name,coefficient])=>({name,coefficient})),boundCoordinate:{name,coefficient}}
}

// Exact same-map key matcher for one affine remainder, anchored by an actual current witness.
export type RemainderMatch={binding:Record<string,E>,tail:string,remainder:E,polynomial:string,liveAnchors:string[]}
export function matchAffineRemainder(pattern:E,actual:E,binders:string[],live:Set<string>):RemainderMatch|undefined{
 const a=linOfE(pattern),b=linOfE(actual);if(!a||!b)return
 if([...Object.entries(a),...Object.entries(b)].some(([n,k])=>!Number.isInteger(k)||(n!=='1'&&k<0)))return
 const tails=binders.filter(n=>a[n]===1);if(tails.length!==1)return;const tail=tails[0]!,rest={...b},binding:Record<string,E>={}
 for(const [name,k]of Object.entries(a)){if(name==='1'||binders.includes(name))continue;if(rest[name]!==k)return;delete rest[name]}
 for(const name of binders){const k=a[name];if(name===tail||k===undefined)continue;if(k<=1)return;const fits=Object.entries(rest).filter(([n,v])=>n!=='1'&&v===k);if(fits.length!==1)return;const n=fits[0]![0];binding[name]={op:'var',name:n};delete rest[n]}
 const constant=(b['1']??0)-(a['1']??0);delete rest['1'];if(constant<0||Object.values(rest).some(k=>k<0||!Number.isInteger(k)))return
 const terms:E[]=Object.entries(rest).filter(([,k])=>k>0).sort(([a],[b])=>a.localeCompare(b)).map(([name,k]):E=>k===1?{op:'var',name}:{op:'mul',k,a:{op:'var',name}})
 if(constant)terms.push({op:'const',value:constant});binding[tail]=terms.length===0?{op:'const',value:0}:terms.slice(1).reduce<E>((a,b)=>({op:'add',a,b}),terms[0]!)
 const liveAnchors=Object.values(binding).flatMap(e=>e.op==='var'&&live.has(e.name)?[e.name]:[]);if(!liveAnchors.length)return
 const expanded=linOfE(substE(pattern,{vars:binding,maps:{},flags:{}}));if(!expanded||canon(expanded)!==canon(b))return
 return {binding,tail,remainder:binding[tail]!,polynomial:canon(expanded),liveAnchors}
}

type Binding=Record<string,E>
export function matchRead(pattern:E,term:E,binders:string[]):Binding|undefined {
 const out:Binding={}
 const go=(a:E|C,b:E|C):boolean=>{
  if(a.op==='var'&&binders.includes(a.name)){if(out[a.name])return json(out[a.name])===json(b);out[a.name]=b as E;return true}
  if(!b||a.op!==b.op)return false
  const target=b as unknown as Record<string,unknown>
  return Object.entries(a).every(([k,v])=>k==='op'||(v&&typeof v==='object'?(Array.isArray(v)?Array.isArray(target[k])&&v.length===(target[k] as unknown[]).length&&v.every((x,i)=>go(x,(target[k] as (C|E)[])[i]!)):go(v as E,target[k] as E)):v===target[k]))
 }
 if(go(pattern,term))return out
 const a=linOfE(pattern),b=linOfE(term);if(!a||!b||(a['1']??0)!==(b['1']??0))return
 const aa=Object.entries(a).filter(([n])=>n!=='1').sort((a,b)=>b[1]-a[1]),bb=Object.entries(b).filter(([n])=>n!=='1').sort((a,b)=>b[1]-a[1])
 if(aa.length!==bb.length||aa.some(([,c],i)=>c!==bb[i]![1]||(i>0&&c===aa[i-1]![1])))return
 const result:Binding={};for(const [i,[n]]of aa.entries()){const t=bb[i]![0];if(binders.includes(n))result[n]={op:'var',name:t};else if(n!==t)return}
 return result
}
type Source={kind:'own'|'write'|'read',map:string,key:E,id:string}
type Partial={binding:Binding,source:Source,pattern:[string,E],sameMap:boolean,projection?:Projection,remainder?:RemainderMatch}
export const projectionEligible=(m:Machine,l:Law,more?:()=>boolean)=>{const ns=vars(l);return ns.length===1&&lawReads(l,more).some(([,key])=>fixedStateCoordinates(m,key,ns[0]!).length>0)}
type Choice={law:string,tuple:E[],sources:Partial[],coherent:boolean,conflicts:string[],score:number,countLaw:boolean}
function emptyReadResult(at: Instances, cap: number) {
 return {at,added:[] as Choice[],proposals:[] as unknown[],mixed:[] as Choice[],summary:{livePairWork:0,livePairLimit:4096,livePairExhausted:false,anchors:[] as Source[],candidates:0,mixedAlternatives:0,admitted:0,perLawLimit:4,cap,rawFocusSupplied:false,selectedWitnesses:[] as string[],directCountMaps:[] as string[],writeVariables:[] as string[],allTuplesGenuinePRE:true,noMixedTupleAdmitted:true}}
}

function baseReadInstances(m:Machine,laws:Law[],own:Law,at:Instances,goal:Goal,cert:Pick<CountCert,'reads'|'insts'>,cap=64,rawNegatedPost?:C,more:()=>boolean=candidateWork().tick,mode:'all'|'live'|'cold'='all',pairBudget={work:0}){
 const boundedReads=(v:unknown)=>readTuples(v,more)
 if(cap<=0)return emptyReadResult(at,cap)
 const ks=vars(own),ownTerms=ks.map((n,i):E=>({op:'var',name:i===0?n+'#':n})),ownBody=substC(own.holds,{vars:Object.fromEntries(ks.map((n,i)=>[n,ownTerms[i]!])),maps:{},flags:{}})
 const ownReads=boundedReads(ownBody),ownMaps=new Set(ownReads.map(([mp])=>mp)),anchors:Source[]=[]
 for(const [i,[map,key]]of ownReads.entries())anchors.push({kind:'own',map,key,id:'own:'+i})
 for(const [map,w]of Object.entries(m.step.maps??{}))if(ownMaps.has(map)&&!('each'in w))anchors.push({kind:'write',map,key:w.key,id:'write:'+map})
 const actual:Source[]=boundedReads(goal.hyps).map(([map,key],i)=>({kind:'read',map,key,id:'read:'+i})),writes=anchors.filter(s=>s.kind==='write'),writeVars=new Set(writes.flatMap(s=>[...names(s.key)])),ownVars=names(ownTerms)
 const directCounts=new Set(boundedReads(rawNegatedPost).filter(([mp])=>!!m.counts?.[mp]).map(([mp])=>mp)),readMap=new Map(cert.reads.map(r=>[r[0],r[1]])),witScore=new Map(cert.insts.map(i=>[i.wit,i.terms.reduce((s,[k,r])=>s+(directCounts.has(readMap.get(r)??'')?(k<0?4:1):0),0)]))
 const candidates:Choice[]=[],mixed:Choice[]=[],selectedWitnesses=new Set(cert.insts.map(i=>i.wit));let livePairWork=0,livePairExhausted=false;const livePairLimit=4096
 const score=(tuple:E[],sources:Partial[])=>{const ns=names(tuple);return [...writeVars].filter(n=>ns.has(n)).length*100+[...ownVars].filter(n=>ns.has(n)).length*10+Math.max(0,...[...ns].map(n=>witScore.get(n)??0))+(sources.some(s=>s.source.kind==='own')&&sources.some(s=>s.source.kind==='write')?30:0)}
 sourceLaws: for(const l of laws){
  if(!more())break
  if(!l.forall||(at[l.name]?.length??0)/(1+(l.keys?.length??0))>=4)continue
  const ns=vars(l),oneKey=projectionEligible(m,l,more);if((ns.length<2&&!oneKey)||l===own)continue
  const pats=lawReads(l,more).filter(([,key])=>[...names(key)].filter(n=>ns.includes(n)).length>=(oneKey?1:2)),partials:Partial[]=[]
  for(const pattern of pats)for(const source of [...(mode==='live'?[]:anchors),...actual.filter(s=>s.map===pattern[0]&&(mode!=='live'||[...names(s.key)].some(n=>selectedWitnesses.has(n))))]){
   if(!more())break sourceLaws
   const sameMap=source.map===pattern[0];if(oneKey&&!sameMap)continue
   const binding=matchRead(pattern[1],source.key,ns)
   const remainder=!binding&&sameMap&&source.kind==='read'?matchAffineRemainder(pattern[1],source.key,ns,selectedWitnesses):undefined
   if(binding)partials.push({binding,source,pattern,sameMap})
   else if(remainder)partials.push({binding:remainder.binding,source,pattern,sameMap,remainder})
   else if(oneKey&&sameMap){const projection=projectBoundCoordinate(m,pattern[1],source.key,ns[0]!);if(projection)partials.push({binding:projection.binding,source,pattern,sameMap,projection})}
  }
  const seen=new Set<string>(),countLaw=lawReads(l,more).some(([mp])=>!!m.counts?.[mp])
  const add=(binding:Binding,sources:Partial[],conflicts:string[])=>{if(!ns.every(n=>binding[n]))return;const tuple=ns.map(n=>binding[n]!),id=json([conflicts.length?'mixed':'coherent',tuple]);if(seen.has(id))return;seen.add(id);const s=score(tuple,sources);const joined=!conflicts.length&&sources.length===2&&sources.every(p=>p.source.kind==='read'&&p.sameMap&&!p.projection)&&Object.entries(sources[0]!.binding).some(([slot,e])=>e.op==='var'&&selectedWitnesses.has(e.name)&&json(e)===json(sources[1]!.binding[slot]));if(mode==='live'&&(!joined||sources[0]!.pattern[0]===sources[1]!.pattern[0]))return;if(s<100&&!joined&&!sources.some(x=>x.source.kind==='own')&&!sources.some(x=>x.remainder)&&!(oneKey&&tuple.some(t=>t.op==='var'&&selectedWitnesses.has(t.name))&&sources.some(p=>p.source.kind==='read'&&p.sameMap)))return;const c:Choice={law:l.name,tuple,sources,coherent:!conflicts.length,conflicts,score:s,countLaw};(conflicts.length?mixed:candidates).push(c)}
  for(const p of partials){if(!more())break sourceLaws;add(p.binding,[p],[])}
  if(mode!=='live')for(let i=0;i<partials.length;i++)for(let j=i+1;j<partials.length;j++){
   if(!more())break sourceLaws
   const a=partials[i]!,b=partials[j]!;if(a.source.kind==='read'&&b.source.kind==='read')continue
   const overlap=Object.keys(a.binding).filter(n=>b.binding[n]&&json(a.binding[n])!==json(b.binding[n]))
   if(!overlap.length)add({...a.binding,...b.binding},[a,b],[])
   else {add({...a.binding,...b.binding},[a,b],overlap);add({...b.binding,...a.binding},[a,b],overlap)}
  }
  // Index read/read joins by the SAME bound slot and CURRENT selected witness before pairing.
  const buckets=new Map<string,Partial[]>(),indices=new Map(partials.map((p,i)=>[p,i]))
  for(const p of partials)if(p.source.kind==='read'&&p.sameMap&&!p.projection)for(const [slot,e]of Object.entries(p.binding))if(e.op==='var'&&selectedWitnesses.has(e.name)){const id=json([slot,e.name]),bucket=buckets.get(id)??[];bucket.push(p);buckets.set(id,bucket)}
  const paired=new Set<string>()
  livePairs: for(const bucket of buckets.values())for(let i=0;i<bucket.length;i++)for(let j=i+1;j<bucket.length;j++){
   if(!more())break sourceLaws
   const a=bucket[i]!,b=bucket[j]!,sameMap=a.pattern[0]===b.pattern[0]
   if(mode==='live'&&sameMap||mode==='cold'&&!sameMap)continue
   if(pairBudget.work>=livePairLimit){livePairExhausted=true;break livePairs}
   const id=json([indices.get(a),indices.get(b)]);if(paired.has(id))continue;paired.add(id);livePairWork++;pairBudget.work++
   const overlap=Object.keys(a.binding).filter(n=>b.binding[n]&&json(a.binding[n])!==json(b.binding[n]));if(overlap.length)continue
   add({...a.binding,...b.binding},[a,b],[])
  }
 }
 const out:Instances={...at},added:Choice[]=[]
 const append=(c:Choice)=>{if(added.length>=cap)return;const n=c.tuple.length,had=out[c.law]??[];if(!n||had.length%n||had.length/n>=4)return;for(let i=0;i<had.length;i+=n)if(json(had.slice(i,i+n))===json(c.tuple))return;out[c.law]=[...had,...c.tuple];added.push(c)}
 if(mode!=='live'&&own.forall)append({law:own.name,tuple:ownTerms,sources:[],coherent:true,conflicts:[],score:Infinity,countLaw:false})
 const existed=(c:Choice)=>{const old=at[c.law]??[],n=c.tuple.length;for(let i=0;i<old.length;i+=n)if(json(old.slice(i,i+n))===json(c.tuple))return true;return false}
 const witnessComplete=(c:Choice)=>c.coherent&&(c.sources.some(p=>p.source.kind==='read'&&p.sameMap&&!p.projection&&Object.keys(p.binding).length===c.tuple.length&&[...names(p.source.key)].some(n=>selectedWitnesses.has(n)))||c.sources.length===2&&c.sources.every(p=>p.source.kind==='read'&&p.sameMap&&!p.projection)&&Object.entries(c.sources[0]!.binding).some(([slot,e])=>e.op==='var'&&selectedWitnesses.has(e.name)&&json(e)===json(c.sources[1]!.binding[slot])))
 const ownAnchor=(c:Choice)=>c.coherent&&c.sources.some(p=>p.source.kind==='own')
 const compare=(a:Choice,b:Choice)=>Number(witnessComplete(b))-Number(witnessComplete(a))||Number(ownAnchor(b))-Number(ownAnchor(a))||b.score-a.score
 // Deduplicate against existing instances BEFORE the unchanged per-law4/global64 limits.
 // Count-read laws remain first; complete current witness/read bindings, then coherent own anchors.

 const byLaw=new Map<string,Choice[]>()
 for(const c of candidates)if(c.law!==own.name&&!existed(c)){const row=byLaw.get(c.law)??[];row.push(c);byLaw.set(c.law,row)}
 const queues=[...byLaw.values()].map(q=>q.sort(compare).slice(0,4)).sort((a,b)=>Number(b[0]!.countLaw)-Number(a[0]!.countLaw))
 for(const tier of [true,false])for(let round=0;round<4&&added.length<cap;round++)for(const q of queues)if(q[0]!.countLaw===tier&&q[round])append(q[round]!)
 const identity=(c:Choice)=>json([c.law,c.tuple]),selectedIds=new Set(added.map(identity)),limited=new Set(queues.flat().map(identity))
 const proposals=candidates.slice(0,128).map(c=>({law:c.law,tuple:c.tuple,provenance:c.sources.map(p=>({kind:p.projection?'coordinate-projection':p.remainder?'affine-remainder-exact':'exact-read-match',pattern:p.pattern,source:p.source,binding:p.binding,...(p.projection?{unmatchedFixed:p.projection.unmatchedFixed,sourceCoordinates:p.projection.sourceCoordinates}: {}),...(p.remainder?{remainder:p.remainder}: {})})),priority:[Number(witnessComplete(c)),Number(ownAnchor(c)),c.score],score:c.score,status:existed(c)?'already-existing':selectedIds.has(identity(c))?'admitted':limited.has(identity(c))?'global-cap-excluded':'per-law-cap-excluded'}))
 return {proposals,at:added.length?out:at,added,mixed:mixed.sort((a,b)=>b.score-a.score).slice(0,128),summary:{provenanceLimit:128,omittedProvenance:Math.max(0,candidates.length-128),livePairWork,livePairLimit,livePairExhausted,anchors,candidates:candidates.length,mixedAlternatives:mixed.length,admitted:added.length,perLawLimit:4,cap,rawFocusSupplied:rawNegatedPost!==undefined,selectedWitnesses:[...selectedWitnesses],directCountMaps:[...directCounts],writeVariables:[...writeVars],allTuplesGenuinePRE:true,noMixedTupleAdmitted:true}}
}

function presentPremises(hyps:C[],more:()=>boolean){const out=new Set<string>();for(const h of hyps){if(!more())break;out.add(json(h))}return out}
const hasVar=(v:unknown,n:string):boolean=>!!v&&typeof v==='object'&&((v as E).op==='var'&&(v as {name:string}).name===n||Object.values(v).some(x=>hasVar(x,n)))
// Recognize only range predicates on a primitive cell at the bare key. An implication's
// guard is inspected structurally, NEVER removed from the law used by the kernel.
export function bareRangeMap(m:Machine,l:Law,more:()=>boolean=candidateWork().tick):string|undefined {
 if(!l.forall||l.keys?.length||l.some?.length)return
 const n=l.forall,primitive=(mp:string)=>Object.hasOwn(m.maps??{},mp)&&!Object.hasOwn(m.counts??{},mp)
 const bound=(e:E):boolean=>e.op==='const'?Number.isSafeInteger(e.value)&&e.value>=0:e.op==='var'?m.params.includes(e.name):e.op==='add'||e.op==='sub'||e.op==='min'||e.op==='max'?bound(e.a)&&bound(e.b):e.op==='mul'?Number.isSafeInteger(e.k)&&e.k>=0&&bound(e.a):false
 const range=(c:C):string|undefined=>{
  if(!more())return
  if(c.op==='or'&&c.xs.length===2){const neg=c.xs.filter(x=>x.op==='not'),rest=c.xs.filter(x=>x.op!=='not');if(neg.length===1&&rest.length===1)return range(rest[0]!)}
  if(c.op==='and'||c.op==='or'){const maps=c.xs.map(range);return maps.length&&maps[0]&&maps.every(mp=>mp===maps[0])?maps[0]:undefined}
  if(c.op!=='<'&&c.op!=='<='&&c.op!=='=')return
  const cell=(e:E)=>e.op==='get'&&primitive(e.map)&&e.key.op==='var'&&e.key.name===n?e.map:undefined
  return cell(c.a)&&bound(c.b)?cell(c.a):cell(c.b)&&bound(c.a)?cell(c.b):undefined
 }
 return range(l.holds)
}
export function seededBoundMaps(m:Machine,laws:Law[],seeds:{law:string,tuple:E[]}[]){
 const maps=new Set<string>()
 for(const seed of seeds){const law=laws.find(l=>l.name===seed.law);if(!law||!vacuousCountBinder(m,law))throw Error('target source must be an actually seeded vacuous PRE law');for(const [map]of readTuples(law.holds)){const d=m.counts?.[map];if(d&&genuinelyKeyless(d))maps.add(map)}}
 return maps
}
export function targetKeylessMeets(m:Machine,decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,rawPost:C|undefined,sourceMaps:ReadonlySet<string>,more:()=>boolean=candidateWork().tick){
 const directions=rawPost?postDirections(rawPost,decls).filter(d=>d.directions.includes('upper')):[],reads=new Map(cert.reads.map(r=>[r[0],r]))
 return cert.insts.filter(i=>more()&&i.unit===-1&&i.terms.length===2&&i.terms.every(([k])=>k===1)&&i.terms.some(([,id])=>{const r=reads.get(id);return r&&directions.some(d=>r[1]===d.map.slice(0,-1)&&keyId(r[2])===keyId(d.key)&&i.terms.some(([,other])=>{const s=reads.get(other),def=s&&decls.find(d=>d.map===s[1]);return other!==id&&!!def&&sourceMaps.has(def.map)&&genuinelyKeyless(def)}))}))
}
export function targetKindMatches(m:Machine,laws:Law[],decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,rawPost:C|undefined,sourceMaps:ReadonlySet<string>,more:()=>boolean=candidateWork().tick){
 const boundedReads=(value:unknown)=>readTuples(value,more)
 const out:{law:string,tuple:E[],map:string,witness:string,body:C,premise:C}[]=[],seen=new Set<string>()
 for(const i of targetKeylessMeets(m,decls,cert,rawPost,sourceMaps,more)){
  if(!more())return out
  // Reuse the kernel's exact CountInst substitution, not a recreated packed-key formula.
  const body=mcGoal([],decls,{reads:cert.reads,insts:[i],picks:[]})?.hyps.at(-1);if(!body)throw Error('selected target meet cannot reify')
  for(const [map,key]of boundedReads(body)){
   if(!more())return out
   if(!hasVar(key,i.wit))continue
   for(const l of laws){if(!more())return out;if(bareRangeMap(m,l,more)!==map)continue;const id=json([l.name,key]);if(seen.has(id))continue;seen.add(id);out.push({law:l.name,tuple:[key],map,witness:i.wit,body,premise:substC(l.holds,{vars:{[l.forall!]:key},maps:{},flags:{}})})}
  }
 }
 return out
}

// Root reads propose arguments to quantified flags. Temporary bindings of fixed
// globals select the argument only; the emitted flag body retains those globals.
export function rootFlagMatches(m:Machine,own:Law,more:()=>boolean=candidateWork().tick){
 const ns=vars(own),binding=Object.fromEntries(ns.map((n,i)=>[n,x(i===0?n+'#':n)])),root=substC(own.holds,{vars:binding,maps:{},flags:{}}),rootReads=readTuples(root,more),live=names(root),globals=new Set([...m.params,...m.inputs,...Object.keys(m.state)])
 const out:{law:string,tuple:E[],map:string,pattern:E,actual:E,matchingOnly:Record<string,E>,premise:C}[]=[],seen=new Set<string>()
 for(const [name,q]of Object.entries(m.step.flags??{})){
  if(!more())return out;if(q.op!=='all'||q.keys?.length)continue
  for(const [map,pattern]of readTuples(q.c,more))for(const [actualMap,actual]of rootReads){
   if(!more())return out;if(map!==actualMap)continue
   const fixed=[...names(pattern)].filter(n=>n!==q.key&&globals.has(n)),binders=[q.key,...fixed]
   const matching=matchRead(pattern,actual,binders)??matchAffineRemainder(pattern,actual,binders,live)?.binding,term=matching?.[q.key]
   if(!matching||!term||keyId(substE(pattern,{vars:matching,maps:{},flags:{}}))!==keyId(actual))continue
   const law='?'+name,id=json([law,keyId(term)]);if(seen.has(id))continue;seen.add(id)
   const originalBody=substC(q.c,{vars:{[q.key]:term},maps:{},flags:{}})
   out.push({law,tuple:[term],map,pattern,actual,matchingOnly:matching,premise:{op:'or',xs:[{op:'=',a:x(law),b:{op:'const',value:0}},originalBody]}})
  }
 }
 return out
}

export function targetFlagMatches(m:Machine,decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,rawPost:C|undefined,sourceMaps:ReadonlySet<string>,more:()=>boolean=candidateWork().tick){
 const boundedReads=(value:unknown)=>readTuples(value,more)
 const out:{law:string,tuple:E[],witness:string,map:string,pattern:E,actual:E,matchingOnly:Record<string,E>,fixed:{name:string,coefficient:number}[],domain:C,premise:C}[]=[],seen=new Set<string>()
 for(const i of targetKeylessMeets(m,decls,cert,rawPost,sourceMaps,more)){
  if(!more())return out
  const body=mcGoal([],decls,{reads:cert.reads,insts:[i],picks:[]})?.hyps.at(-1);if(!body)throw Error('target flag source cannot reify')
  for(const [name,q]of Object.entries(m.step.flags??{})){
   if(!more())return out
   if(q.op!=='all'||q.keys?.length)continue
   for(const [map,pattern]of boundedReads(q.c)){
    if(!more())return out
    const fixed=fixedStateCoordinates(m,pattern,q.key);if(!fixed.length)continue
    for(const [actualMap,actual]of boundedReads(body)){
     if(!more())return out
     if(map!==actualMap)continue
     const match=matchAffineRemainder(pattern,actual,[q.key,...fixed.map(p=>p.name)],new Set([i.wit])),term=match?.binding[q.key];if(!match||!term)continue
     const law='?'+name,id=json([law,term]);if(seen.has(id))continue;seen.add(id)
     // The kernel closes this instance with ?flag=0 OR its ORIGINAL body, not match.binding's fixed-state substitutions.
     const originalBody=substC(q.c,{vars:{[q.key]:term},maps:{},flags:{}})
     out.push({law,tuple:[term],witness:i.wit,map,pattern,actual,matchingOnly:match.binding,fixed,domain:{op:'<=',a:x(law),b:{op:'const',value:1}},premise:{op:'or',xs:[{op:'=',a:x(law),b:{op:'const',value:0}},originalBody]}})
    }
   }
  }
 }
 return out
}

export function targetReadMatches(m:Machine,laws:Law[],decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,rawPost:C|undefined,sourceMaps:ReadonlySet<string>,more:()=>boolean=candidateWork().tick){
 const boundedReads=(value:unknown)=>readTuples(value,more)
 const out:{law:string,tuple:E[],witness:string,map:string,pattern:E,actual:E,premise:C}[]=[],seen=new Set<string>()
 for(const i of targetKeylessMeets(m,decls,cert,rawPost,sourceMaps,more)){
  if(!more())return out
  const body=mcGoal([],decls,{reads:cert.reads,insts:[i],picks:[]})?.hyps.at(-1);if(!body)throw Error('priority target cannot reify')
  for(const [map,actual]of boundedReads(body)){
   if(!more())return out
   if(!hasVar(actual,i.wit)||Object.hasOwn(m.counts??{},map))continue
   for(const l of laws){
    if(!more())return out
    const ns=[l.forall,...(l.keys??[])].filter((x):x is string=>!!x);if(ns.length<2||lawReads(l,more).some(([mp])=>Object.hasOwn(m.counts??{},mp)))continue
    for(const [patternMap,pattern]of lawReads(l,more)){
     if(!more())return out
     if(map!==patternMap)continue
     const binding=matchRead(pattern,actual,ns);if(!binding||!ns.every(n=>binding[n])||!Object.values(binding).some(e=>hasVar(e,i.wit)))continue
     if(keyId(substE(pattern,{vars:binding,maps:{},flags:{}}))!==keyId(actual))throw Error('complete current read did not reconstruct')
     const tuple=ns.map(n=>binding[n]!),id=json([l.name,tuple]);if(seen.has(id))continue;seen.add(id)
     out.push({law:l.name,tuple,witness:i.wit,map,pattern,actual,premise:substC(l.holds,{vars:binding,maps:{},flags:{}})})
    }
   }
  }
 }
 return out
}

// Actual free PRE reads reachable from the target's updates. Quantified bodies
// and bulk-map binders are not free sources; disconnected flag definitions are
// not traversed. This proposes terms only, never a transition or packed equality.
export function transitionReads(m:Machine,own:Law,more:()=>boolean=candidateWork().tick){
 const out:{read:[string,E],path:string[],freeNames:string[]}[]=[],seen=new Set<string>(),flags=new Set<string>()
 const globals=new Set([...m.params,...m.inputs,...Object.keys(m.state)]),variables=names(own.holds),maps=new Set(readTuples(own.holds,more).map(([map])=>map)),expanded=new Set<string>()
 for(const map of maps){
  if(!more())return out
  const d=m.counts?.[map];if(!d||expanded.has(map))continue;expanded.add(map)
  for(const [source]of readTuples(d.body,more))maps.add(source)
 }
 const visit=(value:unknown,path:string[]):void=>{
  if(!more()||!value||typeof value!=='object')return
  if(Array.isArray(value)){value.forEach((v,i)=>visit(v,[...path,String(i)]));return}
  const o=value as Record<string,unknown>
  if(o.op==='all')return
  if(o.op==='flag'&&typeof o.name==='string'&&!flags.has(o.name)){
   flags.add(o.name);visit(m.step.flags?.[o.name],['step','flags',o.name])
  }
  if(o.op==='get'&&typeof o.map==='string'&&o.key){
   const key=o.key as E,freeNames=[...names(key)],id=readKey(o.map,key)
   if(freeNames.every(n=>globals.has(n))&&!seen.has(id)){seen.add(id);out.push({read:[o.map,key],path,freeNames})}
  }
  for(const [key,v]of Object.entries(o))if(v&&typeof v==='object')visit(v,[...path,key])
 }
 for(const [name,value]of Object.entries(m.step.state??{}))if(variables.has(name))visit(value,['step','state',name])
 for(const [map,update]of Object.entries(m.step.maps??{}))if(maps.has(map)&&!('each'in update))visit(update,['step','maps',map])
 return out
}
function primitiveReadKinds(m:Machine,laws:Law[],values:unknown,more:()=>boolean){
 const out:{law:string,tuple:E[],map:string,premise:C}[]=[],seen=new Set<string>(),byMap=new Map<string,Law[]>()
 for(const law of laws){if(!more())return out;const map=bareRangeMap(m,law,more);if(map){const rows=byMap.get(map)??[];rows.push(law);byMap.set(map,rows)}}
 for(const [map,key]of readTuples(values,more))for(const law of byMap.get(map)??[]){
  if(!more())return out;const id=json([law.name,keyId(key)]);if(seen.has(id))continue;seen.add(id)
  out.push({law:law.name,tuple:[key],map,premise:substC(law.holds,{vars:{[law.forall!]:key},maps:{},flags:{}})})
 }
 return out
}

export type CompleteReadMatch={kind:'complete-coherent-read',coherentReadMatch:true,law:string,tuple:E[],source:{kind:'root'|'selected'|'transition',read:[string,E],witness?:string,path?:string[],freeNames?:string[]},pattern:E,binding:Record<string,E>,premise:C}
// A SINGLE actual primitive read binds every coordinate. Index before optional
// partial-coordinate/pair exploration; no invented terms, projections or aliases.
export function completeReadMatches(m:Machine,laws:Law[],own:Law,decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,more:()=>boolean=candidateWork().tick,includeSelected=true):CompleteReadMatch[]{
 const out:CompleteReadMatch[]=[],seen=new Set<string>(),primitive=(map:string)=>Object.hasOwn(m.maps??{},map)&&!Object.hasOwn(m.counts??{},map)
 const byMap=new Map<string,{law:Law,ns:string[],pattern:E}[]>()
 for(const law of laws){
  if(!more())return out
  const ns=vars(law);if(law===own||!law.forall||law.some?.length||new Set(ns).size!==ns.length)continue
  const patterns=lawReads(law,more);if(!more())return out
  if(patterns.some(([map])=>Object.hasOwn(m.counts??{},map)))continue
  for(const [map,pattern]of patterns){if(!more())return out;if(!primitive(map))continue;const entries=byMap.get(map)??[];entries.push({law,ns,pattern});byMap.set(map,entries)}
 }
 const match=(source:CompleteReadMatch['source'])=>{
  for(const {law,ns,pattern}of byMap.get(source.read[0])??[]){
   if(!more())return
   const binding=matchRead(pattern,source.read[1],ns)??(source.kind==='selected'?matchAffineRemainder(pattern,source.read[1],ns,new Set([source.witness!]))?.binding:undefined)
   if(!binding||!ns.every(n=>Object.hasOwn(binding,n)))continue
   if(keyId(substE(pattern,{vars:binding,maps:{},flags:{}}))!==keyId(source.read[1]))continue
   const tuple=ns.map(n=>binding[n]!),id=json([law.name,tuple]);if(seen.has(id))continue;seen.add(id)
   out.push({kind:'complete-coherent-read',coherentReadMatch:true,law:law.name,tuple,source,pattern,binding,premise:substC(law.holds,{vars:binding,maps:{},flags:{}})})
  }
 }
 const rootNames=vars(own).map((n,i)=>i===0?n+'#':n),root=substC(own.holds,{vars:Object.fromEntries(vars(own).map((n,i)=>[n,x(rootNames[i]!)])),maps:{},flags:{}})
 if(!own.some?.length)for(const read of readTuples(root,more)){
  if(!more())return out
  // Root-bound keys, not every cold constant/range read embedded in the law.
  if(primitive(read[0])&&rootNames.some(n=>hasVar(read[1],n)))match({kind:'root',read})
 }
 for(const source of transitionReads(m,own,more)){if(!more())return out;if(primitive(source.read[0]))match({kind:'transition',...source})}
 if(!includeSelected)return out
 const needed=new Set(cert.insts.flatMap(i=>i.terms.map(([,id])=>id))),liveReads=cert.reads.filter(([id])=>needed.has(id))
 const witnesses=new Set(cert.insts.map(i=>i.wit)),reserved=new Set([...m.params,...m.inputs,...Object.keys(m.state),...names(root)])
 // The optional pool may have hundreds of unused reads. Match only the exact
 // live certificate closure (at most three reads per selected instance), not
 // the pool; no pool witness or unused source is admitted by this projection.
 if(cert.insts.length>10||liveReads.length>30||liveReads.length!==needed.size||witnesses.size!==cert.insts.length||cert.insts.some(i=>reserved.has(i.wit)||[...names(i.below)].some(n=>witnesses.has(n)))||liveReads.some(([id,,key])=>witnesses.has(id)||[...names(key)].some(n=>witnesses.has(n))))return out
 for(const i of cert.insts){
  if(!more())return out
  const body=mcGoal([],decls,{reads:liveReads,insts:[i],picks:[]})?.hyps.at(-1)
  if(!body)continue
  for(const read of readTuples(body,more)){if(!more())return out;if(primitive(read[0])&&hasVar(read[1],i.wit))match({kind:'selected',read,witness:i.wit})}
 }
 return out
}

export function ownPREMatches(m:Machine,laws:Law[],own:Law,decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,rawPost:C|undefined,sourceMaps:ReadonlySet<string>,preHyps:C[],more:()=>boolean=candidateWork().tick){
 const ns=[own.forall,...(own.keys??[])].filter((n):n is string=>!!n),out:{law:string,tuple:E[],witness:string,countRead:[string,E],sourceLaw:string,sourcePremise:C,sourceRead:[string,E],premise:C}[]=[],seen=new Set<string>(),reads=new Map(cert.reads.map(r=>[r[0],r]))
 if(ns.length<2)return out
 const present=presentPremises(preHyps,more),patterns=lawReads(own,more),sources=laws.filter(l=>more()&&l!==own&&!l.forall&&!l.keys?.length&&!l.some?.length&&present.has(json(l.holds)))
 for(const i of targetKeylessMeets(m,decls,cert,rawPost,sourceMaps,more))for(const [,id]of i.terms){
  if(!more())return out
  const count=reads.get(id);if(!count||!Object.hasOwn(m.counts??{},count[1]))continue
  for(const [map,pattern]of patterns){
   if(!more())return out
   if(map!==count[1])continue
   const anchor=matchRead(pattern,count[2],ns);if(!anchor||!Object.keys(anchor).length)continue
   if(keyId(substE(pattern,{vars:anchor,maps:{},flags:{}}))!==keyId(count[2]))continue
   for(const source of sources)for(const sourceRead of lawReads(source,more)){
    if(!more())return out
    if(!Object.hasOwn(m.maps??{},sourceRead[0]))continue
    for(const [otherMap,otherPattern]of patterns){
     if(!more())return out
     if(otherMap!==sourceRead[0])continue
     const other=matchRead(otherPattern,sourceRead[1],ns);if(!other||!Object.keys(other).some(k=>!anchor[k])||Object.keys(anchor).some(k=>other[k]&&keyId(anchor[k]!)!==keyId(other[k]!)))continue
     const binding={...anchor,...other};if(!ns.every(n=>binding[n]))continue
     if(keyId(substE(otherPattern,{vars:binding,maps:{},flags:{}}))!==keyId(sourceRead[1]))continue
     const tuple=ns.map(n=>binding[n]!),identity=json(tuple);if(seen.has(identity))continue;seen.add(identity)
     out.push({law:own.name,tuple,witness:i.wit,countRead:[count[1],count[2]],sourceLaw:source.name,sourcePremise:source.holds,sourceRead,premise:substC(own.holds,{vars:binding,maps:{},flags:{}})})
    }
   }
  }
 }
 return out
}

const nonnegative=(e:E)=>{const a=linOfE(e);return !!a&&Object.values(a).every(k=>Number.isSafeInteger(k)&&k>=0)}
export type TermProposal={kind:'one-remaining-coordinate-term-proposal',coherentReadMatch:false,law:string,tuple:E[],witness?:string,countRead?:[string,E],rootLinked?:true,ownWriteKeyMatch?:boolean,anchorRead:[string,E],anchorPattern:E,anchor:Record<string,E>,remaining:string,term:E,sourceLaw?:string,sourcePremise?:C,sourceKind?:'read'|'write',sourceRead:[string,E],sourcePattern:E,projection:Projection,ignoredCounterpartCoordinates:{binder:string,retained:E,counterpart:E}[],sourceKeyReconstructed:boolean,premise:C}
export function remainingCoordinateProposals(m:Machine,laws:Law[],decls:CountDecl[],cert:Pick<CountCert,'reads'|'insts'>,rawPost:C|undefined,sourceMaps:ReadonlySet<string>,preHyps:C[],more:()=>boolean=candidateWork().tick,own?:Law):TermProposal[]{
 const boundedReads=(value:unknown)=>readTuples(value,more)
 const out:TermProposal[]=[],seen=new Set<string>(),useful=new Map<string,number>(),ownWriteKeys=new Set<string>(),reads=new Map(cert.reads.map(r=>[r[0],r])),directions=rawPost?postDirections(rawPost,decls).filter(d=>d.directions.includes('upper')):[]
 const primitive=(map:string)=>Object.hasOwn(m.maps??{},map)&&!Object.hasOwn(m.counts??{},map)
 const present=presentPremises(preHyps,more),sources:{read:[string,E],law?:string,premise?:C,kind?:'read'|'write'}[]=[]
 for(const l of laws)if(more()&&!l.forall&&!l.keys?.length&&!l.some?.length&&present.has(json(l.holds)))for(const read of lawReads(l,more))sources.push({read,law:l.name,premise:l.holds})
 const preReads=boundedReads(preHyps),anchors:{read:[string,E],witness?:string,countRead?:[string,E],rootLinked?:true}[]=[]
 if(own){
  const ns=vars(own),binding=Object.fromEntries(ns.map((n,i)=>[n,x(i===0?n+'#':n)])),rootReads=boundedReads(substC(own.holds,{vars:binding,maps:{},flags:{}})),rootKeys=new Set(rootReads.map(([,key])=>keyId(key))),ownMaps=new Set(rootReads.map(([map])=>map))
  for(const [map,w]of Object.entries(m.step.maps??{}))if(more()&&ownMaps.has(map)&&!('each'in w))ownWriteKeys.add(keyId(w.key))
  // These are genuine concrete PRE terms, not inferred aliases between cells.
  // Other primitive maps must actually occur at the exact root key in PRE.
  for(const read of [...rootReads,...preReads])if(more()&&primitive(read[0])&&rootKeys.has(keyId(read[1])))anchors.push({read,rootLinked:true})
  const scope=new Set([...m.params,...m.inputs,...Object.keys(m.state)]),concrete=(key:E)=>[...names(key)].every(n=>scope.has(n))
  const concreteStep={...m.step,maps:Object.fromEntries(Object.entries(m.step.maps??{}).filter(([,w])=>!('each'in w)))}
  for(const read of boundedReads(concreteStep))if(primitive(read[0])&&concrete(read[1]))sources.push({read,kind:'read'})
  for(const [map,w]of Object.entries(m.step.maps??{}))if(more()&&primitive(map)&&!('each'in w)&&concrete(w.key))sources.push({read:[map,w.key],kind:'write'})
 }
 for(const i of targetKeylessMeets(m,decls,cert,rawPost,sourceMaps,more))for(const [,id]of i.terms){
  if(!more())return out
  const count=reads.get(id);if(!count||!directions.some(d=>d.map===count[1]+'#'&&keyId(d.key)===keyId(count[2])))continue
  for(const read of preReads)if(more()&&primitive(read[0])&&keyId(read[1])===keyId(count[2]))anchors.push({read,witness:i.wit,countRead:[count[1],count[2]]})
 }
 // Exact own-write keys rank genuine source terms; this NEVER equates cells.
 sources.sort((a,b)=>Number(ownWriteKeys.has(keyId(b.read[1])))-Number(ownWriteKeys.has(keyId(a.read[1])))||Number(b.kind==='write')-Number(a.kind==='write')||json(a.read).localeCompare(json(b.read)))
 anchors.sort((a,b)=>Number(!!b.rootLinked)-Number(!!a.rootLinked)||keyId(a.read[1]).localeCompare(keyId(b.read[1]))||json(a.read).localeCompare(json(b.read)))
 const anchorSeen=new Set<string>(),patternsByLaw=new Map<Law,[string,E][]>()
 for(const a of anchors){
  if(!more())return out
  const anchorRead=a.read,aid=json(anchorRead);if(anchorSeen.has(aid))continue;anchorSeen.add(aid)
  for(const law of laws){
   if(!more())return out
   const ns=vars(law),group=json([law.name,keyId(anchorRead[1])]);if(!law.forall||law.some?.length||ns.length<2||new Set(ns).size!==ns.length||(useful.get(group)??0)>=4)continue
   let patterns=patternsByLaw.get(law);if(!patterns){patterns=lawReads(law,more).slice().sort((a,b)=>json(a).localeCompare(json(b)));patternsByLaw.set(law,patterns)}
   for(const [map,anchorPattern]of patterns){
    if(!more())return out
    if(map!==anchorRead[0])continue
    const anchor=matchRead(anchorPattern,anchorRead[1],ns);if(!anchor||!Object.keys(anchor).length||keyId(substE(anchorPattern,{vars:anchor,maps:{},flags:{}}))!==keyId(anchorRead[1]))continue
    const missing=ns.filter(n=>!Object.hasOwn(anchor,n));if(missing.length!==1)continue;const remaining=missing[0]!
    for(const [otherMap,sourcePattern]of patterns){
     if(!more())return out
     if(otherMap!==map||json(sourcePattern)===json(anchorPattern)||!nonnegative(sourcePattern))continue
     // Fixed coordinates are used only to find the one missing term. A conflicting
     // counterpart is provenance, never a coherent match or an equality premise.
     const fixedView:Machine={...m,state:{...m.state,...anchor}}
     for(const source of sources){
      if(!more())return out
      if((useful.get(group)??0)>=4)break
      const sourceRead=source.read;if(sourceRead[0]!==map||!nonnegative(sourceRead[1]))continue
      const projection=projectBoundCoordinate(fixedView,sourcePattern,sourceRead[1],remaining),term=projection?.binding[remaining]
      if(!projection||!term||Object.keys(projection.binding).length!==1)continue
      const binding={...anchor,[remaining]:term},tuple=ns.map(n=>binding[n]!),identity=json([law.name,tuple]);if(seen.has(identity))continue
      if(keyId(substE(anchorPattern,{vars:binding,maps:{},flags:{}}))!==keyId(anchorRead[1]))throw Error('term proposal changed anchor')
      const counterpart=matchRead(sourcePattern,sourceRead[1],ns),ignoredCounterpartCoordinates=Object.entries(anchor).flatMap(([binder,retained])=>counterpart?.[binder]&&keyId(counterpart[binder]!)!==keyId(retained)?[{binder,retained,counterpart:counterpart[binder]!}]:[])
      const premise=substC(law.holds,{vars:binding,maps:{},flags:{}})
      if(structuralTruth(premise,more)!==true)useful.set(group,(useful.get(group)??0)+1)
      seen.add(identity);out.push({kind:'one-remaining-coordinate-term-proposal',coherentReadMatch:false,law:law.name,tuple,...(a.rootLinked?{rootLinked:true as const}:{witness:a.witness,countRead:a.countRead}),ownWriteKeyMatch:ownWriteKeys.has(keyId(sourceRead[1])),anchorRead,anchorPattern,anchor,remaining,term,...(source.kind?{sourceKind:source.kind}:{sourceLaw:source.law,sourcePremise:source.premise}),sourceRead,sourcePattern,projection,ignoredCounterpartCoordinates,sourceKeyReconstructed:keyId(substE(sourcePattern,{vars:binding,maps:{},flags:{}}))===keyId(sourceRead[1]),premise})
     }
    }
   }
  }
 }
 // Admit one proposal per distinct actual key before symmetric/source extras.
 // The full anchored law and nonalias provenance travel with every candidate.
 const byLaw=new Map<string,Map<string,TermProposal[]>>()
 for(const p of out){const keys=byLaw.get(p.law)??new Map<string,TermProposal[]>(),id=keyId(p.anchorRead[1]),q=keys.get(id)??[];q.push(p);keys.set(id,q);byLaw.set(p.law,keys)}
 const ordered:TermProposal[]=[]
 for(const keys of byLaw.values()){
  const queues=[...keys.values()].sort((a,b)=>Number(!!b[0]!.rootLinked)-Number(!!a[0]!.rootLinked)||keyId(a[0]!.anchorRead[1]).localeCompare(keyId(b[0]!.anchorRead[1])))
  for(const q of queues)q.sort((a,b)=>Number(!!b.ownWriteKeyMatch)-Number(!!a.ownWriteKeyMatch)||json(a.anchorPattern).localeCompare(json(b.anchorPattern))||json(a.sourceRead).localeCompare(json(b.sourceRead))||json(a.tuple).localeCompare(json(b.tuple)))
  const rounds=Math.max(0,...queues.map(q=>q.length))
  for(let i=0;i<rounds;i++)for(const q of queues)if(q[i])ordered.push(q[i]!)
 }
 return ordered
}

// Deliberately incomplete structural truth: no solver, path assumption, source
// alias, or arithmetic inference. Unknown means KEEP the original instance.
function structuralTruth(c:C,more:()=>boolean):boolean|undefined{
 if(!more())return
 if(c.op==='not'){const v=structuralTruth(c.x,more);return v===undefined?undefined:!v}
 if(c.op==='and'||c.op==='or'){
  const vs=c.xs.map(x=>structuralTruth(x,more))
  return c.op==='and'?(vs.includes(false)?false:vs.every(v=>v===true)?true:undefined):(vs.includes(true)?true:vs.every(v=>v===false)?false:undefined)
 }
 if(c.op==='='||c.op==='<'||c.op==='<='){
  if(json(c.a)===json(c.b))return c.op!=='<'
  if(c.a.op==='const'&&c.b.op==='const')return c.op==='='?c.a.value===c.b.value:c.op==='<'?c.a.value<c.b.value:c.a.value<=c.b.value
 }
 return
}
function prioritizeTerms(laws:Law[],at:Instances,proposals:TermProposal[],room:number,newSources:Set<string>,more:()=>boolean){
 const out={...at},added:TermProposal[]=[],replacements:{law:string,tuple:E[],premise:C,replacement:TermProposal,reason:'structurally-true',origin:'new-source'|'initial',admissionDebit:number}[]=[],skipped:TermProposal[]=[]
 let admissionCount=0
 for(const p of proposals){
  if(!more())break
  const law=laws.find(l=>l.name===p.law),n=p.tuple.length,old=out[p.law]??[]
  if(!law||!n||old.length%n||old.length/n>4||structuralTruth(p.premise,more)===true){skipped.push(p);continue}
  if(duplicateTerm(law,old,p.tuple))continue
  if(admissionCount<room&&old.length/n<4){out[p.law]=[...old,...p.tuple];newSources.add(json([p.law,p.tuple]));added.push(p);admissionCount++;continue}
  // Replacement does not create budget: same-law when per-law-full, otherwise
  // any explicitly true slot. Only this recognizer authorizes removal.
  let replaced=false
  for(const candidate of old.length/n>=4?[law]:laws){
   if(!more())break
   const width=vars(candidate).length,had=out[candidate.name]??[];if(!width||had.length%width||candidate.some?.length)continue
   for(let i=0;i<had.length;i+=width){
    if(!more())break
    const tuple=had.slice(i,i+width),premise=substC(candidate.holds,{vars:Object.fromEntries(vars(candidate).map((n,j)=>[n,tuple[j]!])),maps:{},flags:{}})
    if(structuralTruth(premise,more)!==true)continue
    const id=json([candidate.name,tuple]),origin=newSources.has(id)?'new-source':'initial',admissionDebit=origin==='initial'?1:0
    if(admissionCount+admissionDebit>room)continue
    admissionCount+=admissionDebit;newSources.delete(id);newSources.add(json([p.law,p.tuple]))
    out[candidate.name]=[...had.slice(0,i),...had.slice(i+width)];out[p.law]=[...(out[p.law]??[]),...p.tuple]
    replacements.push({law:candidate.name,tuple,premise,replacement:p,reason:'structurally-true',origin,admissionDebit});replaced=true;break
   }
   if(replaced)break
  }
 }
 return {at:out,added,replacements,skipped,admissionCount}
}

// A single shared budget for the entire attempt, not a separate quota per phase.
// Priorities only select terms. Even the projection-only proposal retains every
// anchored coordinate and every guard of the original law.
export function sparseReadInstances(m: Machine, laws: Law[], own: Law, at: Instances, goal: Goal,
  cert: Pick<CountCert, 'reads' | 'insts'>, cap = 64, rawPost?: C, decls: CountDecl[] = [],
  sourceMaps: ReadonlySet<string> = new Set(), preHyps: C[] = [], budget = candidateWork(), completePriority: 'current'|'root' = 'current') {
  budget.mark('sources:begin')
  cap = Math.max(0, Math.min(64, cap))
  const slots = (l:Law) => !!l.forall && (at[l.name]?.length??0)/(1+(l.keys?.length??0)) < 4
  const available = cap>0 && (laws.some(slots) || slots(own) || Object.keys(m.step.flags??{}).length>0)
  const more=budget.tick,pairBudget={work:0}, sources=available?laws.filter(l=>!l.forall||slots(l)):[]
  // Reify indispensable own PRE/flag bindings before deriving downstream reads.
  // They often expose the very second read required by a live witness join.
  const foundationalOwn=available&&cert.insts.length?ownPREMatches(m,sources,own,decls,cert,rawPost,sourceMaps,preHyps,more):undefined
  const foundationalRoot=available&&cert.insts.length?rootFlagMatches(m,own,more):undefined
  const foundationalFlags=foundationalRoot?[...foundationalRoot,...targetFlagMatches(m,decls,cert,rawPost,sourceMaps,more)]:undefined
  if(foundationalFlags&&foundationalOwn){
   const next={...at},found:Choice[]=[]
   const add=(p:{law:string,tuple:E[]})=>{const width=p.tuple.length,old=next[p.law]??[];if(!width||old.length%width||old.length/width>=4||found.length>=cap)return;for(let i=0;i<old.length;i+=width)if(json(old.slice(i,i+width))===json(p.tuple))return;next[p.law]=[...old,...p.tuple];found.push({law:p.law,tuple:p.tuple,coherent:true,conflicts:[],score:Infinity,countLaw:false,sources:[]})}
   for(const p of foundationalFlags)add(p)
   const flagAdmissions=found.length
   for(const p of foundationalOwn)add(p)
   if(found.length){const empty=emptyReadResult(next,cap);budget.mark('sources:foundation');return {...empty,added:found,completeMatches:[],readKindMatches:[],termProposals:[],vacuousTermProposals:[],ownMatches:foundationalOwn,priorityMatches:[],rootFlags:foundationalRoot??[],flagMatches:foundationalFlags,kindMatches:[],summary:{...empty.summary,foundationBarrier:true,completeReadAdmissions:0,liveReadAdmissions:0,readKindAdmissions:0,termProposalAdmissions:0,ownPREAdmissions:found.length-flagAdmissions,flagAdmissions,sharedGlobalBudget:true,generationWork:{...budget.state}}}}
  }
  const completeMatches = available?completeReadMatches(m, sources, own, decls, cert, more, completePriority==='current'):[]
  budget.mark('sources:complete')
  const liveMatches=available&&cert.insts.length?baseReadInstances(m,sources,own,at,goal,cert,cap,rawPost,more,'live',pairBudget):emptyReadResult(at,cap)
  const readKindMatches = available?primitiveReadKinds(m,sources,completeMatches.map(p=>p.premise),more):[]
  const termProposals = available?remainingCoordinateProposals(m, sources, decls, cert, rawPost, sourceMaps, preHyps, more, own):[]
  budget.mark('sources:terms')
  const ownMatches = foundationalOwn??(available?ownPREMatches(m, sources, own, decls, cert, rawPost, sourceMaps, preHyps, more):[])
  const priorityMatches = available?targetReadMatches(m, sources.filter(l => l !== own), decls, cert, rawPost, sourceMaps, more):[]
  const rootFlags = foundationalRoot??(available?rootFlagMatches(m,own,more):[])
  const flagMatches = foundationalFlags??(available?[...rootFlags,...targetFlagMatches(m, decls, cert, rawPost, sourceMaps, more)]:[])
  const kindMatches = available?targetKindMatches(m, sources, decls, cert, rawPost, sourceMaps, more):[]
  const out: Instances = {...at}, added: Choice[] = []
  const append = (p: {law: string, tuple: E[]}, coherent = true) => {
    const width = p.tuple.length, old = out[p.law] ?? []
    const flag = p.law.startsWith('?'), prior = flag ? flagMatches.filter(f => f.law === p.law && old.some(t => json(t) === json(f.tuple[0]))).length : old.length / width
    if (!width || old.length % width || prior >= 4 || added.length >= cap) return
    if(!coherent&&duplicateTerm(laws.find(l=>l.name===p.law),old,p.tuple))return
    for (let i = 0; i < old.length; i += width) if (json(old.slice(i, i + width)) === json(p.tuple)) return
    out[p.law] = [...old, ...p.tuple]
    added.push({law: p.law, tuple: p.tuple, coherent, conflicts: [], score: Infinity, countLaw: false, sources: []})
  }
  for (const p of completeMatches) if(p.source.kind==='selected')append(p)
  const beforeLive=added.length
  for(const p of liveMatches.added){const before=added.length;append(p);if(added.length>before)added[added.length-1]=p}
  const liveReadAdmissions=added.length-beforeLive
  for (const p of completeMatches) if(p.source.kind!=='selected')append(p)
  const completeReadAdmissions = added.length-liveReadAdmissions
  for(const p of readKindMatches)append(p)
  const readKindAdmissions = added.length - completeReadAdmissions
  const vacuousTermProposals:TermProposal[]=[],writeAnchored=new Set(termProposals.filter(p=>p.ownWriteKeyMatch).map(p=>p.law))
  // Deduplication must not backfill its freed slots with lower-quality cold
  // sources when the current obligation supplies an exact write-key donor.
  for (const p of termProposals) {if(structuralTruth(p.premise,more)===true)vacuousTermProposals.push(p);else if(p.ownWriteKeyMatch||!writeAnchored.has(p.law))append(p, false)}
  const termProposalAdmissions = added.length - completeReadAdmissions - readKindAdmissions - liveReadAdmissions
  for (const p of ownMatches) append(p)
  const ownPREAdmissions = added.length - completeReadAdmissions - readKindAdmissions - termProposalAdmissions - liveReadAdmissions
  for (const p of priorityMatches) append(p)
  const beforeFlags = added.length
  for (const p of flagMatches) append(p)
  const flagAdmissions = added.length - beforeFlags
  for (const p of kindMatches) append(p)
  // Do not refill deduplicated preferred-source slots through the generic
  // partial-read fallback. Exact matches above remain eligible on every pass.
  const restSources=sources.filter(l=>!writeAnchored.has(l.name))
  const rest = available?baseReadInstances(m, restSources, own, added.length ? out : at, goal, cert, cap - added.length, rawPost, more,'cold',pairBudget):emptyReadResult(at,cap)
  budget.mark('sources:end')
  return {...rest, added: [...added, ...rest.added], completeMatches, readKindMatches, termProposals, vacuousTermProposals, ownMatches, priorityMatches, rootFlags, flagMatches, kindMatches, summary: {...rest.summary, foundationBarrier:false, cap, completeReadAdmissions, liveReadAdmissions, livePairWork:liveMatches.summary.livePairWork+rest.summary.livePairWork, livePairExhausted:liveMatches.summary.livePairExhausted||rest.summary.livePairExhausted, readKindAdmissions, termProposalAdmissions, ownPREAdmissions, flagAdmissions, sharedGlobalBudget: true, generationWork:{...budget.state}}}
}
// Search context only, never an admitted invariant. Keep exact source laws and
// order; every successful certificate must be widened and checked on the whole.
export function sourceContext(m:Machine,laws:Law[],target:Law,support:ReadonlySet<Law>):Law[]{
 const width=Math.max(1,...Object.values(m.step.maps??{}).map(w=>'each'in w?0:names(w.key).size))
 const maps=(value:unknown)=>new Set(readTuples(value).map(([map])=>map)),demand=maps(target.holds)
 for(const map of demand){const d=m.counts?.[map];if(d)for(const dep of maps([d.body,d.below]))demand.add(dep)}
 const countDemand=[...demand].some(map=>!!m.counts?.[map])
 const arity=(l:Law)=>Number(!!l.forall)+(l.keys?.length??0),signature=(l:Law)=>json([arity(l),[...maps(l.holds)].sort()])
 const direct=new Set(laws.filter(l=>!support.has(l)&&readTuples(l.holds).every(([map])=>!m.counts?.[map])).map(signature))
 return laws.filter(l=>{
  if(l===target)return true
  const reads=readTuples(l.holds)
  if(support.has(l))return maps(l.holds).size<2||!direct.has(signature(l))
  if(!reads.length)return true
  if(reads.some(([map])=>!!m.counts?.[map]))return reads.some(([map])=>!!m.counts?.[map]&&(demand.has(map)||countDemand&&genuinelyKeyless(m.counts[map]!)))
  const bound=new Set([l.forall,...l.keys??[],...l.some??[]]);if(arity(l)>width||[...names(l.holds)].some(v=>!bound.has(v)&&Object.hasOwn(m.state,v)))return false
  return reads.every(([map])=>demand.has(map))
 })
}

export const countSignature = (c: Pick<CountCert, 'reads' | 'insts' | 'picks'>) => json([
  c.reads.map(r => [r[1], keyId(r[2])]).sort((a, b) => json(a).localeCompare(json(b))), ids(c).sort()])
export const refinementSignature = (goal: Goal, c: Pick<CountCert, 'reads' | 'insts' | 'picks'>) => json([
  countSignature(c), [...new Set(readTuples(goal.hyps).map(([mp, key]) => json([mp, keyId(key)])))].sort(), c.insts.map(i => i.wit).sort()])

// Keep selected picks on the ordinary, non-renaming path. Only the closed,
// pick-free view may discard unused reads and stabilize witness identifiers.
export function selectedCertificate<T extends Pick<CountCert, 'reads' | 'insts' | 'picks'>>(goal: Goal, decls: CountDecl[], view: T, state: ReturnType<typeof stableState>, lazyRoom: boolean) {
  if (view.insts.length + (view.picks?.length??0) > 10 || new Set(ids(view)).size !== ids(view).length) throw new UnsupportedCountProposal('selected semantic alias or live cap')
  if (!lazyRoom && !(view.picks?.length)) return stableSelected(goal, decls, view, state, {lazyRoom: false, fullPoolUsed: false}).cert
  if (new Set(view.reads.map(r=>r[0])).size!==view.reads.length || new Set(view.insts.map(i=>i.wit)).size!==view.insts.length) throw new UnsupportedCountProposal('nonunique selected read/witness')
  for (const i of view.insts) if (state.reserved.has(i.wit) || view.reads.some(r=>r[0]===i.wit || names(r[2]).has(i.wit)) || decls.some(d=>names([d.below,d.body]).has(i.wit))) throw new UnsupportedCountProposal('selected witness capture')
  if (!mcGoal(goal.hyps,decls,view)) throw new UnsupportedCountProposal('selected view cannot reify')
  return {...view,picks:view.picks??[],wits:view.insts.map(i=>i.wit)}
}
export function sourceBoundMaps(m: Machine, laws: Law[], at: Instances, more:()=>boolean=candidateWork().tick) {
  const maps=new Set<string>()
  for(const l of laws){
    if(!more())break
    if(!at[l.name]?.some(t=>t.op==='const'&&t.value===0)||!vacuousCountBinder(m,l,more))continue
    for(const [map]of readTuples(l.holds,more)){const d=m.counts?.[map];if(d&&genuinelyKeyless(d))maps.add(map)}
  }
  return maps
}
// One shared generation budget covers preparation, pool construction and every
// refinement in the target attempt. No fresh fuel is created by a source phase.
export function prepareSupport(m: Machine, laws: Law[], own: Law, initial: Instances, pass: 0 | 1, budget=candidateWork()) {
  const more=budget.tick;budget.mark('prepare:begin')
  const limit=pass?32:64 // Keep half of the same 64 slots for actual selected witnesses.
  let at: Instances = {...initial}, seedCount = 0
  const newSources=new Set<string>()
  const append = (name: string, tuple: E[]) => {
    const old=at[name]??[],width=tuple.length
    if(!width||seedCount>=limit||old.length%width||old.length/width>=4)return
    for(let i=0;i<old.length;i+=width)if(json(old.slice(i,i+width))===json(tuple))return
    at[name]=[...old,...tuple];newSources.add(json([name,tuple]));seedCount++
  }
  const row = () => countedObligations(m,laws,{[own.name]:at},laws.indexOf(own)).at(-1)!
  if(!pass){
   const cold=row(),ns=vars(own),root=substC(own.holds,{vars:Object.fromEntries(ns.map((n,i)=>[n,x(i===0?n+'#':n)])),maps:{},flags:{}})
   // The root and its reachable free transition reads claim range slots before
   // ambient scalar/flag witnesses. All terms still instantiate original laws.
   const reads=[...readTuples(root,more),...transitionReads(m,own,more).map(s=>s.read),...readTuples(cold.goal.hyps,more)]
   for(const l of laws){if(seedCount>=64||!more())break;const map=bareRangeMap(m,l,more);if(map)for(const [mp,key]of reads){if(!more()||seedCount>=64)break;if(mp===map)append(l.name,[key])}}
  }
  if(pass){const seeded=seedVacuousCounts(m,laws,at,limit-seedCount,more);at=seeded.at;seedCount+=seeded.added.length;for(const s of seeded.added)newSources.add(json([s.law,s.tuple]))}
  const sourceMaps=sourceBoundMaps(m,laws,at,more)
  budget.mark('prepare:seeded')
  const cold=row(),empty={reads:[],insts:[],picks:[],wits:[],loose:false},cert=empty,goal=mcGoal(cold.goal.hyps,cold.decls,cert)
  budget.mark('prepare:certificate')
  const termAdmissions:TermProposal[]=[],replacements:ReturnType<typeof prioritizeTerms>['replacements']=[]
  if(goal&&more()){
   // Complete root/free-transition bindings and their exact range laws may
   // enter early. Count witnesses are deferred until a live view is selected.
   const seeds=sparseReadInstances(m,laws,own,at,goal,cert,limit-seedCount,cold.goal.hyps.at(-1),cold.decls,sourceMaps,cold.goal.hyps.slice(0,-1),budget,'root')
   const roots=new Set([...seeds.completeMatches.filter(p=>p.source.kind!=='selected'),...seeds.readKindMatches,...seeds.rootFlags].map(p=>json([p.law,p.tuple])))
   const proposals=new Map(seeds.termProposals.map(p=>[json([p.law,p.tuple]),p]))
   for(const s of seeds.added){
    const proposal=proposals.get(json([s.law,s.tuple]))
    // Primitive proposals keep their own provenance; they are NOT count laws.
    if(!pass||s.law===own.name||s.countLaw||proposal||roots.has(json([s.law,s.tuple]))){const before=seedCount;append(s.law,s.tuple);if(proposal&&seedCount>before)termAdmissions.push(proposal)}
   }
  }
  if(pass&&more()){
   // The just-produced PRE support exposes additional actual primitive anchors.
   // Revisit only this bounded term path BEFORE counts.ts's seedCount<64 gate.
   // A full law with no explicitly true slot cannot accept another term. Do
   // not enumerate it again; initial/new-source replacement debits stay below.
   const eligible=laws.filter(l=>{
    if(!more())return false
    if(!l.forall)return true
    const ns=vars(l),old=at[l.name]??[],n=ns.length
    if(n<2||l.some?.length||old.length%n||old.length/n>4)return false
    if(old.length/n<4)return true
    for(let i=0;i<old.length;i+=n)if(structuralTruth(substC(l.holds,{vars:Object.fromEntries(ns.map((name,j)=>[name,old[i+j]!])),maps:{},flags:{}}),more)===true)return true
    return false
   })
   budget.mark('prepare:revisit')
   const current=eligible.some(l=>!!l.forall)?row():undefined,proposals=current?remainingCoordinateProposals(m,eligible,current.decls,cert,current.goal.hyps.at(-1),sourceMaps,current.goal.hyps.slice(0,-1),more,own):[]
   const priority=prioritizeTerms(laws,at,proposals,limit-seedCount,newSources,more)
   at=priority.at;seedCount+=priority.admissionCount;termAdmissions.push(...priority.added,...priority.replacements.map(r=>r.replacement));replacements.push(...priority.replacements)
  }
  const finalSourceMaps=replacements.length?sourceBoundMaps(m,laws,at,more):sourceMaps
  budget.mark('prepare:end')
  return {at,seedCount,sourceMaps:finalSourceMaps,termAdmissions,replacements,generationWork:{...budget.state}}
}

// The pool deliberately retains raw read aliases. A live selection does not:
// one semantic id denotes one representative, never all of its raw spellings.
export function chosenView<T extends Pick<CountCert, 'reads' | 'insts' | 'picks'>>(full: T, chosen: Set<string>, cap = 10) {
  const keys=ids(full),seen=new Set<string>(),picks: NonNullable<CountCert['picks']>=[],insts:CountInst[]=[]
  const admit=(id:string)=>{if(!chosen.has(id)||seen.has(id))return false;if(seen.size>=Math.min(10,cap))throw new UnsupportedCountProposal('selected live cap');seen.add(id);return true}
  for(const [j,p]of (full.picks??[]).entries())if(admit(keys[j]!))picks.push(p)
  for(const [j,i]of full.insts.entries())if(admit(keys[j+(full.picks?.length??0)]!))insts.push(i)
  if(seen.size!==chosen.size)throw new UnsupportedCountProposal('selected semantic id missing')
  return {...full,picks,insts,wits:insts.map(i=>i.wit)}
}
