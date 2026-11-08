// A count cell that is free in the abstraction can make MBQI miss a useful law
// instance. Bridge the goal's keys with request keys for unary/binary count laws.
// These are ordinary universal instances, never additional arithmetic facts.
export function countLawSeeds(m: Machine, laws: Law[], at: Instances, own: E[], request: E[], fromRequestOnly = false, options: {requestDiagonals?: boolean} = {}): Instances {
  let out=at
  for(const law of laws) {
    if(!law.forall||(law.keys?.length??0)>1) continue
    let counted=false
    walkOnce(law.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])counted=true})
    if(!counted) continue
    const n=1+(law.keys?.length??0), candidates=n===1?[...own,...request].map(x=>[x]):[...options.requestDiagonals?request.map(b=>[b,b]):[],...own.flatMap(a=>request.flatMap(b=>fromRequestOnly?[[b,a]]:[[a,b],[b,a]]))]
    const have=at[law.name]??[], known=new Set<string>()
    for(let i=0;i<have.length;i+=n)known.add(JSON.stringify(have.slice(i,i+n)))
    const extra=candidates.slice(0,32).filter(t=>{const k=JSON.stringify(t);if(known.has(k))return false;known.add(k);return true}).flat()
    if(extra.length) {if(out===at)out={...at};out[law.name]=[...have,...extra]}
  }
  return out
}

// Universal field guards need ordinary goal-row instances even when no
// count witness mentions that row. Do not expand carried-set predicates here.
export function fieldGuardSeeds(m:Machine,at:Instances,keys:E[]):Instances{
 let out=at
 for(const [name,q]of Object.entries(m.step.flags??{})){
  if(q.op!=='all'||q.keys?.length)continue
  const maps=new Set<string>();walkOnce(q.c,(o:any)=>{if(o.op==='get')maps.add(o.map)})
  if(!maps.size||[...maps].some(map=>(m.inputMaps??[]).includes(map)||map in (m.counts??{})))continue
  const flag=`?${name}`,had=out[flag]??[],seen=new Set(had.map(t=>JSON.stringify(t))),extra:E[]=[]
  for(const key of keys.slice(0,32)){const id=JSON.stringify(key);if(!seen.has(id)){seen.add(id);extra.push(key)}}
  if(extra.length){if(out===at)out={...at};out[flag]=[...had,...extra]}
 }
 return out
}

// Coordinates of a count key are row parameters too. Treating only a bare key
// as a row loses the second row of a packed two-row count; arithmetic witnesses
// outside read keys are intentionally excluded.
export function rowKeyNames(m:Machine,law:Law):Set<string>{
  const names=new Set<string>()
  walkOnce(law.holds,(o:any)=>{
    if(o.op!=='get')return
    if(o.key.op==='var')names.add(o.key.name)
    if(m.counts?.[o.map])walkOnce(o.key,(k:any)=>{if(k.op==='var')names.add(k.name)})
  })
  return names
}

// A copied row changes the row coordinates, not an invariant's arithmetic
// witnesses. Bridge the target instance at those coordinates without enumerating
// fresh half-cardinality tuples (MBQI proposes those separately).
export function countRowBridges(m:Machine,law:Law,at:Instances,own:E[],request:E[]):Instances {
  const names=[law.forall,...law.keys??[]]
  if(!law.forall||own.length!==names.length)return at
  let counted=false
  walkOnce(law.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])counted=true})
  if(!counted)return at
  const rows=rowKeyNames(m,law),arity=names.length,had=at[law.name]??[],seen=new Set<string>()
  for(let i=0;i<had.length;i+=arity)seen.add(JSON.stringify(had.slice(i,i+arity)))
  const out:E[]=[]
  for(const [i,name] of names.entries())if(name&&rows.has(name))for(const source of [...request,{op:'const',value:0} as E]){
    const tuple=[...own];tuple[i]=source
    const key=JSON.stringify(tuple)
    if(!seen.has(key)){seen.add(key);out.push(...tuple)}
  }
  return out.length?{...at,[law.name]:[...had,...out]}:at
}

// Count reads must not depend on a CInst witness (checkMC's freshness rule).
// Numeric comparison witnesses may depend on it; only coordinates occurring
// inside a count read's key are filtered. Existing instances are left intact.
export function independentCountInstances(m:Machine,laws:Law[],before:Instances,next:Instances,witnesses:string[]):Instances|undefined {
  const blocked=new Set(witnesses),out:Instances={...before};let changed=false
  for(const [name,terms] of Object.entries(next)){
    const law=laws.find(l=>l.name===name),had=before[name]??[]
    if(terms.length<=had.length)continue
    if(!law){out[name]=terms;changed=true;continue}
    const names=[law.forall,...law.keys??[]],positions=new Set<number>(),arity=names.length
    walkOnce(law.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])walkOnce(o.key,(v:any)=>{if(v.op==='var'){const i=names.indexOf(v.name);if(i>=0)positions.add(i)}})})
    const extra:E[]=[]
    for(let i=had.length;i<terms.length;i+=arity){
      const tuple=terms.slice(i,i+arity);if(tuple.length!==arity)continue
      let dependent=false
      for(const j of positions)walkOnce(tuple[j],(o:any)=>{if(o.op==='var'&&blocked.has(o.name))dependent=true})
      if(!dependent)extra.push(...tuple)
    }
    if(extra.length){out[name]=[...had,...extra];changed=true}
  }
  return changed?out:undefined
}

// Keep a row law's column symbolic while bridging its row keys to request/source
// rows. Equal model values do not make the column variable the same term as a row.
export function fieldLawBridges(m:Machine,laws:Law[],at:Instances,own:E[],request:E[],column?:E):Instances {
  let out=at
  const sources=[...request,{op:'const',value:0} as E]
  for(const law of laws){
    const arity=1+(law.keys?.length??0)
    if(!law.forall||arity>3||arity===3&&!column)continue
    let counted=false
    walkOnce(law.holds,(o:any)=>{if(o.op==='get'&&m.counts?.[o.map])counted=true})
    if(counted)continue
    const tuples=arity===1?[...own,...sources].map(k=>[k]):own.flatMap(a=>sources.flatMap(b=>arity===2?[[a,b],[b,a]]:[[a,b,column!],[b,a,column!]]))
    const had=out[law.name]??[],seen=new Set<string>()
    for(let i=0;i<had.length;i+=arity)seen.add(JSON.stringify(had.slice(i,i+arity)))
    const extra=tuples.slice(0,32).filter(t=>{const k=JSON.stringify(t);if(seen.has(k))return false;seen.add(k);return true}).flat()
    if(extra.length){if(out===at)out={...at};out[law.name]=[...had,...extra]}
  }
  return out
}

// A small first certificate, not an axiom: equivalent indicator counts and a
// carried set against a stored-row count. The full pool remains the fallback.
import {type C, type E, type Law, type Machine, walkOnce, x} from './machine.ts'
import {type CountCert, type CountDecl, type Instances, substC, substE} from '../kernel/kernel.ts'
import {countsForReads} from './count-facts.ts'
import {proposeCountDemand} from './count-demand.ts'
import {proposeWriteCountFrames} from './count-write-frames.ts'
import {activeWriteRow} from './count-recovery/row-cases.ts'

// An untrusted starting subset for row-copy cases. Keep pre-state partitions
// and query-local frames/copies, not every unrelated source tuple. A caller
// must retain its full pool for fallback and check the resulting certificate.
export function copyCountSubset(m:Machine,cert:Pick<CountCert,'reads'|'insts'>):Pick<CountCert,'reads'|'insts'>{
 const reads=new Map(cert.reads.map(r=>[r[0],r])),variants=new Map<string,Set<string>>(),sources=new Set<string>()
 for(const [map,write]of Object.entries(m.step.maps??{}))if('each'in write){
  const scan=(e:E):void=>{
   if(e.op==='if'){scan(e.then);scan(e.else)}
   else if(e.op==='get'&&e.map===map&&e.key.op==='var'&&m.inputs.includes(e.key.name))sources.add(e.key.name)
  }
  scan(write.value)
 }
 const keys=(id:string,key:E):Set<string>=>{
  const prior=variants.get(id);if(prior)return prior
  const names=new Set<string>();walkOnce(key,(o:any)=>{if(o.op==='var'&&!m.inputs.includes(o.name)&&!m.params.includes(o.name)&&!(o.name in m.state))names.add(o.name)})
  const vars=[...names],out=new Set([JSON.stringify(key)])
  if(vars.length<=3)for(const input of sources.size?sources:m.inputs)for(let mask=1;mask<(1<<vars.length);mask++){
   const substitutions=Object.fromEntries(vars.filter((_,i)=>mask&(1<<i)).map(name=>[name,x(input)]))
   out.add(JSON.stringify(substE(key,{vars:substitutions,maps:{},flags:{}})))
  }
  variants.set(id,out);return out
 }
 return {...cert,insts:cert.insts.filter(inst=>{
  if(inst.terms.length>=3)return inst.terms.length===3&&inst.terms.every(([,id])=>!(reads.get(id)?.[1].endsWith('#')??true))
  if(inst.terms.length===1)return reads.get(inst.terms[0]![1])?.[1].endsWith('#')??false
  if(inst.terms.length!==2||!inst.terms.every(([coefficient])=>Math.abs(coefficient)===1))return true
  const a=reads.get(inst.terms[0]![1]),b=reads.get(inst.terms[1]![1]);if(!a||!b)return true
  const post=a[1].endsWith('#')?a:b[1].endsWith('#')?b:undefined,pre=post===a?b:a
  return !!post&&pre[1]===post[1].slice(0,-1)&&keys(post[0],post[2]).has(JSON.stringify(pre[2]))
 })}
}
// Generate directly for the conclusion's reads and their pre-state twins.
// This is separate from certFor's unchanged legacy prefix. At most 128
// structured proposals survive, and every one keeps its witness alternative.
export function demandCountCert(m:Machine,decls:CountDecl[],full:Pick<CountCert,'reads'|'insts'>,claim:C):Pick<CountCert,'reads'|'insts'>{
 const wanted=new Set<string>(),reserved=new Set([...m.inputs,...m.params,...Object.keys(m.state),...full.insts.map(q=>q.wit)])
 walkOnce(claim,(o:any)=>{
  if(o.op==='var'){reserved.add(o.name);if(full.reads.some(read=>read[0]===o.name))wanted.add(o.name)}
  if(o.op==='get')for(const read of full.reads)if(read[1]===o.map&&JSON.stringify(read[2])===JSON.stringify(o.key))wanted.add(read[0])
 })
 if(wanted.size<2)return full
 const cs=countsForReads(decls,full.reads);if(!cs)return full
 const byId=new Map(cs.map(c=>[c.v,c])),byCell=new Map(full.reads.map(r=>[JSON.stringify([r[1],r[2]]),r[0]])),heads=new Set(wanted),projected=new Set<string>(),actor=activeWriteRow(m,new Map())
 for(const read of full.reads)if(heads.has(read[0])&&read[1].endsWith('#')){
  const names=new Set<string>();walkOnce(read[2],(o:any)=>{if(o.op==='var'&&!m.inputs.includes(o.name)&&!m.params.includes(o.name))names.add(o.name)})
  const vars=[...names];if(actor&&vars.length<=3)for(let mask=1;mask<(1<<vars.length);mask++){
   const key=substE(read[2],{vars:Object.fromEntries(vars.filter((_,i)=>mask&(1<<i)).map(name=>[name,x(actor)])),maps:{},flags:{}}),id=byCell.get(JSON.stringify([read[1].slice(0,-1),key]))
   if(id)projected.add(id)
  }
  const twin=byCell.get(JSON.stringify([read[1].slice(0,-1),read[2]]));if(twin)heads.add(twin)
 }
 for(const id of projected)wanted.add(id)
 const pending=[...wanted],expanded=new Set<string>(),primitiveMaps=new Set<string>(),expandedFlags=new Set<string>()
 while(pending.length){
  const id=pending.shift()!;if(expanded.has(id))continue;expanded.add(id)
  const add=(id:string|undefined)=>{if(id&&!wanted.has(id)){wanted.add(id);pending.push(id)}}
  const read=full.reads.find(r=>r[0]===id)
  if(read?.[1].endsWith('#'))add(byCell.get(JSON.stringify([read[1].slice(0,-1),read[2]])))
  const depend=(value:unknown):void=>{walkOnce(value,(o:any)=>{
   if(o.op==='get'){primitiveMaps.add(o.map);add(byCell.get(JSON.stringify([o.map,o.key])))}
   const name=o.op==='flag'?o.name:o.op==='var'&&o.name.startsWith('?')?o.name.slice(1):undefined
   if(name&&!expandedFlags.has(name)){expandedFlags.add(name);const flag=m.step.flags?.[name];if(flag)depend(flag)}
  })}
  const body=byId.get(id)?.body
  if(body)depend(body)
 }
 // Partition requests and positive-pair requests have separate fair shares.
 // One early head cannot exhaust all slots before a later demanded head.
 // Only proposal discovery uses symbolic post-state cells. Expanding a map
 // write hides Boolean identities behind hundreds of guard atoms; all emitted
 // witnesses are still proved against the original expanded declarations.
 const preDecls=new Map(decls.filter(d=>!d.map.endsWith('#')).map(d=>[d.map,d]))
 const postMaps=Object.fromEntries(Object.keys(m.maps??{}).map(map=>[map,(key:E)=>({op:'get' as const,map:`${map}#`,key})]))
 const postVars=Object.fromEntries(Object.keys(m.state).map(name=>[name,{op:'var' as const,name:`${name}#`}]))
 const proposalDecls=decls.map(d=>{
  const pre=d.map.endsWith('#')?preDecls.get(d.map.slice(0,-1)):undefined
  return pre&&pre.key===d.key&&pre.j===d.j&&pre.lo===d.lo&&pre.base===d.base?{...d,body:substE(pre.body,{vars:postVars,maps:postMaps,flags:{}})}:d
 })
 const proposalCounts=countsForReads(proposalDecls,full.reads)??cs
 // Domain ceilings for requested Boolean counts share the existing 128 slots.
 // They remain witness-backed proposals; no range is admitted syntactically.
 const bounded=(body:E):boolean=>{
  const todo=[body];let seen=0
  while(todo.length){const e=todo.pop()!;if(++seen>256)return false;if(e.op==='const'){if(e.value!==0&&e.value!==1)return false}else if(e.op==='if')todo.push(e.then,e.else);else return false}
  return true
 }
 walkOnce([m,decls,full],(o:any)=>{if(o&&typeof o==='object')for(const value of Object.values(o))if(typeof value==='string')reserved.add(value)})
 const ranges:CountCert['insts']=[];let serial=0
 for(const count of cs)if(wanted.has(count.v)&&bounded(count.body)&&ranges.length<16){
  let wit:string;do{wit=`range$${serial++}`}while(reserved.has(wit));reserved.add(wit)
  ranges.push({wit,below:count.below,terms:[[1,count.v]],unit:-1})
  const read=full.reads.find(r=>r[0]===count.v),pre=read?.[1].endsWith('#')?preDecls.get(read[1].slice(0,-1)):undefined
  let fields=false;if(pre)walkOnce(pre.body,(o:any)=>{if(o.op==='<'&&o.a.op==='get'&&o.b.op==='get')fields=true})
  if(fields&&ranges.length<16){do{wit=`range$${serial++}`}while(reserved.has(wit));reserved.add(wit);ranges.push({wit,below:count.below,terms:[[1,count.v]],unit:0})}
 }
 const proposed=[...ranges,...proposeCountDemand(proposalCounts,wanted,{pairs:[],maxFacts:64-ranges.length,reserved})]
 for(const q of proposed)reserved.add(q.wit)
 const carriedView=(e:E):E|undefined=>{
  if(e.op==='get')return e
  if(e.op!=='if'||e.then.op!=='const'||e.then.value!==1||e.else.op!=='const'||e.else.value!==0)return undefined
  const c=e.c
  if(c.op==='='){if(c.a.op==='get'&&c.b.op==='const'&&c.b.value===1)return c.a;if(c.b.op==='get'&&c.a.op==='const'&&c.a.value===1)return c.b}
  if(c.op==='<='&&c.a.op==='const'&&c.a.value===1&&c.b.op==='get'||c.op==='<'&&c.a.op==='const'&&c.a.value===0&&c.b.op==='get')return c.b
  return undefined
 }
 const carried=cs.filter(c=>{const view=carriedView(c.body);return view?.op==='get'&&(wanted.has(c.v)||primitiveMaps.has(view.map))&&(m.inputMaps??[]).includes(view.map)}),pairs=[...heads].flatMap(head=>carried.filter(c=>c.v!==head).map(c=>[head,c.v] as const))
 const share=Math.max(1,Math.floor((128-proposed.length)/Math.max(1,pairs.length)))
 for(const pair of pairs){
  if(proposed.length>=128)break
  const batch=proposeCountDemand(proposalCounts,new Set([...pair,...projected]),{pairs:[pair],partitions:false,maxFacts:Math.min(share,128-proposed.length),reserved})
  for(const q of batch){reserved.add(q.wit);proposed.push(q)}
 }
 if(!proposed.length){const frames=proposeWriteCountFrames(m,decls,full,wanted);return frames.length?{reads:full.reads,insts:[...frames,...full.insts]}:full}
 const key=(q:CountCert['insts'][number])=>JSON.stringify({below:q.below,unit:q.unit,terms:[...q.terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0])}),seen=new Set<string>(),structured:CountCert['insts']=[]
 for(const q of [...proposed,...full.insts.filter(q=>q.terms.length>=3)]){
  const id=key(q);if(seen.has(id))continue;seen.add(id);structured.push(q);if(structured.length===128)break
 }
 const merged={reads:full.reads,insts:[...full.insts.filter(q=>q.terms.length<3),...structured]},frames=proposeWriteCountFrames(m,decls,merged,wanted)
 return frames.length?{reads:merged.reads,insts:[...frames,...merged.insts]}:merged
}
export function focusCountCert(m: Machine, decls: CountDecl[], full: Pick<CountCert,'reads'|'insts'>, options: {carried?: string, structural?: boolean, frames?: boolean, algebraic?: boolean, requestFrames?: boolean, copyFrames?: boolean, targets?: E[], claim?: C} = {}): Pick<CountCert,'reads'|'insts'> {
  const cs=countsForReads(decls,full.reads)
  if(!cs) return {reads:full.reads,insts:[]}
  const inputs=new Set(m.inputMaps??[]), text=(e:unknown)=>JSON.stringify(e)
  const bodies=new Map(cs.map(c=>[c.v,substE(c.body,{vars:{[c.key]:x('$member')},maps:{},flags:{}})]))
  const indicator=(e:E):E=> e.op==='if'&&e.then.op==='const'&&e.then.value===1&&e.else.op==='const'&&e.else.value===0 ? member(e.c)??e : e
  const predicate=(e:E):C|undefined=> e.op==='if'&&e.then.op==='const'&&e.then.value===1&&e.else.op==='const'&&e.else.value===0 ? e.c : e.op==='get' ? {op:'=',a:e,b:{op:'const',value:1}} : undefined
  const conjuncts=(c:C):string[]=>c.op==='and'?c.xs.flatMap(conjuncts):[text(c)]
  // A carried set's membership flag identifies the stored view it is a subset
  // of. Do not compare it with every unrelated row merely because the bound fits.
  const member=(c:C):E|undefined=>{
    if(c.op==='='&&c.a.op==='get'&&c.b.op==='const'&&c.b.value===1)return c.a
    if(c.op==='='&&c.b.op==='get'&&c.a.op==='const'&&c.a.value===1)return c.b
    if(c.op==='<'&&c.a.op==='const'&&c.a.value===0&&c.b.op==='get')return c.b
    if(c.op==='<='&&c.a.op==='const'&&c.a.value===1&&c.b.op==='get')return c.b
    return undefined
  }
  const views=new Map<string,Set<string>>()
  for(const q of Object.values(m.step.flags??{}))if(q.op==='all'&&!q.keys?.length){
    const c=substC(q.c,{vars:{[q.key]:x('$member')},maps:{},flags:{}})
    if(c.op!=='or'||c.xs.length!==2)continue
    const a=c.xs[0]!.op==='not'?c.xs[0]!.x:undefined,b=c.xs[1]!
    const src=a&&member(a),view=member(b)
    if(src?.op!=='get'||!inputs.has(src.map)||!view)continue
    const got=views.get(src.map)??new Set<string>();got.add(text(view));views.set(src.map,got)
  }
  const stored=new Set<string>()
  for(const [id,map] of full.reads) {
    const d=decls.find(d=>d.map===map)
    if(!d||map.endsWith('#')) continue
    let request=false
    walkOnce([d.below,d.body],(o:any)=>{if(o.op==='get'&&inputs.has(o.map)||o.op==='var'&&m.inputs.includes(o.name)&&![d.j,d.lo,d.key].includes(o.name))request=true})
    if(!request) stored.add(id)
  }
  // Reserve existing slots for disjoint-union bounds: a prefix of partition
  // identities must not starve the five-term family that uses those identities.
  const algebraicSeen=new Set<string>()
  const eligible=options.algebraic?full.insts.filter(q=>{
    if(q.unit!==0||q.terms.length<3||q.terms.length>5||!q.terms.every(([k])=>Math.abs(k)===1))return false
    const id=text({below:q.below,unit:q.unit,terms:[...q.terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0])})
    if(algebraicSeen.has(id))return false;algebraicSeen.add(id);return true
  }):[]
  const unionPriority=(q:CountCert['insts'][number]):number=>{
    const positive=q.terms.filter(([k])=>k===1).map(([,id])=>id)
    const post=positive.some(id=>full.reads.some(r=>r[0]===id&&r[1].endsWith('#')))
    const carried=positive.some(id=>{const b=bodies.get(id),e=b&&indicator(b);return e?.op==='get'&&inputs.has(e.map)&&(!options.carried||e.map===options.carried)})
    return post&&carried?(q.terms.filter(([k])=>k===-1).every(([,id])=>stored.has(id))?2:1):0
  }
  const unions=eligible.filter(q=>q.terms.length===5).sort((a,b)=>unionPriority(b)-unionPriority(a)).slice(0,8)
  const regions=new Set(unions.flatMap(q=>q.terms.filter(([k])=>k===-1).map(([,id])=>id)))
  const requestSizes=new Set([...bodies].filter(([,b])=>{const e=indicator(b);return e.op==='get'&&inputs.has(e.map)}).map(([id])=>id))
  const overlap=(q:CountCert['insts'][number])=>q.terms.filter(([,id])=>regions.has(id)).length
  // Prioritize actual pointwise Boolean identities, not every triple that
  // happens to mention an input size. This only ranks untrusted proposals.
  const booleanIdentity=(q:CountCert['insts'][number]):boolean=>{
    const ps=q.terms.map(([,id])=>{const b=bodies.get(id);return b&&predicate(b)})
    if(ps.some(p=>!p))return false
    const atoms=new Map<string,number>(),atom=(c:C)=>text(member(c)??c)
    const visit=(c:C):void=>{if(c.op==='and'||c.op==='or')c.xs.forEach(visit);else if(c.op==='not')visit(c.x);else if(!atoms.has(atom(c)))atoms.set(atom(c),atoms.size)}
    ps.forEach(p=>visit(p!));if(atoms.size>8)return false
    const value=(c:C,bits:number):boolean=>c.op==='and'?c.xs.every(p=>value(p,bits)):c.op==='or'?c.xs.some(p=>value(p,bits)):c.op==='not'?!value(c.x,bits):!!(bits&(1<<atoms.get(atom(c))!))
    for(let bits=0;bits<1<<atoms.size;bits++)if(q.terms.reduce((sum,[k],i)=>sum+k*(value(ps[i]!,bits)?1:0),0)!==0)return false
    return true
  }
  const identityPriority=(q:CountCert['insts'][number])=>(booleanIdentity(q)?q.terms.length===3?200:100:0)+overlap(q)+(q.terms.some(([,id])=>requestSizes.has(id))?10:0)
  const identities=eligible.filter(q=>q.terms.length!==5).map(q=>({q,rank:identityPriority(q)})).sort((a,b)=>b.rank-a.rank).map(({q})=>q)
  const algebraic=new Set([...unions,...identities.slice(0,16-unions.length)])
  const insts=full.insts.filter(q=>{
    if(options.frames&&q.unit===0&&q.terms.length===3){
      const ps=q.terms.filter(([k])=>k===1).map(([,v])=>v),ns=q.terms.filter(([k])=>k===-1).map(([,v])=>v)
      const cover=ns.length===1?bodies.get(ns[0]!):undefined,view=cover&&indicator(cover)
      if(ps.length===2&&view?.op==='get'&&stored.has(ns[0]!))for(const id of ps){
        const post=full.reads.some(r=>r[0]===id&&r[1].endsWith('#')),other=bodies.get(ps.find(p=>p!==id)!),source=other&&indicator(other)
        if(!post||source?.op!=='get'||!inputs.has(source.map))continue
        let present=false;walkOnce(bodies.get(id),(o:any)=>{if(o.op==='get'&&text(o)===text(view))present=true})
        if(present)return true
      }
    }
    if(algebraic.has(q))return true
    if(q.unit!==0||q.terms.length!==2) return false
    const positive=q.terms.find(([n])=>n===1)?.[1], negative=q.terms.find(([n])=>n===-1)?.[1]
    if(!positive||!negative) return false
    const a=bodies.get(positive),b=bodies.get(negative)
    if(!a||!b) return false
    if(text(indicator(a))===text(indicator(b))) return true
    if(options.algebraic&&text(indicator(a))===text(indicator(b)))return true
    const pa=predicate(a),pb=predicate(b)
    if(pa&&pb) {
      const have=new Set(conjuncts(pa)),need=new Set(conjuncts(pb))
      if(have.size===need.size&&[...need].every(p=>have.has(p)))return true
      if((options.structural!==false||options.frames&&full.reads.some(r=>r[0]===positive&&r[1].endsWith('#'))&&full.reads.some(r=>r[0]===negative&&r[1].endsWith('#')))&&[...need].every(p=>have.has(p)))return true
    }
    if(options.frames&&stored.has(negative)&&full.reads.some(r=>r[0]===positive&&r[1].endsWith('#'))){
      const members=(c:C):E[]=>c.op==='and'?c.xs.flatMap(members):member(c)?[member(c)!]:[]
      const covers=pb?members(pb):[],direct=indicator(b);if(direct.op==='get')covers.push(direct)
      let present=false
      if(covers.length)walkOnce(a,(o:any)=>{if(o.op==='get'&&covers.some(c=>text(o)===text(c)))present=true})
      if(present)return true
    }
    const source=indicator(a)
    if(source.op!=='get'||!inputs.has(source.map)||options.carried&&source.map!==options.carried)return false
    if(options.targets?.length){
      const targetNames=new Set(options.targets.flatMap(t=>t.op==='var'?[t.name]:[]));let relevant=false
      walkOnce(b,(o:any)=>{if(o.op==='var'&&targetNames.has(o.name))relevant=true})
      if(!relevant)return false
    }
    const view=views.get(source.map)
    if(!view?.size)return stored.has(negative)
    let matches=false
    walkOnce(b,(o:any)=>{if(o.op==='get'&&view.has(text(o)))matches=true})
    return matches
  })
  if(options.frames||options.requestFrames||options.copyFrames){
    const used=new Set([...m.inputs,...m.params,...Object.keys(m.state),...full.insts.map(i=>i.wit),...full.reads.map(r=>r[0])])
    walkOnce(cs,(o:any)=>{if(o.op==='var')used.add(o.name)})
    let serial=0
    const add=(terms:[number,string][],below:E)=>{
      if(insts.some(i=>i.unit===0&&JSON.stringify(i.terms)===JSON.stringify(terms)))return
      let wit:string;do{wit=`frame$${serial++}`}while(used.has(wit));used.add(wit)
      insts.push({wit,below,terms,unit:0})
    }
    const byId=new Map(cs.map(c=>[c.v,c])),afters=full.reads.filter(r=>r[1].endsWith('#')).slice(0,16)
    if(options.copyFrames){
      // Share the existing cross-row cap between result counts. Prefer the
      // machine's input keys over unrelated law keys and setup constants.
      const rank=(key:E):number=>{
        const names=new Set<string>();walkOnce(key,(o:any)=>{if(o.op==='var')names.add(o.name)})
        return names.size&&[...names].every(name=>m.inputs.includes(name))?Math.min(...[...names].map(name=>m.inputs.indexOf(name))):[...names].some(name=>m.inputs.includes(name))?100:200
      }
      const pools=afters.flatMap(after=>{
        const c=byId.get(after[0]);if(!c)return []
        const before=full.reads.filter(old=>old[1]===after[1].slice(0,-1)&&text(old[2])!==text(after[2])&&text(byId.get(old[0])?.below)===text(c.below)).sort((a,b)=>rank(a[2])-rank(b[2]))
        return [{after,c,before}]
      })
      let copies=0
      for(let row=0;copies<16;row++){
        let found=false
        for(const pool of pools){
          const before=pool.before[row];if(!before)continue
          found=true;add([[1,pool.after[0]],[-1,before[0]]],pool.c.below);add([[1,before[0]],[-1,pool.after[0]]],pool.c.below)
          if(++copies>=16)break
        }
        if(!found)break
      }
    }
    for(const after of afters){
      const c=byId.get(after[0]);if(!c)continue
      if(options.frames)add([[1,after[0]]],c.below)
      const before=full.reads.find(r=>r[1]===after[1].slice(0,-1)&&text(r[2])===text(after[2]))
      if(options.frames&&before&&text(byId.get(before[0])?.below)===text(c.below)){
        add([[1,after[0]],[-1,before[0]]],c.below)
        add([[1,before[0]],[-1,after[0]]],c.below)
      }
      if(options.requestFrames){
        const shape=(v:unknown):unknown=>Array.isArray(v)?v.map(shape):v&&typeof v==='object'?(v as any).op==='get'?{op:'cell'}:(v as any).op==='var'?{op:'key'}:Object.fromEntries(Object.entries(v).map(([k,v])=>[k,shape(v)])):v
        const beforeDecl=decls.find(d=>d.map===after[1].slice(0,-1))
        if(beforeDecl)for(const read of full.reads){
          if(read[1].endsWith('#'))continue
          const d=decls.find(d=>d.map===read[1]),count=byId.get(read[0]);if(!d||!count||text(count.below)!==text(c.below))continue
          let carried=false
          walkOnce(d.body,(o:any)=>{if(o.op==='get'&&inputs.has(o.map)&&(!options.carried||o.map===options.carried))carried=true})
          if(!carried||text(shape(indicator(d.body)))!==text(shape(indicator(beforeDecl.body))))continue
          add([[1,after[0]],[-1,read[0]]],c.below)
          add([[1,read[0]],[-1,after[0]]],c.below)
        }
      }
    }
  }
  const focused={reads:full.reads,insts}
  return options.algebraic&&options.claim?demandCountCert(m,decls,focused,options.claim):focused
}
