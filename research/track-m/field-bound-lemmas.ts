// Checked field-ceiling cuts suggested by a counted predicate and a carried
// set's per-member bound. The suggestion is untrusted; every cut is reconstructed
// and the complete result is checked against the original counted goal.
import {type C,type Machine,same,walkOnce,x} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Goal,type Path,type Tree,canon,check,linear,substC,substE,truth} from '../../kernel/kernel.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {refuteFast,sub} from '../../core/solver.ts'
import {liftCountProxies} from './lift-count-proxies.ts'
import {piecesAt,walkLive} from './live-dependencies.ts'
import {carriedCase} from './carried-case.ts'
import {foldPath} from './fold-path.ts'
import {booleanCore} from './boolean-core.ts'
import {proveRowCases,rowPairs} from './row-cases.ts'
import {activeCarried} from './action-guard.ts'
import {frameLemmas} from './frame-lemmas.ts'
import {atPoint,clock,grow,rowsAt,widen,withDeadline} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>
export function fieldBounds(m:Machine,ds:CountDecl[],cert:Proposal):C[]{
 const key=x('$member'),bounds:{a:unknown,b:any,guard:C}[]=[]
 for(const [name,q] of Object.entries(m.step.flags??{}))if(q.op==='all')walkOnce(substC(q.c,{vars:{[q.key]:key},maps:{},flags:{}}),(c:any)=>{
  const next=c.op==='<'&&c.b?.op==='add'&&c.b.b.op==='const'&&c.b.b.value===1?c.b.a:undefined
  const pairs=c.op==='='?[[c.a,c.b],[c.b,c.a]]:c.op==='<='?[[c.a,c.b]]:next?[[c.a,next]]:[]
  for(const [left,right]of pairs)if(right&&left?.op==='get'&&JSON.stringify(left).includes('"name":"$member"')&&!JSON.stringify(right).includes('"name":"$member"'))bounds.push({a:left,b:right,guard:{op:'=',a:x(`?${name}`),b:{op:'const',value:1}}})
 })
 const out:C[]=[],seen=new Set<string>(),pre=new Set(cert.reads.filter(r=>!r[1].endsWith('#')).map(r=>r[0]))
 for(const c of countsForReads(ds,cert.reads)??[])if(pre.has(c.v))walkOnce(substE(c.body,{vars:{[c.key]:key},maps:{},flags:{}}),(p:any)=>{
  if(p.op!=='<'||p.a?.op!=='get'||JSON.stringify(p.b).includes('"name":"$member"'))return
  for(const b of bounds)if(JSON.stringify(b.a)===JSON.stringify(p.a)){
   const guard:C=p.b.op==='get'?{op:'and',xs:[b.guard,{op:'<',a:p.b.key,b:c.below}]}:b.guard
   const candidate:C={op:'<=',a:{op:'if',c:guard,then:p.b,else:{op:'const',value:0}},b:b.b},id=JSON.stringify(candidate)
   if(!seen.has(id)){seen.add(id);out.push(candidate)}
  }
 })
 const targets=new Set<string>(),twins=cert.reads.filter(r=>r[1].endsWith('#')).map(([v,map,key])=>[v,map.slice(0,-1),key] as [string,string,typeof key])
 for(const c of countsForReads(ds,twins)??[])walkOnce(substE(c.body,{vars:{[c.key]:key},maps:{},flags:{}}),(p:any)=>{
  if(p.op==='<'&&bounds.some(b=>JSON.stringify(b.a)===JSON.stringify(p.a)))targets.add(JSON.stringify(p.b))
 })
 const focused=out.filter(c=>c.op==='<='&&c.a.op==='if'&&targets.has(JSON.stringify(c.a.then)))
 return (focused.length?focused:out).slice(0,4)
}
export function fieldBoundLemmas(m:Machine,ds:CountDecl[],g:Goal,cert:Proposal,until:number,trace:object[],onModel?:(goal:Goal,witness:Record<string,number>)=>boolean,root:Path=new Map(),options:{splitRows?:boolean}={}):Tree|undefined{
 const seq=modelSequence(root),ctx:C[]=[],path:Path=new Map(root),lemmas:{split:Record<string,number>,no:Tree}[]=[]
 const rowPlan=options.splitRows!==false&&process.env.LAB_ROW_SPLIT==='1'?rowPairs(m,cert):[]
 let arithmetic:Tree|undefined
 const postMaps=new Set(cert.reads.filter(r=>r[1].endsWith('#')).map(r=>r[1])),postIds=new Set(cert.reads.filter(r=>r[1].endsWith('#')).map(r=>r[0]))
 const base=g.hyps.slice(0,g.hyps.length-cert.insts.length).flatMap(c=>piecesAt(c,root)).filter(c=>{let post=false;walkLive(c,root,(o:any)=>{if(o.op==='get'&&postMaps.has(o.map)||o.op==='var'&&postIds.has(o.name))post=true});return !post})
 const cs=new Map((countsForReads(ds,cert.reads)??[]).map(c=>[c.v,{...c,body:substE(c.body,{vars:{[c.key]:x('$member')},maps:{},flags:{}})}]))
 const view=(e:any):any=>{
  if(e.op!=='if'||e.then.op!=='const'||e.then.value!==1||e.else.op!=='const'||e.else.value!==0)return e
  const c=e.c
  if(c.op==='='&&c.a.op==='get'&&c.b.op==='const'&&c.b.value===1)return c.a
  if(c.op==='='&&c.b.op==='get'&&c.a.op==='const'&&c.a.value===1)return c.b
  if(c.op==='<='&&c.a.op==='const'&&c.a.value===1&&c.b.op==='get')return c.b
  if(c.op==='<'&&c.a.op==='const'&&c.a.value===0&&c.b.op==='get')return c.b
  return e
 }
 const signature=(e:any):string|undefined=>{
  const pred=e.op==='get'?{op:'=',a:e,b:{op:'const',value:1}}:e.op==='if'&&e.then.op==='const'&&e.then.value===1&&e.else.op==='const'&&e.else.value===0?e.c:undefined
  const atoms=(c:any):string[]=>c.op==='and'?c.xs.flatMap(atoms):[JSON.stringify(c)]
  return pred?JSON.stringify([...new Set(atoms(pred))].sort()):undefined
 }
 const narrow=(good:Extract<C,{a:unknown}>)=>{
  const keep=cert.insts.flatMap((inst,i)=>{
   if(inst.unit!==0||inst.terms.length!==2||inst.terms.some(t=>postIds.has(t[1])))return []
   const positive=inst.terms.find(t=>t[0]===1),negative=inst.terms.find(t=>t[0]===-1),a=positive&&cs.get(positive[1]),b=negative&&cs.get(negative[1])
   if(!a||!b)return []
   const as=signature(a.body),bs=signature(b.body),same=as!==undefined&&as===bs,input=(view(a.body) as any).op==='get'&&(m.inputMaps??[]).includes((view(a.body) as any).map)
   let target=false;walkOnce(b.body,(o:any)=>{if(o.op==='<'&&JSON.stringify(o.b)===JSON.stringify(good.a.op==='if'?good.a.then:good.a))target=true})
   return same||input&&target?[i]:[]
  })
  const wanted=new Set(keep.map(i=>cert.insts[i]!.wit)),all=new Set(cert.insts.map(i=>i.wit))
  const weaken=(c:C):C|undefined=>{
   if(c.op==='and'){const xs=c.xs.flatMap(c=>{const n=weaken(c);return n?[n]:[]});return xs.length?{op:'and',xs}:undefined}
   let other=false,own=false;walkLive(c,root,(o:any)=>{if(o.op==='var'&&all.has(o.name)){if(wanted.has(o.name))own=true;else other=true}})
   return other&&!own?undefined:c
  }
  return [...base.flatMap(c=>{const n=weaken(c);return n?[n]:[]}),...keep.map(i=>g.hyps[g.hyps.length-cert.insts.length+i]!)]
 }
 const solve=(goal:Goal,limit:number,finish=false):Tree|undefined=>{
  const budget=finish?Math.min(limit,Number(process.env.LAB_BOUND_QUERY_MS??limit)):limit,started=clock(),q=seq(goal,Math.min(until,clock()+budget))
  trace.push({stage:'field-query',hyps:goal.hyps.length,ms:Math.round(clock()-started),limit:budget,outcome:'tree'in q?'tree':q.stuck,core:q.core?.length,...(!('tree'in q)&&q.stuck==='sat'?{model:q.witness}:{})})
  if('tree'in q)return q.tree
  if(finish&&q.stuck==='sat'&&q.witness&&onModel?.(goal,q.witness))return undefined
  const reduced=q.why===REFUTED&&q.core?.length?{...goal,hyps:q.core.map(i=>goal.hyps[i]!)}:finish?goal:undefined
  if(!reduced)return undefined
  if(process.env.LAB_CORE_TRACE==='1'&&q.core?.length===6)trace.push({stage:'small-core',goal:reduced,path:[...root]})
  const before=atPoint.on;atPoint.on=!(root.size>0&&!finish&&q.core&&q.core.length<=8)
  try{
   const deadline=Math.min(until,clock()+(finish?Math.max(0,until-clock()):250))
   if(!finish&&root.size>0&&q.core&&q.core.length<=8){
    const start=clock(),folded=foldPath(reduced,root),out=grow(folded.goal,root,{nodes:0,until:Math.min(deadline,clock()+25),units:false})
    const lifted='tree'in out?withDeadline(deadline,()=>widen(folded.goal,reduced,out.tree,folded.opaque,root,root)):undefined
    trace.push({stage:'folded-core',aliases:Object.keys(folded.opaque).length,ms:Math.round(clock()-start),sourceChecked:'tree'in out,lifted:!!lifted})
    if(lifted)return widen(reduced,goal,lifted,{},root,root)
    const direct=booleanCore(reduced,root,new Set(cert.insts.map(i=>i.wit)),deadline,trace)
    if(direct)return widen(reduced,goal,direct,{},root,root)
   }
   const split=!finish&&root.size>0&&q.core&&q.core.length<=8?carriedCase(reduced,root,m.inputMaps??[],new Set(cert.insts.map(i=>i.wit)),deadline,trace):undefined
   if(split)return widen(reduced,goal,split,{},root,root)
   const out=grow(reduced,root,{nodes:0,until:deadline,units:root.size>0&&!!q.core&&q.core.length<=8})
   return 'tree'in out?widen(reduced,goal,out.tree,{},root,root):undefined
  }finally{atPoint.on=before}
 }
 for(let i=0;i<cert.reads.length;i++)for(let j=i+1;j<cert.reads.length;j++){
  const a=cert.reads[i]!,b=cert.reads[j]!
  if(a[1]!==b[1]||truth({op:'=',a:a[2],b:b[2]},root)!==true)continue
  for(const [left,right]of [[a[0],b[0]],[b[0],a[0]]]){
   if(clock()>=until)break
   const split=sub({[left!]:1},{[right!]:1});if(path.get(canon(split))?.holds===true)continue
   const noPath=new Map(path).set(canon(split),{lin:split,holds:false}),begun=clock()
   trace.push({stage:'read-alias-start',left,right})
   const bindings=g.hyps.filter(c=>c.op==='='&&[[c.a,c.b],[c.b,c.a]].some(([v,e])=>v?.op==='var'&&[left,right].includes(v.name)&&e?.op==='get'&&e.map===a[1]))
   if(bindings.length!==2)continue
   const small:Goal={name:'equal-key count reads',hyps:bindings},out=refuteFast(rowsAt(small,noPath),256)
   const local:Tree|undefined=out?.kind==='refuted'?{leaf:out.steps}:undefined
   const no=local&&check(small,local,noPath)?liftCountProxies(small,g,local,[],noPath,noPath):undefined,checked=!!no&&check(g,no,noPath)
   trace.push({stage:'read-alias',left,right,ms:Math.round(clock()-begun),checked})
   if(checked&&no){lemmas.push({split,no});ctx.push({op:'<=',a:x(left!),b:x(right!)});path.set(canon(split),{lin:split,holds:true})}
  }
 }
 for(const good of fieldBounds(m,ds,cert)){
  if(good.op!=='<='||clock()>=until)break
  if(truth(good,path)===true)continue
  const a=linear(good.a,root),b=linear(good.b,root);if(!a||!b)continue
  const split=sub(a,b),noPath=new Map(path).set(canon(split),{lin:split,holds:false}),start=clock()
  const facts=narrow(good),part={...g,hyps:[...facts,...ctx,{op:'not' as const,x:good}]},proof=solve(part,250),lifted=proof&&widen(part,g,proof,{},root,noPath),no=lifted&&check(g,lifted,noPath)?lifted:undefined
  trace.push({stage:'field-bound',bound:good,ms:Math.round(clock()-start),proved:!!no,checked:!!no})
  if(no){lemmas.push({split,no});ctx.push(good);path.set(canon(split),{lin:split,holds:true})}
 }
 if(process.env.LAB_COUNT_LEMMAS==='1'){
  const carriedMaps=activeCarried(m,root),countMaps=new Set(cert.reads.map(r=>r[1])),countIds=new Set(cert.reads.map(r=>r[0])),wits=new Set(cert.insts.map(i=>i.wit)),raw=g.hyps.slice(0,g.hyps.length-cert.insts.length)
  const pieces=(c:C)=>piecesAt(c,root)
  const selected=(inst:Proposal['insts'][number]):boolean=>{
   if(inst.unit!==0||rowPlan.length&&inst.terms.some(([,id])=>postIds.has(id)))return false
   const carried=inst.terms.some(([k,id])=>{const c=cs.get(id),b=c&&view(c.body);return k===1&&b?.op==='get'&&carriedMaps.has(b.map)})
   if(inst.terms.length===3||inst.terms.length===5&&carried)return true
   if(inst.terms.length!==2)return false
   const [a,b]=inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id))
   return carried||process.env.LAB_POST_SUBSETS==='1'&&!!a&&!!b&&a[1].endsWith('#')&&!b[1].endsWith('#')||!!a&&!!b&&a[1].replace(/#$/,'')===b[1].replace(/#$/,'')&&a[1].endsWith('#')!==b[1].endsWith('#')&&JSON.stringify(a[2])===JSON.stringify(b[2])
  }
  for(const [index,inst] of cert.insts.entries()){
   if(clock()>=until)break
   if(!selected(inst))continue
   const h=g.hyps[raw.length+index];if(h?.op!=='or'||h.xs[0]?.op!=='<=')continue
   const good=h.xs[0];if(truth(good,path)===true)continue
   const split=Object.fromEntries(inst.terms.map(([n,v])=>[v,n])),noPath=new Map(path).set(canon(split),{lin:split,holds:false})
   const relevant=raw.flatMap(c=>pieces(c)).filter(c=>{let skip=false;walkLive(c,root,(o:any)=>{if(o.op==='get'&&countMaps.has(o.map)||o.op==='var'&&(countIds.has(o.name)||wits.has(o.name)&&o.name!==inst.wit))skip=true});return !skip})
   const part={...g,hyps:[...relevant,...ctx,h,{op:'not' as const,x:good}]},started=clock(),proof=solve(part,150),lifted=proof&&widen(part,g,proof,{},root,noPath),no=lifted&&check(g,lifted,noPath)?lifted:undefined
   trace.push({stage:'count-lemma',index,arity:inst.terms.length,terms:inst.terms,ms:Math.round(clock()-started),checked:!!no})
   if(no){lemmas.push({split,no});ctx.push(good);path.set(canon(split),{lin:split,holds:true})}
  }
  const pure=(c:C):boolean=>{let skip=false;walkLive(c,root,(o:any)=>{if(o.op==='get'||o.op==='var'&&wits.has(o.name))skip=true});return !skip}
  const maps=Object.fromEntries([...countMaps].map(map=>[map,(key:any)=>{const r=cert.reads.find(r=>r[1]===map&&JSON.stringify(r[2])===JSON.stringify(key));return r?x(r[0]):{op:'get' as const,map,key}}]))
  const flags=Object.fromEntries(Object.keys(m.step.flags??{}).map(name=>[name,{op:'flag' as const,name}]))
  const numeric:Goal={...g,hyps:[...raw.map(c=>substC(c,{vars:{},maps,flags})).flatMap(c=>pieces(c)).filter(pure),...ctx.filter(pure)]},begun=clock(),q=seq(numeric,Math.min(until,clock()+200))
  trace.push({stage:'count-arithmetic',hyps:numeric.hyps.length,ms:Math.round(clock()-begun),outcome:'tree'in q?'tree':q.stuck,core:q.core?.length,...(!('tree'in q)&&q.stuck==='sat'?{model:q.witness}:{})})
  let proof='tree'in q?q.tree:undefined
  if(!proof&&!('tree'in q)&&q.why===REFUTED&&q.core?.length){
   const reduced={...numeric,hyps:q.core.map(i=>numeric.hyps[i]!)},out=grow(reduced,root,{nodes:0,until:Math.min(until,clock()+400),units:false})
   if('tree'in out)proof=widen(reduced,numeric,out.tree,{},root,root)
  }
  const lifted=proof&&liftCountProxies(numeric,g,proof,cert.reads,root,path,event=>trace.push({stage:'count-transport',...event}))
  if(lifted&&check(g,lifted,path))arithmetic=lifted
 }
 if(clock()>=until)return undefined
 const part={...g,hyps:[...g.hyps,...ctx]},start=clock()
 let tree=arithmetic
 if(!tree&&rowPlan.length){
  trace.push({stage:'row-pairs',pairs:rowPlan})
  tree=proveRowCases(g,path,rowPlan,until,(branch,end)=>{
   if(rowPlan.every(([a,b])=>truth(same(a,b),branch)===false)){
    const frame=frameLemmas(g,cert,Math.min(end,clock()+500),trace,branch,{stopAfterFailed:2,boolean:true})
    trace.push({stage:'unchanged-row-frame',checked:!!frame})
    if(frame)return frame
   }
   return fieldBoundLemmas(m,ds,g,cert,end,trace,onModel,branch,{splitRows:false})
  },e=>trace.push(e))
 }
 if(!tree){const proof=solve(part,Math.max(150,until-clock()-200),true);tree=proof&&widen(part,g,proof,{},root,path)}
 trace.push({stage:'field-bound-conclusion',facts:lemmas.length,ms:Math.round(clock()-start),proved:!!tree})
 if(!tree)return undefined
 for(const {split,no} of lemmas.reverse())tree={split,yes:tree,no}
 return check(g,tree,root)?tree:undefined
}
