// Research-only Section 5 falsification. No default prover imports this module.
import {type C,type Machine,x} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Goal,type LemmaCut,type Path,type Tree,canon,canonFlip,check,leafConstraintsReusing,lemmaPath,linear,substC,substE,truth} from '../../kernel/kernel.ts'
import {clock,grow,pastWall,widen,withDeadline} from '../../kernel/prove.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {scale,sub} from '../../core/solver.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {fieldBounds,fieldBoundLemmas,countBindingsAt,emptyCountCandidate} from '../../core/count-recovery/field-bound-lemmas.ts'
import {preStateCountSource} from '../../core/count-recovery/pre-state-source.ts'
import {booleanCore} from '../../core/count-recovery/boolean-core.ts'
import {piecesAt,sourceScalarContext,walkLive} from '../../core/count-recovery/live-dependencies.ts'
import {activeCarried} from '../../core/count-recovery/action-guard.ts'
import {proveNaturalCases} from '../../core/count-recovery/natural-cases.ts'
import {liftCountProxies} from '../../core/count-recovery/lift-count-proxies.ts'

type Packet=Pick<CountCert,'reads'|'insts'>
type Saved={lemma:LemmaCut,good:C,index?:number}
const put=(path:Path,lin:Record<string,number>,holds:boolean):Path=>new Map(path).set(canon(lin),{lin,holds})
const flip=(lin:Record<string,number>)=>{const out=scale(lin,-1);out['1']=(out['1']??0)+1;return out}
const proofPath=(lemma:Pick<LemmaCut,'when'|'cut'>):Path=>{
 const path:Path=new Map();let duplicate=0
 for(const atom of [{lin:lemma.cut,holds:false},...lemma.when.map(lin=>({lin,holds:true}))]){
  const id=canon(atom.lin);path.set(path.has(id)?`@${duplicate++}`:id,atom)
 }
 return path
}
export function deriveClosure(m:Machine,ds:CountDecl[],g:Goal,cert:Packet,root:Path,until:number,trace:any[]){
 const start=clock(),saved:Saved[]=[],raw=g.hyps.slice(0,-cert.insts.length),postIds=new Set(cert.reads.filter(r=>r[1].endsWith('#')).map(r=>r[0]))
 const countIds=new Set(cert.reads.map(r=>r[0])),countMaps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(q=>q.wit))
 const alive=()=>clock()<until&&!pastWall(),when=[...root.values()].map(a=>a.holds?a.lin:flip(a.lin))
 const extend=(base:Path,entries=saved)=>lemmaPath(entries.map(s=>s.lemma),base)
 const transport=(from:Goal,to:Goal,tree:Tree,old:Path,next:Path)=>alive()?withDeadline(until,()=>widen(from,to,tree,{},old,next)):undefined
 // The kernel does not permit one lemma to assume another. Inline only already
 // checked prerequisites into each new independent lemma proof.
 const inline=(tree:Tree,from:Path,base:Path,entries=saved):Tree|undefined=>{
  let path=extend(base,entries),out=transport(g,g,tree,from,path)
  for(let i=entries.length-1;out&&i>=0;i--){
   const l=entries[i]!.lemma,prefix=extend(base,entries.slice(0,i)),yesPath=put(prefix,l.cut,true)
   const yes=transport(g,g,out,path,yesPath),no=transport(g,g,l.tree,proofPath(l),put(prefix,l.cut,false))
   out=yes&&no?{split:l.cut,yes,no}:undefined;path=prefix
  }
  return out
 }
 const dependencies=(source:Goal,tree:Tree,path:Path):Saved[]=>{
  const seen=new Set<string>()
  class Observed extends Map<string,{lin:Record<string,number>,holds:boolean}>{
   override get(key:string){seen.add(key);return super.get(key)}
   override has(key:string){seen.add(key);return super.has(key)}
  }
  const visit=(t:Tree,p:Path):void=>{
   if('split'in t){visit(t.yes,put(p,t.split,true));visit(t.no,put(p,t.split,false));return}
   const rows=leafConstraintsReusing(source,new Observed(p)),values=[...p.values()]
   for(const index of [...t.leaf.flatMap(step=>step.kind==='input'?[step.index]:[]),...(t.products??[]).flat()]){
    const src=rows[index]?.src
    if(src&&'atom'in src){const atom=values[src.atom];if(atom){seen.add(canon(atom.lin));seen.add(canonFlip(atom.lin))}}
   }
  }
  visit(tree,path)
  return saved.filter(s=>seen.has(canon(s.lemma.cut))||seen.has(canonFlip(s.lemma.cut)))
 }
 const admit=(good:C,source:Goal,tree:Tree,from:Path,index?:number):boolean=>{
  if(good.op!=='<=')return false
  const a=linear(good.a,root),b=linear(good.b,root);if(!a||!b)return false
  const cut=sub(a,b);if(saved.some(s=>canon(s.lemma.cut)===canon(cut)))return true
  const base=put(root,cut,false),required=dependencies(source,tree,from),target=extend(base,required)
  const full=transport(source,g,tree,from,target)
  const independent=full&&inline(full,target,base,required),lemma:LemmaCut={when,cut,tree:{leaf:[]}}
  const closed=independent&&transport(g,g,independent,base,proofPath(lemma))
  if(!closed||!check(g,closed,proofPath(lemma))){trace.push({stage:'cut-check',index,checked:false});return false}
  lemma.tree=closed;saved.push({lemma,good,index});trace.push({stage:'cut-check',index,checked:true,when:when.length,dependencies:required.length});return true
 }
 // Phase A: the same bounded pre-state source, not a stronger assumption.
 const ceilings=fieldBounds(m,ds,cert,{claim:g.hyps.at(-1),path:root})
 const guardParts=(c:C):C[]=>c.op==='and'?c.xs.flatMap(guardParts):[c]
 const dominates=(strong:C,weak:C):boolean=>{
  if(strong.op!=='<='||weak.op!=='<='||strong.a.op!=='if'||weak.a.op!=='if'||JSON.stringify([strong.a.then,strong.b])!==JSON.stringify([weak.a.then,weak.b]))return false
  const wanted=guardParts(weak.a.c).filter(c=>truth(c,root)!==true).map(c=>JSON.stringify(c))
  const needs=guardParts(strong.a.c).filter(c=>truth(c,root)!==true)
  return needs.every(c=>wanted.includes(JSON.stringify(c)))&&needs.length<wanted.length
 }
 for(const good of ceilings){
  if(!alive())break
  if(good.op!=='<='||truth(good,extend(root))===true)continue
  if(ceilings.some(other=>other!==good&&dominates(other,good)))continue
  const begun=clock(),negative:C={op:'not',x:good},before=preStateCountSource(g,cert,negative,root)
  const events:any[]=[],end=Math.min(until,clock()+250)
  const tree=fieldBoundLemmas(m,ds,before.goal,before.cert,end,events,undefined,root,{deferCheck:true,fieldClaim:negative})
  const a=linear(good.a,root),b=linear(good.b,root),cut=a&&b?sub(a,b):undefined
  const source={...g,hyps:[...g.hyps,negative]},lifted=tree&&transport(before.goal,source,tree,root,root)
  const no=lifted&&cut?transport(source,g,lifted,root,put(root,cut,false)):undefined
  const checked=!!no&&!!cut&&admit(good,g,no,put(root,cut,false))
  trace.push({stage:'phase-a',good,sourceHyps:before.goal.hyps.length,sourceInsts:before.cert.insts.length,ms:clock()-begun,checked,events})
 }
 const view=(e:any):any=>{
  if(e.op!=='if'||e.then.op!=='const'||e.then.value!==1||e.else.op!=='const'||e.else.value!==0)return e
  const c=e.c
  if(c.op==='='&&c.a.op==='get'&&c.b.op==='const'&&c.b.value===1)return c.a
  if(c.op==='='&&c.b.op==='get'&&c.a.op==='const'&&c.a.value===1)return c.b
  if(c.op==='<='&&c.a.op==='const'&&c.a.value===1&&c.b.op==='get')return c.b
  if(c.op==='<'&&c.a.op==='const'&&c.a.value===0&&c.b.op==='get')return c.b
  return e
 }
 const cs=new Map((countsForReads(ds,cert.reads)??[]).map(c=>[c.v,{...c,body:substE(c.body,{vars:{[c.key]:x('$member')},maps:{},flags:{}})}]))
 const carriedMaps=activeCarried(m,root)
 const selected=(inst:Packet['insts'][number]):boolean=>{
  if(inst.unit!==0)return false
  if(emptyCountCandidate(m,cert,inst))return true
  const carried=inst.terms.some(([k,id])=>{const c=cs.get(id),b=c&&view(c.body);return k===1&&b?.op==='get'&&carriedMaps.has(b.map)})
  if(inst.terms.length===3||inst.terms.length===5&&carried)return true
  if(inst.terms.length!==2)return false
  const [a,b]=inst.terms.map(([,id])=>cert.reads.find(r=>r[0]===id))
  const [ca,cb]=inst.terms.map(([,id])=>cs.get(id))
  const alias=!inst.terms.some(([,id])=>postIds.has(id))&&ca&&cb&&JSON.stringify(view(ca.body))===JSON.stringify(view(cb.body))
  const frame=a&&b&&a[1].replace(/#$/,'')===b[1].replace(/#$/,'')&&a[1].endsWith('#')!==b[1].endsWith('#')
  const request=inst.terms.some(([,id])=>postIds.has(id))&&inst.terms.some(([,id])=>{const c=cs.get(id),v=c&&view(c.body);return v?.op==='get'&&(m.inputMaps??[]).includes(v.map)})
  return !!(carried||alias||frame||a&&b&&a[1].endsWith('#')&&b[1].endsWith('#')||request||a&&b&&a[1].endsWith('#')&&!b[1].endsWith('#'))
 }
 const pool=[...cert.insts.entries()].filter(([,q])=>selected(q)),closed=new Set<number>()
 let rounds=0,fixedPoint=false
 while(alive()){
  rounds++;let added=0
  for(const [index,inst]of pool){
   if(!alive())break
   if(closed.has(index))continue
   const path=extend(root),h=g.hyps[raw.length+index]
   if(h?.op!=='or'||h.xs[0]?.op!=='<=')continue
   const good=h.xs[0]
   if(truth(good,path)===true){closed.add(index);continue}
   const negative:C={op:'not',x:good},begun=clock(),end=Math.min(until,clock()+(inst.terms.length===5?150:30))
   const relevant=raw.flatMap(c=>piecesAt(c,path)).filter(c=>{let skip=false;walkLive(c,path,(o:any)=>{if(o.op==='get'&&countMaps.has(o.map)||o.op==='var'&&(countIds.has(o.name)||wits.has(o.name)&&o.name!==inst.wit))skip=true});return !skip})
   const part={...g,hyps:[...relevant,h,negative]},tiny={...g,hyps:[h,negative]}
   const source=inst.terms.length===3&&inst.terms.every(([,id])=>!postIds.has(id))?tiny:sourceScalarContext({name:g.name,hyps:raw},part,new Set([...m.params,...m.inputs,...Object.keys(m.state)]),path)
   const events:any[]=[],point=modelSequence(path)(source,Math.min(end,clock()+8))
   let tree:Tree|undefined='tree'in point?point.tree:undefined
   if(!tree&&!('tree'in point)&&point.stuck!=='sat'&&clock()<end){
    const reduced=point.why===REFUTED&&point.core?.length?{...source,hyps:point.core.map(i=>source.hyps[i]!)}:source
    const proposed=booleanCore(reduced,path,new Set([inst.wit]),end,events,{extended:true,scalarGuards:true,deferCheck:true,model:true})
    tree=proposed&&transport(reduced,source,proposed,path,path)
   }
   const checked=!!tree&&admit(good,source,tree,path,index)
   if(checked){closed.add(index);added++}
   trace.push({stage:'phase-b',round:rounds,index,arity:inst.terms.length,wit:inst.wit,terms:inst.terms,ms:clock()-begun,checked,sourceHyps:source.hyps.length,pointOutcome:'tree'in point?'tree':point.stuck,events})
  }
  trace.push({stage:'round',round:rounds,added,closed:closed.size,remaining:pool.length-closed.size,expired:!alive()})
  if(!added){fixedPoint=alive();break}
 }
 let finalOutcome='not-run',tree:Tree|undefined,numericHyps=0,arithmeticMs=0
 if(alive()){
  const pure=(c:C)=>{let skip=false;walkLive(c,root,(o:any)=>{if(o.op==='get'||o.op==='var'&&wits.has(o.name))skip=true});return !skip}
  const maps=Object.fromEntries([...countMaps].map(map=>[map,(key:any)=>{const r=cert.reads.find(r=>r[1]===map&&JSON.stringify(r[2])===JSON.stringify(key));return r?x(r[0]):{op:'get' as const,map,key}}]))
  const flags=Object.fromEntries(Object.keys(m.step.flags??{}).map(name=>[name,{op:'flag' as const,name}]))
  const numeric={...g,hyps:[...raw.map(c=>substC(c,{vars:{},maps,flags})).flatMap(c=>piecesAt(c,root)).filter(pure),...countBindingsAt(cert.reads,root),...saved.map(s=>s.good).filter(pure)]}
  numericHyps=numeric.hyps.length;const begun=clock(),q=modelSequence(root)(numeric,Math.min(until,clock()+200))
  finalOutcome='tree'in q?'tree':q.stuck
  trace.push({stage:'phase-c-query',outcome:finalOutcome,core:q.core?.length,ms:clock()-begun,...(!('tree'in q)&&q.stuck==='sat'?{model:q.witness}:{})})
  let proof='tree'in q?q.tree:undefined
  if(!proof&&!('tree'in q)&&q.why===REFUTED&&q.core?.length&&alive()){
   const reduced={...numeric,hyps:q.core.map(i=>numeric.hyps[i]!)},out=grow(reduced,root,{nodes:0,until:Math.min(until,clock()+400),units:false})
   if('tree'in out)proof=transport(reduced,numeric,out.tree,root,root)
  }
  if(!proof&&!('tree'in q)&&q.stuck==='unknown'&&alive())proof=proveNaturalCases(numeric,root,Math.min(until,clock()+400),trace,{deferCheck:true})
  const lifted=proof&&liftCountProxies(numeric,g,proof,cert.reads,root,extend(root),e=>trace.push({stage:'count-transport',...e}),{deferCheck:true})
  tree=lifted&&inline(lifted,extend(root),root);arithmeticMs=clock()-begun
 }
 const used=clock()-start,checked=!!tree&&check(g,tree,root)
 return {tree,lemmas:saved.map(s=>s.lemma),indices:saved.flatMap(s=>s.index===undefined?[]:[s.index]),closedIndices:[...closed],pool:pool.length,rounds,fixedPoint,finalOutcome,numericHyps,arithmeticMs,countedMs:used,checked,expired:!alive()}
}
