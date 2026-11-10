// T-9A only: exact live source slices and opaque columns, no production strategy.
import {createHash} from 'node:crypto'
import {type C,type E,type Machine,less,same,x} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Goal,type LemmaCut,type Path,type Tree,canon,canonFlip,check,countHyp,lemmaPath,linear,truth} from '../../kernel/kernel.ts'
import {atPoint,brokenOf,clock,counted,fullRate,fullWork,grow,rowsAt,widen,withDeadline,withWall} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {sub,refuteFast} from '../../core/solver.ts'
import {walkLive} from '../../core/count-recovery/live-dependencies.ts'
import {booleanCore} from '../../core/count-recovery/boolean-core.ts'
import {foldPath} from '../../core/count-recovery/fold-path.ts'
import {proveNaturalCases} from '../../core/count-recovery/natural-cases.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
import {checkConditionalProof,markConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {liftCountProxies} from '../../core/count-recovery/lift-count-proxies.ts'
export type Packet=Pick<CountCert,'reads'|'insts'>
type Bound={op:'<=',a:E,b:E}
type Saved={good:Bound,lemma:LemmaCut,index?:number}
export type Context={m:Machine,ds:CountDecl[],g:Goal,cert:Packet,scope:Path,numeric:Goal,available:Saved[],saved:Saved[],q:any,source:(p:Path,w?:string)=>C[],scopesFor:(i:number)=>Path[],numericFor:(p:Path,extra:Saved[])=>Goal}
const hash=(x:unknown)=>createHash('sha256').update(JSON.stringify(x)).digest('hex')
const put=(p:Path,lin:Record<string,number>,holds:boolean):Path=>new Map(p).set(canon(lin),{lin,holds})
const active=(saved:Saved[],p:Path)=>saved.filter(s=>lemmaPath([s.lemma],p)!==p)
const fast=(g:Goal,p:Path):Tree|undefined=>{const r=refuteFast(rowsAt(g,p),256);return r?.kind==='refuted'?{leaf:r.steps}:undefined}
const decide=(lin:Record<string,number>,p:Path)=>p.get(canon(lin))?.holds??(p.has(canonFlip(lin))?!p.get(canonFlip(lin))!.holds:undefined)
const scopeValid=(p:Path,m:Record<string,number>)=>[...p.values()].every(a=>{if(Object.keys(a.lin).some(k=>k!=='1'&&!Object.hasOwn(m,k)))return false;const n=Object.entries(a.lin).reduce((s,[k,z])=>s+z*(k==='1'?1:m[k]!),0);return a.holds?n<=0:n>0})
function completed(q:Record<string,number>,g:Goal,p:Path){const model={...q},names=new Set<string>();walkLive(g.hyps,p,(o:any)=>{if(o.op==='var')names.add(o.name)});for(const a of p.values())for(const k of Object.keys(a.lin))if(k!=='1')names.add(k);const zero=[...names].filter(k=>!Object.hasOwn(model,k));for(const k of zero)model[k]=0;return {model,zero,valid:scopeValid(p,model)&&brokenOf(g)(model).length===0}}
export class GuardObserver{
 protected label='';protected indices:number[]=[];protected contexts:Context[]=[];protected full!:Packet
 begin(label:string,selection:any,full:Packet){this.label=label;this.indices=selection.originalIndices;this.contexts=[];this.full=full}
 capture(c:Context){this.contexts.push({...c,available:c.available.slice(),saved:c.saved.slice()})}
 protected pool(c:Context){const counts=countsForReads(c.ds,c.cert.reads);if(!counts)throw new Error('missing count declarations');return c.cert.insts.flatMap((inst,index)=>{const h=countHyp(counts,inst);return inst.terms.length<=5&&h?.op==='or'&&h.xs[0]?.op==='<='?[{index,originalIndex:this.indices[index]!,good:{op:'<=' as const,a:h.xs[0].a,b:h.xs[0].b},inst}]:[]})}
 protected attempt(c:Context,originalIndex:number,p:Path,extra:Saved[],end:number,queryShare?:number){
  const row=this.pool(c).find(r=>r.originalIndex===originalIndex);if(!row)throw new Error('candidate absent '+originalIndex)
  const available=active([...c.saved,...extra],p),h=c.g.hyps[c.g.hyps.length-c.cert.insts.length+row.index]!,part:Goal={name:c.g.name,hyps:[...c.source(p,row.inst.wit),...available.map(s=>s.good),h,{op:'not',x:row.good}]}
  const before=fullWork(),start=performance.now(),limit=Math.min(end,clock()+(queryShare??(row.inst.terms.length===5?150:50))),q:any=modelSequence(p)(part,limit),queryCountedUnits=(fullWork()-before)/fullRate,queryWallMs=performance.now()-start
  let tree:Tree|undefined='tree'in q?q.tree:undefined,proofSource=part
  if(!tree&&q.why===REFUTED&&q.core?.length&&q.core.length<=8&&clock()<end){
   const small={...part,hyps:q.core.map((i:number)=>part.hyps[i]!)},until=Math.min(end,Math.max(limit,clock()+100)),old=atPoint.on;atPoint.on=false
   try{let local=booleanCore(small,p,new Set([row.inst.wit]),until,[],{deferCheck:true,extended:true,scalarGuards:true,model:true});if(!local&&clock()<until){const folded=foldPath(small,p),out=grow(folded.goal,p,{nodes:0,until:Math.min(until,clock()+25),units:false});local='tree'in out?withDeadline(until,()=>widen(folded.goal,small,out.tree,folded.opaque,p,p)):undefined}if(local){tree=local;proofSource=small}}finally{atPoint.on=old}
  }
  const a=linear(row.good.a,p),b=linear(row.good.b,p),lemma=tree&&a&&b&&admitConditionalCut(c.g,proofSource,tree,p,p,sub(a,b),available.map(s=>s.lemma),performance.now()+1000)
  const value=q.stuck==='sat'&&q.witness?completed(q.witness,part,p):undefined
  const saved=lemma?{good:row.good,lemma,index:row.index}:undefined
  return {originalIndex,witness:row.inst.wit,outcome:saved?'checked':value?.valid?'sat':q.why===REFUTED?'refuted-unadmitted':q.stuck??'untransported',coreSize:q.core?.length??null,core:q.core??null,queryCountedUnits,queryWallMs,coreLimit:8,coreEligible:!!q.core?.length&&q.core.length<=8,countedUnits:(fullWork()-before)/fullRate,wallMs:performance.now()-start,source:part,sourceHash:hash(part),path:[...p],model:value?.model,zeroCompleted:value?.zero,sourceAndScopeValid:value?.valid??false,addedOriginalIndices:extra.map(s=>this.indices[s.index!]),saved,proofSource,tree,query:q}
 }
 protected numeric(c:Context,p:Path,extra:Saved[],end:number){
  const goal=c.numericFor(p,extra),before=fullWork(),start=performance.now(),natural=proveNaturalCases(goal,p,end,[],{deferCheck:true}),q:any=natural?{tree:natural}:modelSequence(p)(goal,end),queryCountedUnits=(fullWork()-before)/fullRate,queryWallMs=performance.now()-start
  let proof:Tree|undefined='tree'in q?q.tree:undefined
  if(!proof&&q.why===REFUTED&&q.core?.length&&clock()<end){const small={...goal,hyps:q.core.map((i:number)=>goal.hyps[i]!)},direct=fast(small,p),out=direct?undefined:grow(small,p,{nodes:0,until:end,units:false}),local=direct??(out&&'tree'in out?out.tree:undefined);if(local)proof=withDeadline(end,()=>widen(small,goal,local,{},p,p))}
  const numericChecked=!!proof&&check(goal,proof,p),available=active([...c.saved,...extra],p),extended=lemmaPath(available.map(s=>s.lemma),p),lifted=numericChecked&&liftCountProxies(goal,c.g,proof!,c.cert.reads,p,extended,undefined,{deferCheck:true}),marked=lifted&&markConditionalProof(c.g,lifted,available.map(s=>s.lemma)),conditionalChecked=!!marked&&checkConditionalProof(c.g,marked,p)
  const value=q.stuck==='sat'&&q.witness?completed(q.witness,goal,p):undefined
  const violated=value?.valid?this.pool(c).filter(r=>brokenOf({name:'pool good',hyps:[r.good]})(value.model).length>0).map(r=>r.originalIndex):undefined
  return {outcome:conditionalChecked?'checked':value?.valid?'sat':q.why===REFUTED?'refuted-untransported':q.stuck??'untransported',numericChecked,conditionalChecked,goal,path:[...p],model:value?.model,zeroCompleted:value?.zero,validModel:value?.valid??false,violated,query:q,numericProof:proof,proof:marked,lemmas:available.map(s=>s.lemma),queryCountedUnits,queryWallMs,countedUnits:(fullWork()-before)/fullRate,wallMs:performance.now()-start}
 }
 private branch(c:Context,name:string,p:Path,end:number,extra:Saved[]){
  const before=fullWork(),start=performance.now(),attempts:ReturnType<GuardObserver['attempt']>[]=[],queries:ReturnType<GuardObserver['numeric']>[]=[],excluded=new Set<number>()
  const finish=(outcome:string,reason:string)=>({name,path:[...p],outcome,reason,attempts,queries,excluded:[...excluded],extraOriginalIndices:extra.map(s=>this.indices[s.index!]),countedUnits:(fullWork()-before)/fullRate,wallMs:performance.now()-start})
  for(let round=0;round<=c.cert.insts.length&&clock()<end;round++){
   const q=this.numeric(c,p,extra,end);queries.push(q)
   if(q.conditionalChecked)return finish('checked','numeric-and-conditional-proof')
   if(!q.validModel||!q.violated)return finish('unknown','no-validated-numeric-model')
   const pending=q.violated.filter(i=>!excluded.has(i)&&!attempts.some(a=>a.originalIndex===i))
   if(!pending.length){
    // T-9A explicitly requires 27 and 32 to be checked as SAT on the complement.
    for(const i of [27,32])if(name==='complement'&&!attempts.some(a=>a.originalIndex===i)&&clock()<end){const a=this.attempt(c,i,p,extra,end);attempts.push(a);if(a.saved)extra.push(a.saved);else if(a.outcome==='sat')excluded.add(i)}
    const both=[27,32].every(i=>attempts.some(a=>a.originalIndex===i&&a.outcome==='sat')),allSat=q.violated.every(i=>excluded.has(i))
    return finish(name==='complement'&&both&&allSat?'generator-gap':'stalled',both&&allSat?'27-and-32-source-sat':'no-unexcluded-violated-pool-fact')
   }
   const expected=pending.every(i=>[27,32,77,84].includes(i));if(!expected)return finish('unknown','unexpected-violated-pool-fact')
   let added=0
   for(const i of [84,77,27,32].filter(i=>pending.includes(i))){if(clock()>=end)break;const a=this.attempt(c,i,p,extra,end);attempts.push(a);if(a.saved){extra.push(a.saved);added++}else if(a.outcome==='sat')excluded.add(i)}
   if(!added&&pending.every(i=>excluded.has(i))){
    const missing=[27,32].filter(i=>!attempts.some(a=>a.originalIndex===i))
    for(const i of missing)if(name==='complement'&&clock()<end){const a=this.attempt(c,i,p,extra,end);attempts.push(a);if(a.saved){extra.push(a.saved);added++}else if(a.outcome==='sat')excluded.add(i)}
    if(added)continue
    const both=[27,32].every(i=>attempts.some(a=>a.originalIndex===i&&a.outcome==='sat'))
    return finish(name==='complement'&&both?'generator-gap':'stalled',both?'27-and-32-source-sat':'all-violated-pool-facts-source-sat')
   }
  }
  return finish('unknown','shared-400-unit-limit')
 }
 finish(){
  if(!this.label.startsWith('Inv*'))throw new Error('T-9A expects Inv*')
  const c=this.contexts.findLast(c=>truth(same(x('a$#'),x('i')),c.scope)===true&&truth(less(x('j$'),x('i')),c.scope)===true&&!('tree'in c.q));if(!c)throw new Error('captured Inv* leaf missing')
  const guard:C={op:'<=',a:{op:'get',map:'CfgT',key:x('j$')},b:{op:'get',map:'CT',key:x('i')}},left=linear(guard.a,c.scope),right=linear(guard.b,c.scope);if(!left||!right)throw new Error('guard does not linearize')
  const atom=sub(left,right);if(truth(guard,c.scope)!==undefined)throw new Error('guard already decided')
  const proposals=[84,77,27,32].map(i=>{const index=this.indices.indexOf(i);if(index<0)throw new Error('missing original index');return {originalIndex:i,scopes:c.scopesFor(index).map(p=>({path:[...p],guard:truth(guard,p),newAtoms:[...p.values()].filter(a=>decide(a.lin,c.scope)===undefined)}))}})
  const generated=proposals.some(row=>row.scopes.some(s=>s.guard===true&&s.newAtoms.some(a=>canon(a.lin)===canon(atom)||canon(a.lin)===canonFlip(atom))))
  const side=process.env.LAB_SECTION9_SIDE??'A',repeat=Number(process.env.LAB_SECTION9_REPEAT??'1'),complementOnly=process.env.LAB_SECTION9_COMPLEMENT_ONLY==='1',before=fullWork(),start=performance.now()
  const branches=withWall(start+60000,()=>counted(fullRate,()=>{const end=clock()+400,extra:Saved[]=[];return side==='A'?[this.branch(c,'bare',c.scope,end,extra)]:complementOnly?[this.branch(c,'complement',put(c.scope,atom,false),end,extra)]:[this.branch(c,'guard',put(c.scope,atom,true),end,extra),this.branch(c,'complement',put(c.scope,atom,false),end,extra)]},true))
  const units=(fullWork()-before)/fullRate,wallMs=performance.now()-start,complement=branches.find(b=>b.name==='complement'),pass=side==='B'&&!complementOnly&&generated&&branches.every(b=>b.outcome==='checked')&&units<=400
  console.log(JSON.stringify({test:'T-9A',side,repeat,complementOnly,law:this.label,leafOrdinal:this.contexts.indexOf(c)+1,activeCuts:c.available.length,poolSize:this.pool(c).length,packetHash:hash({g:c.g,cert:c.cert,path:[...c.scope]}),guard,atom,generated,proposals,branches,countedUnits:units,wallMs,unitLimit:400,pass,stop:side==='B'&&!pass,generatorGap:complement?.outcome==='generator-gap',completeLawProof:false,packet:{g:c.g,cert:c.cert,fullCert:this.full,indices:this.indices,scope:[...c.scope],numeric:c.numeric,available:c.available}}))
 }
}
export const s9=new GuardObserver()
