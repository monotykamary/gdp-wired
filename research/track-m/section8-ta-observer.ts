// T-A only: retain exact leaf contexts during the unchanged sweep; query later.
import {gzipSync} from 'node:zlib'
import {type C,type E,type Machine,less,same,x} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Goal,type LemmaCut,type Path,type Tree,check,countHyp,lemmaPath,linear,truth} from '../../kernel/kernel.ts'
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
type Packet=Pick<CountCert,'reads'|'insts'>
type Saved={good:{op:'<=',a:E,b:E},lemma:LemmaCut,index?:number}
type Context={m:Machine,ds:CountDecl[],g:Goal,cert:Packet,scope:Path,numeric:Goal,available:Saved[],saved:Saved[],q:any,source:(path:Path,witness?:string)=>C[]}
const fast=(g:Goal,p:Path):Tree|undefined=>{const r=refuteFast(rowsAt(g,p),256);return r?.kind==='refuted'?{leaf:r.steps}:undefined}
export class TAObserver{
 private label=''
 private full!:Packet
 private indices:number[]=[]
 private contexts:Context[]=[]
 begin(label:string,selection:any,full:Packet){this.label=label;this.full=full;this.indices=selection.originalIndices;this.contexts=[]}
 capture(context:Context){this.contexts.push({...context,available:context.available.slice(),saved:context.saved.slice()})}
 private goods(context:Context,full=false){
  const cert=full?this.full:context.cert,counts=countsForReads(context.ds,cert.reads)
  if(!counts)throw new Error('missing count declarations')
  return cert.insts.flatMap((inst,index)=>{const h=countHyp(counts,inst);return inst.terms.length<=5&&h?.op==='or'&&h.xs[0]?.op==='<='?[{index,originalIndex:full?index:this.indices[index]!,good:h.xs[0],inst}]:[]})
 }
 private violated(context:Context,model:Record<string,number>,full=false){
  const rows=this.goods(context,full),missing:{index:number,names:string[]}[]=[],violated:number[]=[]
  for(const row of rows){const vars=new Set<string>();walkLive(row.good,context.scope,(o:any)=>{if(o.op==='var')vars.add(o.name)});const absent=[...vars].filter(name=>!Object.hasOwn(model,name));if(absent.length){missing.push({index:row.originalIndex,names:absent});continue}if(brokenOf({name:'pool-good',hyps:[row.good]})(model).length)violated.push(row.originalIndex)}
  return {size:rows.length,violated,missing,complete:missing.length===0,empty:missing.length===0&&violated.length===0}
 }
 private query(context:Context):any{
  const start=performance.now(),before=fullWork()
  const result=withWall(start+2000,()=>counted(fullRate,()=>{
   const end=clock()+2000,natural=proveNaturalCases(context.numeric,context.scope,end,[],{deferCheck:true}),q:any=natural?{tree:natural}:modelSequence(context.scope)(context.numeric,end)
   let proof:Tree|undefined='tree'in q?q.tree:undefined
   if(!proof&&q.why===REFUTED&&q.core?.length){const small={...context.numeric,hyps:q.core.map((i:number)=>context.numeric.hyps[i]!)},direct=fast(small,context.scope),grown=direct?undefined:grow(small,context.scope,{nodes:0,until:end,units:false}),local=direct??(grown&&'tree'in grown?grown.tree:undefined);if(local)proof=withDeadline(end,()=>widen(small,context.numeric,local,{},context.scope,context.scope))}
   const numericChecked=!!proof&&check(context.numeric,proof,context.scope),extended=lemmaPath(context.available.map(s=>s.lemma),context.scope)
   const lifted=numericChecked&&liftCountProxies(context.numeric,context.g,proof!,context.cert.reads,context.scope,extended,undefined,{deferCheck:true})
   const marked=lifted&&markConditionalProof(context.g,lifted,context.available.map(s=>s.lemma))
   return {q,numericChecked,conditionalChecked:!!marked&&checkConditionalProof(context.g,marked,context.scope)}
  },true))
  return {...result,wallMs:performance.now()-start,countedUnits:(fullWork()-before)/fullRate,wallLimitMs:2000,queryUnitLimit:2000}
 }
 private source(context:Context,originalIndex:number):any{
  const index=this.indices.indexOf(originalIndex),row=this.goods(context).find(r=>r.index===index)
  if(!row)throw new Error('source candidate absent')
  const h=context.g.hyps[context.g.hyps.length-context.cert.insts.length+index]!,path=context.scope,part:Goal={name:context.g.name,hyps:[...context.source(path,row.inst.wit),...context.available.map(s=>s.good),h,{op:'not',x:row.good}]}
  const start=performance.now(),before=fullWork()
  const result=withWall(start+2000,()=>counted(fullRate,()=>{
   const end=clock()+500,queryEnd=clock()+(row.inst.terms.length===5?150:50),q:any=modelSequence(path)(part,queryEnd)
   let tree:Tree|undefined='tree'in q?q.tree:undefined,source=part
   if(!tree&&q.why===REFUTED&&q.core?.length&&q.core.length<=8){
    const small={...part,hyps:q.core.map((i:number)=>part.hyps[i]!)},limit=Math.min(end,Math.max(queryEnd,clock()+100)),old=atPoint.on;atPoint.on=false
    try{let local=booleanCore(small,path,new Set([row.inst.wit]),limit,[],{deferCheck:true,extended:true,scalarGuards:true,model:true});if(!local&&clock()<limit){const folded=foldPath(small,path),out=grow(folded.goal,path,{nodes:0,until:Math.min(limit,clock()+25),units:false});local='tree'in out?withDeadline(limit,()=>widen(folded.goal,small,out.tree,folded.opaque,path,path)):undefined}if(local){tree=local;source=small}}finally{atPoint.on=old}
   }
   const a=linear(row.good.a,path),b=linear(row.good.b,path),lemma=tree&&a&&b&&admitConditionalCut(context.g,source,tree,path,path,sub(a,b),context.available.map(s=>s.lemma),performance.now()+1000)
   const model:Record<string,number>|undefined='tree'in q?undefined:q.witness,live=new Set<string>();walkLive(part.hyps,path,(o:any)=>{if(o.op==='var')live.add(o.name)})
   const missing=model?[...live].filter(name=>!Object.hasOwn(model,name)):undefined
   const scopeMissing=model?[...new Set([...path.values()].flatMap(a=>Object.keys(a.lin)))].filter(name=>name!=='1'&&!Object.hasOwn(model,name)):undefined
   const sourceValid=!!model&&brokenOf(part)(model).length===0
   const scopeValid=!!model&&scopeMissing?.length===0&&[...path.values()].every(a=>{const n=Object.entries(a.lin).reduce((sum,[key,z])=>sum+z*(key==='1'?1:model[key]!),0);return a.holds?n<=0:n>0})
   return {outcome:lemma?'checked':'tree'in q?'untransported':q.stuck,why:'tree'in q?undefined:q.why,core:'tree'in q?undefined:q.core,lemma,sourceHyps:part.hyps.length,treeBuilt:!!tree,reuseUsed:false,model,missing,scopeMissing,sourceValid,scopeValid,source:part,path:[...path]}
  },true))
  return {originalIndex,index,witness:row.inst.wit,...result,countedUnits:(fullWork()-before)/fullRate,wallMs:performance.now()-start}
 }
 finish(){
  const star=this.label.startsWith('Inv*'),target=star?this.contexts.findLast(c=>truth(same(x('a$#'),x('i')),c.scope)===true&&truth(less(x('j$'),x('i')),c.scope)===true&&!('tree'in c.q)):this.contexts[13]
  if(!target)throw new Error('T-A exact target leaf was not reached')
  if(!star&&(this.contexts.length!==14||target.available.length!==53))throw new Error('Inv2973 target differs from recorded leaf 14 / 53 cuts')
  const before=target.q,query=star?undefined:this.query(target),q=query?.q??before,model='tree'in q?undefined:q.witness
  const restricted=model?this.violated(target,model):undefined,full=model?this.violated(target,model,true):undefined
  const gap=restricted?.empty===true
  const wanted=star?[84,77]:[126,271,272,275,276],attempts=gap?[]:wanted.filter(i=>restricted?.violated.includes(i)).map(i=>this.source(target,i))
  const result={test:'T-A',law:this.label,leafOrdinal:this.contexts.indexOf(target)+1,baselineLeaves:this.contexts.length,activeCuts:target.available.length,activeOriginalIndices:target.available.flatMap(s=>s.index===undefined?[]:[this.indices[s.index]]),query,baselineOutcome:'tree'in before?'tree':before.stuck,baselineReason:'tree'in before?undefined:before.why,path:[...target.scope],numericHyps:target.numeric.hyps.length,model,restricted,full,stop:gap,reason:gap?'no-pool-fact':query?.conditionalChecked?'checked-leaf':attempts.some(a=>a.outcome==='checked')?'some-violated-facts-check':'no-violated-fact-proved',attempts}
  console.log(JSON.stringify(result))
  console.log(JSON.stringify({artifact:'T-A-leaf',law:this.label,encoding:'gzip-base64',data:gzipSync(JSON.stringify({g:target.g,numeric:target.numeric,path:[...target.scope],cert:target.cert,fullCert:this.full,indices:this.indices,available:target.available.map(s=>({good:s.good,lemma:s.lemma,index:s.index,originalIndex:s.index===undefined?undefined:this.indices[s.index]})),query,model,restricted,full,attempts})).toString('base64')}))
 }
}
export const ta=new TAObserver()
