// Untrusted three-phase recovery. Scalar/pointwise facts are prepared once;
// only the final arithmetic decision is repeated at row leaves. Every cut is
// independently checked, and the returned tree is checked without new axioms.
import {type C,type E,type Machine,x} from '../machine.ts'
import {type CountCert,type CountDecl,type Goal,type LemmaCut,type Path,type Tree,canon,canonFlip,facts,lemmaPath,linear,substC,substE,truth} from '../../kernel/kernel.ts'
import {atPoint,brokenOf,clock,pastWall,wallAt,withDeadline} from '../../kernel/prove.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {scale,sub} from '../solver.ts'
import {check,grow,modelSequence,refuteFast,rowsAt,widen} from './ops.ts'
import {fieldBounds,countBindingsAt} from './field-bound-lemmas.ts'
import {preStateCountSource} from './pre-state-source.ts'
import {booleanCore} from './boolean-core.ts'
import {foldPath} from './fold-path.ts'
import {piecesAt,walkLive} from './live-dependencies.ts'
import {liftCountProxies} from './lift-count-proxies.ts'
import {proveNaturalCases} from './natural-cases.ts'
import {type RowPair,proveRowCases,rowPairs} from './row-cases.ts'
import {admitConditionalCut,inlineConditionalCuts} from './conditional-cuts.ts'
import {markConditionalProof,checkConditionalProof} from './conditional-proof.ts'
import {countScalarGuards} from './scalar-guards.ts'
import {proposeWriteCountFrames} from '../count-write-frames.ts'
import {countsForReads} from '../count-facts.ts'
type Packet=Pick<CountCert,'reads'|'insts'>
type Bound={op:'<=',a:E,b:E}
type Saved={lemma:LemmaCut,good:Bound,index?:number}
type SourceModel={witness:string,model:Record<string,number>}
type Options={claim?:C,pairs?:RowPair[],conditional?:boolean,fieldSource?:(g:Goal,c:Packet,claim:C,p:Path,end:number)=>Tree|undefined}
const put=(p:Path,lin:Record<string,number>,holds:boolean):Path=>new Map(p).set(canon(lin),{lin,holds})
const plain=(lin:Record<string,number>)=>!Object.keys(lin).some(k=>k.startsWith('⟦'))
const fast=(g:Goal,p:Path):Tree|undefined=>{const q=refuteFast(rowsAt(g,p),256);return q?.kind==='refuted'?{leaf:q.steps}:undefined}
const decide=(lin:Record<string,number>,path:Path)=>path.get(canon(lin))?.holds??(path.has(canonFlip(lin))?!path.get(canonFlip(lin))!.holds:undefined)
const active=(saved:Saved[],path:Path)=>saved.filter(s=>lemmaPath([s.lemma],path)!==path)

export function deriveCountClosure(m:Machine,ds:CountDecl[],g:Goal,cert:Packet,root:Path,until:number,trace:object[],options:Options={}):Tree|undefined{
 const wanted=new Set<string>();walkLive(options.claim,root,(o:any)=>{
  if(o.op==='var'&&cert.reads.some(r=>r[0]===o.name))wanted.add(o.name)
  if(o.op==='get')for(const r of cert.reads)if(r[1]===o.map&&JSON.stringify(r[2])===JSON.stringify(o.key))wanted.add(r[0])
 })
 if(wanted.size<2||!cert.insts.some(q=>q.unit===0&&q.terms.length>=3)||clock()>=until||pastWall())return undefined
 const started=clock(),reserve=Math.min(400,(until-started)/3),buildEnd=until-reserve
 const raw=g.hyps.slice(0,-cert.insts.length),ids=new Set(cert.reads.map(r=>r[0])),maps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(q=>q.wit))
 const saved:Saved[]=[],models:SourceModel[]=[],pins:{split:Record<string,number>,no:Tree}[]=[]
 let base=new Map(root)
 const alive=()=>clock()<until&&!pastWall(),building=()=>clock()<buildEnd&&!pastWall()
 const wallEnd=()=>Math.min(wallAt(),performance.now()+Math.min(10000,Math.max(0,until-clock())*10))
 const transport=(from:Goal,to:Goal,t:Tree,a:Path,b:Path)=>alive()?withDeadline(until,()=>widen(from,to,t,{},a,b)):undefined
 const sourceCache=new WeakMap<Path,{rows:{c:C,owner?:string}[],views:Map<string|undefined,C[]>}>()
 const source=(path:Path,witness?:string):C[]=>{
  let entry=sourceCache.get(path)
  if(!entry){
   const rows: {c:C,owner?:string}[]=[]
   for(const c of raw.flatMap(c=>piecesAt(c,path))){
    let skip=false;const owners=new Set<string>()
    walkLive(c,path,(o:any)=>{if(o.op==='get'&&maps.has(o.map)||o.op==='var'&&ids.has(o.name))skip=true;else if(o.op==='var'&&wits.has(o.name))owners.add(o.name)})
    if(!skip&&owners.size<=1)rows.push({c,owner:owners.values().next().value})
   }
   entry={rows,views:new Map()};sourceCache.set(path,entry)
  }
  let view=entry.views.get(witness)
  if(!view){view=entry.rows.filter(r=>r.owner===undefined||r.owner===witness).map(r=>r.c);entry.views.set(witness,view)}
  return view
 }
 const accept=(good:Bound,part:Goal,tree:Tree,from:Path,scope:Path,index?:number):boolean=>{
  if(!building())return false
  const a=linear(good.a,from),b=linear(good.b,from);if(!a||!b)return false
  const cut=sub(a,b);if(!plain(cut))return false
  if(truth(good,lemmaPath(saved.map(s=>s.lemma),scope))===true)return true
  const lemma=admitConditionalCut(g,part,tree,from,scope,cut,saved.map(s=>s.lemma),wallEnd())
  if(!lemma||!building())return false
  saved.push({lemma,good,...(index===undefined?{}:{index})});trace.push({stage:'closure-cut',index,when:lemma.when,cut:lemma.cut});return true
 }
 // Pin only consequences already proved from the original raw hypotheses.
 // Other guards remain explicit conditions of a scalar cut, not assumptions.
 const pin=(atom:Record<string,number>):boolean=>{
  if(decide(atom,base)===true)return true
  if(!plain(atom)||!building())return false
  const noPath=put(base,atom,false),part={name:g.name,hyps:raw},tree=fast(part,noPath),no=tree&&transport(part,g,tree,noPath,noPath)
  if(!no)return false
  pins.push({split:atom,no});base=put(base,atom,true);return true
 }
 // Phase A, once: plain-cell ceilings with their guard atoms in `when`.
 for(const guarded of fieldBounds(m,ds,cert,{claim:options.claim,path:base})){
  if(!building())break
  if(guarded.op!=='<=')continue
  const condition=guarded.a.op==='if'?guarded.a.c:undefined
  if(condition&&truth(condition,base)===false)continue
  const conditions=condition?facts(condition,base):[]
  conditions.forEach(pin)
  let scope=new Map(base);for(const atom of conditions)scope=put(scope,atom,true)
  if(condition&&truth(condition,scope)!==true)continue
  const good:Bound={op:'<=',a:guarded.a.op==='if'?guarded.a.then:guarded.a,b:guarded.b},a=linear(good.a,scope),b=linear(good.b,scope)
  if(!a||!b||!plain(sub(a,b))||truth(good,lemmaPath(saved.map(s=>s.lemma),scope))===true)continue
  const before=clock(),traceStart=trace.length,noPath=put(scope,sub(a,b),false),small={name:g.name,hyps:source(scope)},direct=fast(small,noPath)
  let accepted=!!direct&&accept(good,small,direct,noPath,scope)
  if(!accepted&&options.fieldSource&&building()){
   const claim:C={op:'not',x:good},prior=preStateCountSource(g,cert,claim,scope),path=lemmaPath(saved.map(s=>s.lemma),scope)
   const tree=options.fieldSource(prior.goal,prior.cert,claim,path,Math.min(buildEnd,clock()+250))
   if(tree)accepted=accept(good,prior.goal,tree,path,scope)
  }
  trace.push({stage:'closure-scalar',plain:good,checked:accepted,ms:clock()-before,...(!accepted?{sourceTail:trace.slice(traceStart).slice(-8)}:{})})
 }
 // Conditional source scopes are data, not arithmetic proof leaves. Minimal
 // equal-row scopes come first; full order scopes cover the remaining cases.
 const pairMap=new Map((options.pairs??[]).map(pair=>[JSON.stringify(pair),pair]))
 for(const read of cert.reads)if(wanted.has(read[0])&&read[1].endsWith('#'))for(const pair of rowPairs(m,{reads:[read]},base,options.claim))pairMap.set(JSON.stringify(pair),pair)
 const pairs=[...pairMap.values()].slice(0,2),scopes:Path[]=[],scopeByKey=new Map<string,Path>()
 const addScope=(path:Path):Path=>{const key=JSON.stringify([...path].map(([id,a])=>[id,a.holds])),old=scopeByKey.get(key);if(old)return old;scopeByKey.set(key,path);scopes.push(path);return path}
 const rowChoices=(path:Path,pair:RowPair):Path[]=>{
  const c:C={op:'=',a:pair[0],b:pair[1]};if(truth(c,path)!==undefined)return [path]
  const a=linear(pair[0],path),b=linear(pair[1],path);if(!a||!b)return [path]
  const f=sub(a,b),back=scale(f,-1)
  return [put(put(path,f,true),back,true),put(put(path,f,true),back,false),put(path,f,false)]
 }
 addScope(base)
 for(const pair of pairs)for(const scope of rowChoices(base,pair))addScope(scope)
 let complete=[base]
 for(const pair of pairs)complete=complete.flatMap(path=>rowChoices(path,pair))
 for(const scope of complete)addScope(scope)
 const rowScopes=[...scopes]
 const postReads=new Set(cert.reads.filter(r=>r[1].endsWith('#')).map(r=>r[0]))
 const conditional=(index:number)=>cert.insts[index]!.terms.some(([,id])=>postReads.has(id))
 const readMap=new Map(cert.reads.map(([id,map])=>[id,map]))
 const frame=(index:number)=>{const q=cert.insts[index]!;if(q.terms.length!==2)return false;const [a,b]=q.terms.map(([,id])=>readMap.get(id));return !!a&&!!b&&(a.endsWith('#')&&a.slice(0,-1)===b||b.endsWith('#')&&b.slice(0,-1)===a)}
 const vector=(q:CountCert['insts'][number])=>JSON.stringify([...q.terms].sort((a,b)=>a[1].localeCompare(b[1])||a[0]-b[0]))
 const bridges=new Set(proposeWriteCountFrames(m,ds,{reads:cert.reads,insts:[]},wanted).map(vector))
 // Inclusion is cheap even when an expanded post partition is not. Rank by
 // declarative membership containment only; the actual witness still proves it.
 const predicates=new Map<string,Set<string>>()
 for(const read of cert.reads){
  const plainRead:typeof read=[read[0],read[1].endsWith('#')?read[1].slice(0,-1):read[1],read[2]],count=countsForReads(ds,[plainRead])?.[0]
  if(!count)continue
  const body=substE(count.body,{vars:{[count.key]:x('closure$member')},maps:{},flags:{}})
  if(body.op!=='if'||body.then.op!=='const'||body.then.value!==1||body.else.op!=='const'||body.else.value!==0)continue
  const atoms=new Set<string>(),collect=(c:C):void=>{if(c.op==='and')c.xs.forEach(collect);else atoms.add(JSON.stringify(c))};collect(body.c);predicates.set(read[0],atoms)
 }
 const inclusion=(q:CountCert['insts'][number]):boolean=>{
  if(q.unit!==0||q.terms.length!==2)return false
  const a=q.terms.find(([z])=>z===1)?.[1],b=q.terms.find(([z])=>z===-1)?.[1]
  if(!a||!b||postReads.has(a)!==postReads.has(b))return false
  const left=predicates.get(a),right=predicates.get(b)
  return !!left&&!!right&&[...right].every(atom=>left.has(atom))
 }
 const rank=(index:number)=>{const q=cert.insts[index]!,arity=q.terms.length;return q.unit!==0&&arity===1?-2:inclusion(q)?-1:arity===1&&wanted.has(q.terms[0]![1])?0:!conditional(index)&&arity===3?0:bridges.has(vector(q))?1:!conditional(index)&&arity===5?2:frame(index)?3:!conditional(index)?4:arity===3?5:arity===2?6:7}
 const pool=cert.insts.flatMap((q,index)=>q.terms.length<=5?[index]:[]).sort((a,b)=>rank(a)-rank(b))
 const rowNames=new Set<string>();for(const pair of pairs)walkLive(pair,base,(o:any)=>{if(o.op==='var'&&!m.inputs.includes(o.name))rowNames.add(o.name)})
 const sourceRows=new Map(pool.map(index=>{
  const names=new Set<string>()
  for(const [,id]of cert.insts[index]!.terms){const read=cert.reads.find(r=>r[0]===id);if(read)walkLive(read[2],base,(o:any)=>{if(o.op==='var'&&rowNames.has(o.name))names.add(o.name)})}
  return [index,names] as const
 }))
 const scalarAtoms=new Set<string>(),scopeCache=new Map<number,Path[]>()
 const scopesFor=(index:number)=>{
  const old=scopeCache.get(index);if(old)return old
  const rows=rowScopes.filter(scope=>[...scope].every(([id,atom])=>base.has(id)||Object.keys(atom.lin).every(name=>!rowNames.has(name)||sourceRows.get(index)!.has(name))))
  const bridge=bridges.has(vector(cert.insts[index]!)),guarded:Path[]=[],equalRows=rows.filter(scope=>scope!==base&&scope.size<=base.size+2&&pairs.some(([a,b])=>truth({op:'=',a,b},scope)===true))
  const distinctRows=bridge?rows.filter(scope=>{const states=pairs.map(([a,b])=>truth({op:'=',a,b},scope));return states.includes(true)&&states.includes(false)}):[]
  const origins=conditional(index)?[...distinctRows,...equalRows,base]:[base]
  const proposed=countScalarGuards(m,ds,cert.reads,cert.insts[index]!,base,{name:g.name,hyps:source(base,cert.insts[index]!.wit)}),equal=proposed.filter(guards=>guards.every(c=>c.op==='='))
  const choices=bridge&&equal.length?equal.sort((a,b)=>b.length-a.length):proposed
  for(const guards of choices)for(const origin of origins){
   let scope=new Map(origin),valid=true
   const aliases:Record<string,E>={}
   for(const [a,b]of pairs)if(a.op==='var'&&truth({op:'=',a,b},origin)===true)aliases[a.name]=b
   for(const original of guards){
    const condition=substC(original,{vars:aliases,maps:{},flags:{}})
    if(truth(condition,scope)===false){valid=false;break}
    for(const atom of facts(condition,scope)){
     if(!plain(atom)){valid=false;break}
     scalarAtoms.add(canon(atom));scalarAtoms.add(canonFlip(atom));scope=put(scope,atom,true)
    }
    if(!valid)break
   }
   if(valid)guarded.push(addScope(scope))
  }
  const unique=new Set<string>(),out=(bridge?[base,...rows,...guarded]:[base,...guarded,...rows]).filter(scope=>{const key=JSON.stringify([...scope].map(([id,a])=>[id,a.holds]));if(unique.has(key))return false;unique.add(key);return true})
  scopeCache.set(index,out);return out
 }
 const failed=new Map<string,number>();let rounds=0,fixedPoint=false
 // Phase B, once: a fixed point of conditional facts. A model can reject a
 // source only after its entire source AND every scope atom validate.
 while(building()){
  const version=saved.length;let added=0,unresolved=0;rounds++
  for(const index of pool){
   if(!building())break
   for(const scope of scopesFor(index)){
    if(!building())break
    const key=`${scopes.indexOf(scope)}:${index}`;if(failed.get(key)===version)continue
    const inst=cert.insts[index]!,h=g.hyps[raw.length+index];if(h?.op!=='or'||h.xs[0]?.op!=='<=')continue
    const good:Bound={op:'<=',a:h.xs[0].a,b:h.xs[0].b},available=active(saved,scope),path=scope
    if(truth(good,lemmaPath(available.map(s=>s.lemma),scope))===true)continue
    if(scope!==base&&!sourceRows.get(index)!.size&&available.filter(s=>s.index===undefined).every(s=>active([s],base).length>0))continue
    const part:Goal={name:g.name,hyps:[...source(path,inst.wit),...available.map(s=>s.good),h,{op:'not',x:good}]},before=clock()
    const reused=models.some(savedModel=>{
     if(![...path.values()].every(a=>{
      if(Object.keys(a.lin).some(k=>k!=='1'&&!Object.hasOwn(savedModel.model,k)))return false
      const value=Object.entries(a.lin).reduce((sum,[k,v])=>sum+v*(k==='1'?1:savedModel.model[k]!),0)
      return a.holds?value<=0:value>0
     }))return false
     const renamed={...part,hyps:part.hyps.map(c=>substC(c,{vars:{[inst.wit]:x(savedModel.witness)},maps:{},flags:{}}))}
     return brokenOf(renamed)(savedModel.model).length===0
    })
    if(reused){failed.set(key,version);trace.push({stage:'closure-source',scope:scopes.indexOf(scope),index,outcome:'reused-model',ms:clock()-before});continue}
    const queryLimit=Math.min(buildEnd,clock()+(inst.terms.length===5?150:50)),q=modelSequence(path)(part,queryLimit)
    let tree:Tree|undefined='tree'in q?q.tree:undefined,proofSource=part,validModel=false
    if(!tree&&!('tree'in q)&&q.stuck==='sat'&&q.witness){
     if(brokenOf(part)(q.witness).length===0){validModel=true;models.push({witness:inst.wit,model:q.witness});if(models.length>32)models.shift()}
    }else if(!tree&&!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=8&&building()){
     const limit=Math.min(buildEnd,Math.max(queryLimit,clock()+100))
     const small={...part,hyps:q.core.map(i=>part.hyps[i]!)},oldPoint=atPoint.on
     atPoint.on=false
     try{
      let local=booleanCore(small,path,new Set([inst.wit]),limit,trace,{deferCheck:true,extended:true,scalarGuards:true,model:true})
      if(!local&&clock()<limit){
       const folded=foldPath(small,path),out=grow(folded.goal,path,{nodes:0,until:Math.min(limit,clock()+25),units:false})
       local='tree'in out?withDeadline(limit,()=>widen(folded.goal,small,out.tree,folded.opaque,path,path)):undefined
      }
      if(local){tree=local;proofSource=small}
     }finally{atPoint.on=oldPoint}
    }
    const accepted=!!tree&&accept(good,proofSource,tree,path,scope,index)
    if(accepted)added++;else{failed.set(key,version);if(!validModel)unresolved++}
    trace.push({stage:'closure-source',scope:scopes.indexOf(scope),index,core:q.core?.length,tree:!!tree,outcome:accepted?'checked':'tree'in q?'untransported':q.stuck,ms:clock()-before})
   }
  }
  trace.push({stage:'closure-round',round:rounds,added,unresolved,cuts:saved.length,models:models.length,scopes:scopes.length})
  if(!added){fixedPoint=building()&&unresolved===0;break}
 }
 // Phase C only: use active proved facts, then decide one numeric goal per
 // leaf. Natural-subtraction splitting is confined to this arithmetic phase.
 const pure=(c:C,path:Path)=>{let other=false;walkLive(c,path,(o:any)=>{if(o.op==='get'||o.op==='var'&&wits.has(o.name))other=true});return !other}
 const replacements=Object.fromEntries([...maps].map(map=>[map,(key:any)=>{const r=cert.reads.find(r=>r[1]===map&&JSON.stringify(r[2])===JSON.stringify(key));return r?x(r[0]):{op:'get' as const,map,key}}]))
 const flags=Object.fromEntries(Object.keys(m.step.flags??{}).map(name=>[name,{op:'flag' as const,name}]))
 const abstracted=raw.map(c=>substC(c,{vars:{},maps:replacements,flags}))
 const finish=(scope:Path,end:number):Tree|undefined=>{
  if(!alive())return undefined
  const available=active(saved,scope),path=scope,before=clock()
  const numeric:Goal={name:g.name,hyps:[...abstracted.flatMap(c=>piecesAt(c,path)).filter(c=>pure(c,path)),...countBindingsAt(cert.reads,path),...available.map(s=>s.good).filter(c=>pure(c,path))]}
  const natural=proveNaturalCases(numeric,path,end,trace,{deferCheck:true}),q=natural?{tree:natural}:modelSequence(path)(numeric,end)
  let proof:Tree|undefined='tree'in q?q.tree:undefined
  if(!proof&&!('tree'in q)&&q.why===REFUTED&&q.core?.length){
   const small={...numeric,hyps:q.core.map(i=>numeric.hyps[i]!)},direct=fast(small,path),out=direct?undefined:grow(small,path,{nodes:0,until:end,units:false}),local=direct??(out&&'tree'in out?out.tree:undefined)
   if(local)proof=transport(small,numeric,local,path,path)
  }
  const extended=lemmaPath(available.map(s=>s.lemma),scope)
  const lifted=proof&&liftCountProxies(numeric,g,proof,cert.reads,path,extended,e=>trace.push({stage:'closure-transport',...e}),{deferCheck:true})
  const tree=lifted&&(options.conditional?markConditionalProof(g,lifted,available.map(s=>s.lemma)):inlineConditionalCuts(g,g,lifted,extended,scope,available.map(s=>s.lemma),wallEnd(),e=>trace.push({stage:'closure-inline',...e})))
  trace.push({stage:'closure-final',fixedPoint,hyps:numeric.hyps.length,cuts:available.length,closedIndices:available.flatMap(s=>s.index===undefined?[]:[s.index]),rounds,core:'tree'in q?undefined:q.core?.length,outcome:tree?'checked':'tree'in q?'untransported':q.stuck,reason:'tree'in q?undefined:q.why,...(!('tree'in q)&&q.stuck==='sat'?{model:q.witness,path:[...scope]}:{}),ms:clock()-before,total:clock()-started})
  return tree
 }
 const scalar=(path:Path,end:number,depth=0):Tree|undefined=>{
  if(!alive())return undefined
  const candidates=new Map<string,{atom:Record<string,number>,uses:number}>()
  for(const {lemma}of saved){
   if(lemma.when.some(atom=>decide(atom,path)===false))continue
   for(const atom of lemma.when){const id=canon(atom);if(!scalarAtoms.has(id)||decide(atom,path)!==undefined)continue;const old=candidates.get(id);candidates.set(id,{atom,uses:(old?.uses??0)+1})}
  }
  const next=[...candidates.values()].sort((a,b)=>b.uses-a.uses)[0]
  if(!next||depth>=8)return finish(path,Math.min(end,clock()+350))
  const yes=scalar(put(path,next.atom,true),end,depth+1),no=yes&&scalar(put(path,next.atom,false),end,depth+1)
  trace.push({stage:'closure-scalar-case',depth,split:next.atom,proposed:!!yes&&!!no})
  return yes&&no?{split:next.atom,yes,no}:undefined
 }
 let tree=pairs.length?proveRowCases(g,base,pairs,until,(path,end)=>scalar(path,end),e=>trace.push(e),{deferToCaller:true,splitEqual:true}):scalar(base,until)
 for(let i=pins.length-1;tree&&i>=0;i--)tree={split:pins[i]!.split,yes:tree,no:pins[i]!.no}
 const checked=!!tree&&alive()&&(options.conditional?checkConditionalProof(g,tree,root):check(g,tree,root))
 trace.push({stage:'closure-complete',cuts:saved.length,rounds,fixedPoint,checked,total:clock()-started})
 return checked?tree:undefined
}
