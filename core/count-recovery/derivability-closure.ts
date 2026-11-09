// Untrusted model-driven recovery. Scalar facts are prepared once; numeric
// countermodels select batches of pointwise facts at bounded row leaves. Every
// cut and the final tree are independently checked, without new axioms.
import {type C,type E,type Machine,x} from '../machine.ts'
import {type CountCert,type CountDecl,type Goal,type LemmaCut,type Path,type Tree,canon,canonFlip,facts,lemmaPath,linear,substC,substE,truth} from '../../kernel/kernel.ts'
import {atPoint,brokenOf,clock,pastWall,usedHyps,wallAt,withDeadline} from '../../kernel/prove.ts'
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
import {memberInclusions} from './member-inclusions.ts'
import {leafAllowance} from './leaf-allowance.ts'
import {type FieldDemand,beginFieldAttempt,endFieldAttempt} from './field-demand.ts'
type Packet=Pick<CountCert,'reads'|'insts'>
type Bound={op:'<=',a:E,b:E}
type Saved={lemma:LemmaCut,good:Bound,index?:number}
type SourceModel={witness:string,model:Record<string,number>}
type Options={claim?:C,pairs?:RowPair[],conditional?:boolean,fieldDemand?:FieldDemand,fieldSource?:(g:Goal,c:Packet,claim:C,p:Path,end:number)=>Tree|undefined}
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
 let leafEnd:number|undefined
 const alive=()=>clock()<until&&!pastWall(),building=()=>clock()<(leafEnd??buildEnd)&&!pastWall()
 const wallEnd=()=>Math.min(wallAt(),performance.now()+Math.min(10000,Math.max(0,(leafEnd??until)-clock())*10))
 const transport=(from:Goal,to:Goal,t:Tree,a:Path,b:Path)=>alive()?withDeadline(Math.min(until,leafEnd??until),()=>widen(from,to,t,{},a,b)):undefined
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
  const before=clock(),traceStart=trace.length,noPath=put(scope,sub(a,b),false),small={name:g.name,hyps:source(scope)},meter=beginFieldAttempt(guarded,scope,options.fieldDemand,'closure-scalar')
  let accepted=false
  try{const direct=fast(small,noPath);accepted=!!direct&&accept(good,small,direct,noPath,scope)
  if(!accepted&&options.fieldSource&&building()){
   const claim:C={op:'not',x:good},prior=preStateCountSource(g,cert,claim,scope),path=lemmaPath(saved.map(s=>s.lemma),scope)
   const tree=options.fieldSource(prior.goal,prior.cert,claim,path,Math.min(buildEnd,clock()+250))
   if(tree)accepted=accept(good,prior.goal,tree,path,scope)
  }
  }finally{endFieldAttempt(meter,accepted)}
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
 const memberHints=new Map<string,C[]>(memberInclusions(m,ds,cert.reads).map(p=>[vector({wit:'',unit:0,below:p.below,terms:[[1,p.positive],[-1,p.negative]]}),p.guards]))
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
  const preferred=memberHints.get(vector(cert.insts[index]!))
  const proposed=[...(preferred?[preferred]:[]),...countScalarGuards(m,ds,cert.reads,cert.insts[index]!,base,{name:g.name,hyps:source(base,cert.insts[index]!.wit)})].slice(0,8),equal=proposed.filter(guards=>guards.every(c=>c.op==='='))
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
 let rounds=0,fixedPoint=false
 for(const index of pool)scopesFor(index)
 const excludedAt=new Map<string,Set<number>>(),attempted=new Map<string,{version:number,outcome:'checked'|'sat'|'unknown'}>()
 const validPoint=(part:Goal,path:Path,point:Record<string,number>):Record<string,number>|undefined=>{
  const model={...point}
  walkLive(part.hyps,path,(o:any)=>{if(o.op==='var'&&!Object.hasOwn(model,o.name))model[o.name]=0})
  for(const atom of path.values())for(const name of Object.keys(atom.lin))if(name!=='1'&&!Object.hasOwn(model,name))model[name]=0
  if(!Object.values(model).every(Number.isSafeInteger)||brokenOf(part)(model).length)return undefined
  return [...path.values()].every(a=>{const n=Object.entries(a.lin).reduce((s,[k,z])=>s+z*(k==='1'?1:model[k]!),0);return Number.isFinite(n)&&(a.holds?n<=0:n>0)})?model:undefined
 }
 const attempt=(index:number,scope:Path,end:number):'checked'|'sat'|'unknown'=>{
  if(!building())return 'unknown'
  scope=addScope(scope)
  const version=saved.length,key=`${scopes.indexOf(scope)}:${index}`,had=attempted.get(key)
  if(had?.version===version)return had.outcome
  const inst=cert.insts[index]!,h=g.hyps[raw.length+index];if(h?.op!=='or'||h.xs[0]?.op!=='<=')return 'unknown'
  const good:Bound={op:'<=',a:h.xs[0].a,b:h.xs[0].b},available=active(saved,scope),path=scope,before=clock()
  const part:Goal={name:g.name,hyps:[...source(path,inst.wit),...available.map(s=>s.good),h,{op:'not',x:good}]}
  const reused=models.some(m=>validPoint({...part,hyps:part.hyps.map(c=>substC(c,{vars:{[inst.wit]:x(m.witness)},maps:{},flags:{}}))},path,m.model)!==undefined)
  if(reused){attempted.set(key,{version,outcome:'sat'});trace.push({stage:'closure-source',scope:scopes.indexOf(scope),index,outcome:'reused-model',ms:clock()-before});return 'sat'}
  const queryLimit=Math.min(end,clock()+(inst.terms.length===5?150:50)),q=modelSequence(path)(part,queryLimit)
  let tree:Tree|undefined='tree'in q?q.tree:undefined,proofSource=part,validModel=false
  if(!tree&&!('tree'in q)&&q.stuck==='sat'&&q.witness){
   const model=validPoint(part,path,q.witness)
   if(model){validModel=true;models.push({witness:inst.wit,model});if(models.length>32)models.shift()}
  }else if(!tree&&!('tree'in q)&&q.why===REFUTED&&q.core?.length&&q.core.length<=8&&building()){
   const limit=Math.min(end,Math.max(queryLimit,clock()+100)),small={...part,hyps:q.core.map(i=>part.hyps[i]!)},oldPoint=atPoint.on;atPoint.on=false
   try{let local=booleanCore(small,path,new Set([inst.wit]),limit,trace,{deferCheck:true,extended:true,scalarGuards:true,model:true});if(!local&&clock()<limit){const folded=foldPath(small,path),out=grow(folded.goal,path,{nodes:0,until:Math.min(limit,clock()+25),units:false});local='tree'in out?withDeadline(limit,()=>widen(folded.goal,small,out.tree,folded.opaque,path,path)):undefined}if(local){tree=local;proofSource=small}}finally{atPoint.on=oldPoint}
  }
  const accepted=!!tree&&accept(good,proofSource,tree,path,scope,index),outcome=accepted?'checked':validModel?'sat':'unknown'
  attempted.set(key,{version,outcome})
  trace.push({stage:'closure-source',scope:scopes.indexOf(scope),index,core:'tree'in q?undefined:q.core?.length,tree:!!tree,outcome,ms:clock()-before})
  return outcome
 }
 // Phase C only: use active proved facts, then decide one numeric goal per
 // leaf. Natural-subtraction splitting is confined to this arithmetic phase.
 const pure=(c:C,path:Path)=>{let other=false;walkLive(c,path,(o:any)=>{if(o.op==='get'||o.op==='var'&&wits.has(o.name))other=true});return !other}
 const replacements=Object.fromEntries([...maps].map(map=>[map,(key:any)=>{const r=cert.reads.find(r=>r[1]===map&&JSON.stringify(r[2])===JSON.stringify(key));return r?x(r[0]):{op:'get' as const,map,key}}]))
 const flags=Object.fromEntries(Object.keys(m.step.flags??{}).map(name=>[name,{op:'flag' as const,name}]))
 const abstracted=raw.map(c=>substC(c,{vars:{},maps:replacements,flags}))
 const finish=(scope:Path,end:number,depth=0):Tree|undefined=>{
  if(!alive())return undefined
  scope=addScope(scope)
  const before=clock(),scopeKey=JSON.stringify([...scope].map(([id,a])=>[id,a.holds])),excluded=excludedAt.get(scopeKey)??new Set<number>(),previousEnd=leafEnd
  excludedAt.set(scopeKey,excluded);leafEnd=end
  const numericFor=():Goal=>({name:g.name,hyps:[...abstracted.flatMap(c=>piecesAt(c,scope)).filter(c=>pure(c,scope)),...countBindingsAt(cert.reads,scope),...active(saved,scope).map(s=>s.good).filter(c=>pure(c,scope))]})
  const stop=(reason:string)=>{trace.push({stage:'closure-final',mode:'model-driven',outcome:'unknown',reason,path:[...scope],cuts:active(saved,scope).length,ms:clock()-before,total:clock()-started});return undefined}
  const merge=(candidate:Path):Path|undefined=>{
   const path=new Map(scope)
   for(const a of candidate.values()){const known=decide(a.lin,path);if(known!==undefined&&known!==a.holds)return undefined;path.set(canon(a.lin),a)}
   return addScope(path)
  }
  try{
   for(let round=0;round<=pool.length&&building();round++){
    rounds++;const available=active(saved,scope),numeric=numericFor(),natural=proveNaturalCases(numeric,scope,end,trace,{deferCheck:true}),q=natural?{tree:natural}:modelSequence(scope)(numeric,end)
    let proof:Tree|undefined='tree'in q?q.tree:undefined
    // An empty core refutes the path alone; it still needs a transported proof.
    if(!proof&&!('tree'in q)&&q.why===REFUTED&&q.core){const small={...numeric,hyps:q.core.map(i=>numeric.hyps[i]!)},direct=fast(small,scope),out=direct?undefined:grow(small,scope,{nodes:0,until:end,units:false}),local=direct??(out&&'tree'in out?out.tree:undefined);if(local)proof=transport(small,numeric,local,scope,scope)}
    if(proof){
     const extended=lemmaPath(available.map(s=>s.lemma),scope),lifted=liftCountProxies(numeric,g,proof,cert.reads,scope,extended,e=>trace.push({stage:'closure-transport',...e}),{deferCheck:true})
     const tree=lifted&&(options.conditional?markConditionalProof(g,lifted,available.map(s=>s.lemma)):inlineConditionalCuts(g,g,lifted,extended,scope,available.map(s=>s.lemma),wallEnd(),e=>trace.push({stage:'closure-inline',...e})))
     trace.push({stage:'closure-final',mode:'model-driven',fixedPoint,hyps:numeric.hyps.length,cuts:available.length,rounds:round+1,closedIndices:available.flatMap(s=>s.index===undefined?[]:[s.index]),outcome:tree?'checked':'untransported',ms:clock()-before,total:clock()-started});return tree
    }
    if('tree'in q||q.stuck!=='sat'||!q.witness)return stop('no-numeric-model')
    const point={...q.witness}
    for(const index of pool){const h=g.hyps[raw.length+index];if(h?.op==='or'&&h.xs[0]?.op==='<=')walkLive(h.xs[0],scope,(o:any)=>{if(o.op==='var'&&!Object.hasOwn(point,o.name))point[o.name]=0})}
    const model=validPoint(numeric,scope,point);if(!model)return stop('invalid-numeric-model')
    const violated=pool.filter(index=>{const h=g.hyps[raw.length+index];return h?.op==='or'&&h.xs[0]?.op==='<='&&brokenOf({name:'candidate',hyps:[h.xs[0]]})(model).length>0}),pending=new Set(violated.filter(i=>!excluded.has(i))),startedVersion=saved.length
    trace.push({stage:'closure-model-round',round:round+1,scope:scopes.indexOf(scope),violated,pending:[...pending],excluded:[...excluded],cuts:available.length,pool:pool.length})
    if(!pending.size){fixedPoint=true;return stop('no-unexcluded-violated-fact')}
    while(pending.size&&building()){
     const indices=[...pending],baseGoal=numericFor(),goods=indices.map(i=>(g.hyps[raw.length+i] as Extract<C,{op:'or'}>).xs[0]!),assumed={...baseGoal,hyps:[...baseGoal.hyps,...goods]},selection=modelSequence(scope)(assumed,end)
     const core='tree'in selection?[...usedHyps(assumed,selection.tree,scope)]:selection.why===REFUTED?selection.core:undefined
     const validAssumedModel=!('tree'in selection)&&selection.stuck==='sat'&&selection.witness&&validPoint(assumed,scope,selection.witness)
     if(!core?.length&&!validAssumedModel)return stop('no-batch-core-or-model')
     // A partial violated set can leave another numeric model: its members
     // are still useful cuts against the current model, not a generator gap.
     const chosen=core?.length?core.filter(i=>i>=baseGoal.hyps.length).map(i=>indices[i-baseGoal.hyps.length]!).filter(i=>i!==undefined):indices
     trace.push({stage:'closure-batch-core',scope:scopes.indexOf(scope),round:round+1,indices:chosen,core:core?.length,selector:core?.length?'refuted':'sat'})
     if(!chosen.length){if(saved.length>startedVersion)break;return stop('empty-batch-core')}
     let changed=false
     for(const index of chosen){
      if(!building())break
      pending.delete(index)
      const candidates=scopesFor(index).map(merge).filter((p):p is Path=>p!==undefined),hinted=memberHints.has(vector(cert.insts[index]!)),order=hinted?[...candidates.filter(p=>p!==scope),scope]:[scope,...candidates],seen=new Set<Path>();let allSat=true,proved=false
      for(const path of order){
       if(seen.has(path))continue;seen.add(path)
       if(!building()){allSat=false;break}
       const result=attempt(index,path,end)
       if(result==='checked'){changed=true;proved=true;break}
       if(result!=='sat')allSat=false
      }
      if(allSat&&!proved)excluded.add(index)
     }
     const guard=saved.slice(startedVersion).flatMap(s=>s.lemma.when).find(atom=>scalarAtoms.has(canon(atom))&&decide(atom,scope)===undefined)
     if(guard){
      if(depth>=8)return stop('scalar-depth')
      const yes=scalar(put(scope,guard,true),end,depth+1),no=yes&&scalar(put(scope,guard,false),end,depth+1)
      trace.push({stage:'closure-model-split',depth,split:guard,proposed:!!yes&&!!no,ms:clock()-before})
      return yes&&no?{split:guard,yes,no}:undefined
     }
     if(changed)break
    }
    if(saved.length===startedVersion)return stop(building()?'batch-exhausted':'time')
   }
   return stop('time')
  }finally{leafEnd=previousEnd}
 }
 const scalar=(path:Path,end:number,depth=0):Tree|undefined=>{
  if(!alive())return undefined
  const candidates=new Map<string,{atom:Record<string,number>,uses:number}>()
  for(const {lemma}of saved){
   if(lemma.when.some(atom=>decide(atom,path)===false))continue
   for(const atom of lemma.when){const id=canon(atom);if(!scalarAtoms.has(id)||decide(atom,path)!==undefined)continue;const old=candidates.get(id);candidates.set(id,{atom,uses:(old?.uses??0)+1})}
  }
  const next=[...candidates.values()].sort((a,b)=>b.uses-a.uses)[0]
  if(!next||depth>=8)return finish(path,end,depth)
  const yes=scalar(put(path,next.atom,true),end,depth+1),no=yes&&scalar(put(path,next.atom,false),end,depth+1)
  trace.push({stage:'closure-scalar-case',depth,split:next.atom,proposed:!!yes&&!!no})
  return yes&&no?{split:next.atom,yes,no}:undefined
 }
 let leavesLeft=Math.max(1,complete.length)
 const atLeaf=(path:Path,end:number):Tree|undefined=>{
  const before=clock(),remaining=Math.max(0,until-before),draw=leafAllowance(remaining,leavesLeft),stop=Math.min(end,before+draw)
  trace.push({stage:'closure-leaf-budget',remaining,leavesLeft,draw,granted:Math.max(0,stop-before),end:stop})
  return scalar(path,stop)
 }
 const rowTrace=(event:object)=>{const e=event as {stage?:string};if(e.stage==='row-case'||e.stage==='row-mirror')leavesLeft=Math.max(1,leavesLeft-1);trace.push(event)}
 let tree=pairs.length?proveRowCases(g,base,pairs,until,atLeaf,rowTrace,{deferToCaller:true,splitEqual:true}):atLeaf(base,until)
 for(let i=pins.length-1;tree&&i>=0;i--)tree={split:pins[i]!.split,yes:tree,no:pins[i]!.no}
 const checked=!!tree&&alive()&&(options.conditional?checkConditionalProof(g,tree,root):check(g,tree,root))
 trace.push({stage:'closure-complete',cuts:saved.length,rounds,fixedPoint,checked,total:clock()-started})
 return checked?tree:undefined
}
