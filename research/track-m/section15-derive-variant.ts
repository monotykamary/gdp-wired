// Section 15.5 research policy. It never writes the laptop's production source.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux copy required')
const mode=process.argv[2];if(!['before','after'].includes(mode!))throw Error('before|after required')
if(mode==='after'){
 const path='core/count-recovery/derivability-closure.ts',before=readFileSync(path,'utf8');let s=before
 const replace=(a:string,b:string)=>{if(s.split(a).length!==2)throw Error('derive anchor changed: '+a);s=s.replace(a,b)}
 s="import {deriveClassOrder,frameClassifier} from '../../research/track-m/section15-derive-order.ts'\nimport {observeFieldLeaf} from './field-demand.ts'\n"+s
 replace('q.unit!==0&&arity===1?-2:','q.unit!==0&&arity===1?8:')
 replace(' const attempt=(index:number,scope:Path,end:number)', ' let deriveClassPhase=false\n const attempt=(index:number,scope:Path,end:number)')
 replace('  const reused=models.some(', "  if(deriveClassPhase)trace.push({stage:'derive-class-source',index,scope:[...path],hyps:part.hyps})\n  const reused=models.some(")
 const close=`     const extended=lemmaPath(available.map(s=>s.lemma),scope),lifted=liftCountProxies(numeric,g,proof,cert.reads,scope,extended,e=>trace.push({stage:'closure-transport',...e}),{deferCheck:true})
     const tree=lifted&&(options.conditional?markConditionalProof(g,lifted,available.map(s=>s.lemma)):inlineConditionalCuts(g,g,lifted,extended,scope,available.map(s=>s.lemma),wallEnd(),e=>trace.push({stage:'closure-inline',...e})))
     trace.push({stage:'closure-final',mode:'model-driven',fixedPoint,hyps:numeric.hyps.length,cuts:available.length,rounds:round+1,closedIndices:available.flatMap(s=>s.index===undefined?[]:[s.index]),outcome:tree?'checked':'untransported',ms:clock()-before,total:clock()-started});return tree`
 const oldStop="  const stop=(reason:string)=>{trace.push({stage:'closure-final',mode:'model-driven',outcome:'unknown',reason,path:[...scope],cuts:active(saved,scope).length,ms:clock()-before,total:clock()-started});return undefined}"
 replace(oldStop,`  const close=(numeric:Goal,available:Saved[],proof:Tree,roundCount:number):Tree|undefined=>{\n${close.replace('rounds:round+1','rounds:roundCount')}\n  }
  const stop=(reason:string):Tree|undefined=>{
   if(building()&&['no-numeric-model','batch-exhausted','no-unexcluded-violated-fact'].includes(reason)){
    const numeric=numericFor(),natural=proveNaturalCases(numeric,scope,end,trace,{deferCheck:true});trace.push({stage:'derive-natural-last',reason,proved:!!natural})
    if(natural)return close(numeric,active(saved,scope),natural,0)
   }
   trace.push({stage:'closure-final',mode:'model-driven',outcome:'unknown',reason,path:[...scope],cuts:active(saved,scope).length,ms:clock()-before,total:clock()-started});return undefined
  }`)
 const oldTry='  try{\n   for(let round=0;round<=pool.length&&building();round++){'
 replace(oldTry,`  try{
   const classVersion=saved.length,bodies=new Map<string,ReturnType<typeof countsForReads>>()
   const body=(id:string)=>{let c=bodies.get(id);if(!bodies.has(id)){const read=cert.reads.find(r=>r[0]===id);c=read?countsForReads(ds,[read]):undefined;bodies.set(id,c)}return c?.[0]}
   const sameFrame=frameClassifier(scope)
   const classes=deriveClassOrder(pool.map(index=>{const q=cert.insts[index]!,v=vector(q),reverse={...q,terms:q.terms.map(([z,id])=>[-z,id] as [number,string])};return {index,zero:q.unit!==0&&q.terms.length===1,frame:frame(index)&&sameFrame(body(q.terms[0]![1]),body(q.terms[1]![1])),monotone:bridges.has(v),member:memberHints.has(v),alias:inclusion(q)&&inclusion(reverse),partition:!conditional(index)&&q.terms.length===3}}))
   deriveClassPhase=true
   try{for(const index of classes){
    if(!building())break
    const h=g.hyps[raw.length+index];if(h?.op!=='or'||h.xs[0]?.op!=='<=')continue
    if(truth(h.xs[0],lemmaPath(active(saved,scope).map(s=>s.lemma),scope))!==undefined)continue
    const candidate=memberHints.has(vector(cert.insts[index]!))?scopesFor(index).map(merge).find(p=>p&&p!==scope)??scope:scope
    const started=clock(),outcome=attempt(index,candidate,end);trace.push({stage:'derive-class-attempt',index,outcome,units:clock()-started})
   }}finally{deriveClassPhase=false}
   for(let round=0;round<=pool.length&&building();round++){`)
 replace("rounds++;const available=active(saved,scope),numeric=numericFor(),natural=proveNaturalCases(numeric,scope,end,trace,{deferCheck:true}),q=natural?{tree:natural}:modelSequence(scope)(numeric,end)","rounds++;const available=active(saved,scope),numeric=numericFor(),q=modelSequence(scope)(numeric,end)\n    if(!('tree'in q))observeFieldLeaf(numeric,scope,q)")
 replace('    if(proof){\n'+close+'\n    }','    if(proof)return close(numeric,available,proof,round+1)')
 replace("    if('tree'in q||q.stuck!=='sat'||!q.witness)return stop('no-numeric-model')",`    if('tree'in q||q.stuck!=='sat'||!q.witness)return stop('no-numeric-model')
    const classGuard=saved.slice(classVersion).flatMap(s=>s.lemma.when).find(atom=>scalarAtoms.has(canon(atom))&&decide(atom,scope)===undefined)
    if(classGuard){if(depth>=8)return stop('scalar-depth');const yes=scalar(put(scope,classGuard,true),end,depth+1),no=yes&&scalar(put(scope,classGuard,false),end,depth+1);return yes&&no?{split:classGuard,yes,no}:undefined}`)
 writeFileSync(path,s)
 const demandPath='core/count-recovery/field-demand.ts',demand=readFileSync(demandPath,'utf8'),anchor='candidate,path:new Map(path),demand,source'
 if(demand.split(anchor).length!==2)throw Error('demand anchor changed')
 writeFileSync(demandPath,demand.replace(anchor,'candidate,path:new Map(path),demand:demand??fieldDemandAt(path),source'))
 console.log(JSON.stringify({researchOnly:true,deriveFirst:true,cap:24,sourceModelsRevalidated:true,sharedBareSatExclusions:false,before:createHash('sha256').update(before).digest('hex'),after:createHash('sha256').update(s).digest('hex')}))
}
