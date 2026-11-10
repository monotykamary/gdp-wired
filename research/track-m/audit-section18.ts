// Recheck captured proofs and cost ledgers. No proof search.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {homedir} from 'node:os'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
import {strict as assert} from 'node:assert'
import {canon,check,termColumn,columnTerm,type Path} from '../../kernel/kernel.ts'
import {fullWork,fullRate} from '../../kernel/prove.ts'
import {markConditionalProof,checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
import {normalize,dependence,independent,inequalityKey} from './section18-data.ts'
import {unpack} from './section18-codec.ts'
import {dependencies,lemmaRecorder} from './section18-recorder.ts'
import {statement} from './section16-statements.ts'
const hash=(x:string|Buffer)=>createHash('sha256').update(x).digest('hex'),near=(a:number,b:number)=>Math.abs(a-b)<1e-6*Math.max(1,Math.abs(a),Math.abs(b))
const signature=inequalityKey
const linC=(lin:any)=>({op:'<=',a:Object.entries(lin).reduce<any>((a,[name,k])=>({op:'add',a,b:name==='1'?{op:'const',value:k}:{op:'mul',k,a:{op:'var',name}}}),{op:'const',value:0}),b:{op:'const',value:0}})
const pathOf=(when:any[],cut:any):Path=>{const p:Path=new Map();let n=0;for(const a of [{lin:cut,holds:false},...when.map(lin=>({lin,holds:true}))]){const id=canon(a.lin);p.set(p.has(id)?'@'+n++:id,a)}return p}
if(process.argv[3]==='--one'){
 const x=unpack(readFileSync(process.argv[2]!,'utf8')),out=process.argv[4]!;assert.equal(x.allowance,5000);assert.equal(x.wallAllowance,4800);assert.equal(x.t12,false);assert(!x.error)
 for(const [i,t]of x.columns.entries())assert.equal(termColumn(t),`⟦${i}⟧`)
 const frames=x.frames as any[],byId=new Map(frames.map(f=>[f.id,f]));for(const f of frames){assert(near(f.units,f.end-f.start));assert(near(f.exclusive,f.units-f.children));assert(f.exclusive>=-1e-6)}
 const records:any[]=[];let checks=0
 for(const r of x.results){
  const norm=(v:any)=>normalize(v,r.reads,columnTerm);assert.equal(JSON.stringify(norm(r.statement)),r.key)
  const marks=new WeakMap<object,any>(),restore=(tree:any,snapshots:any[])=>{for(const s of snapshots){let t=tree;for(const p of s.path)t=t[p];marks.set(t,{goal:s.goal,lemmas:s.lemmas});markConditionalProof(s.goal,t,s.lemmas)}}
  if(r.sourceTree)restore(r.sourceTree,r.sourceMarks??[]);if(r.tree)restore(r.tree,r.targetMarks??[])
  if(r.sourceTree){assert.equal(checkConditionalProof(r.source,r.sourceTree,new Map(r.sourcePath)),r.sourceChecked);checks++}
  if(r.tree){assert.equal(checkConditionalProof(r.target,r.tree,new Map(r.targetPath)),r.targetChecked);checks++}
  let actualPremises=r.premises
  if(r.sourceChecked){const used=dependencies(r.source,r.sourceTree,new Map(r.sourcePath),t=>marks.get(t));assert.deepEqual(used.indices,r.premises.indices);assert.deepEqual(used.indices.map(i=>norm(r.source.hyps[i])),r.premises.premises);actualPremises={indices:used.indices,premises:used.indices.map(i=>norm(r.source.hyps[i])),path:used.atoms.map(atom=>({holds:atom.holds,condition:norm(lemmaRecorder.conditions(atom.lin))}))}}
  if(r.rootChecked){const p=r.rootProof;assert(!p.lemma.when.length);assert(check(p.goal,p.lemma.tree,pathOf([],p.lemma.cut)));assert.deepEqual(dependence(norm(p.goal.hyps),x.stateFields),p.dependence);checks++}
  let targetPremises:any=null
  if(r.targetChecked){const used=dependencies(r.target,r.tree,new Map(r.targetPath),t=>marks.get(t));targetPremises={indices:used.indices,premises:used.indices.map(i=>norm(r.target.hyps[i])),path:used.atoms.map(atom=>({holds:atom.holds,condition:norm(lemmaRecorder.conditions(atom.lin))}))}}
  assert.equal(r.eligible,!!(r.targetChecked&&r.rootChecked&&independent(r.literal)&&independent(r.rootDependence)))
  let rootLift=r.rootChecked?r.rootProof:undefined
  if(r.targetChecked&&!r.literal.op&&!rootLift&&x.root){
   const atom=(r.targetPath as any[]).map(([,a])=>a).find(a=>!a.holds&&signature(norm(linC(a.lin)))===signature(r.statement))
   if(atom)for(const [goal,tree,path,accepted]of [[r.source,r.sourceTree,r.sourcePath,r.sourceChecked],[r.target,r.tree,r.targetPath,r.targetChecked]]){if(!accepted)continue;const before=fullWork()/fullRate,lemma=admitConditionalCut(x.root,goal,tree,new Map(path),new Map(),atom.lin,[],Infinity);if(lemma&&!lemma.when.length){const small={...x.root,hyps:(lemma.slice??x.root.hyps.map((_:any,i:number)=>i)).map((i:number)=>x.root.hyps[i])};assert(check(small,lemma.tree,pathOf([],lemma.cut)));rootLift={goal:small,lemma,cost:fullWork()/fullRate-before,dependence:dependence(norm(small.hyps),x.stateFields)};checks++;break}}
  }
  const opIndependentRoot=!!(r.targetChecked&&!r.literal.op&&rootLift)
  assert(near(Object.values(r.units).reduce((a:any,b:any)=>a+b,0) as number,r.totalExclusive))
  const a=byId.get(r.id);assert(a);assert(a.kind==='attempt')
  const {source:_source,sourceTree:_sourceTree,sourcePath,target:_target,tree:_tree,targetPath,rootProof:_rootProof,reads:_reads,sourceMarks:_sourceMarks,targetMarks:_targetMarks,...small}=r
  records.push({...small,key:inequalityKey(r.statement),opIndependentRoot,rootLiftCertificate:rootLift,premises:actualPremises,targetPremises,proofDependence:actualPremises||targetPremises?dependence([actualPremises?.premises,actualPremises?.path,targetPremises?.premises,targetPremises?.path],x.stateFields):null,statementText:statement({bound:r.statement})?.text,sourcePath,targetPath,rootAdmissionUnits:rootLift?.cost??r.rootAdmissionUnits})
 }
 assert(near(x.helperRootUnits,x.attemptUnits+x.nonAttemptHelperUnits));assert(near(records.reduce((n,r)=>n+r.totalExclusive,0),x.attemptUnits));assert(x.nonAttemptHelperUnits>=-1e-6)
 const split={helperOther:x.nonAttemptHelperUnits,setup:0,failed:0,source:0,check:0,transport:0};for(const r of records)for(const k of Object.keys(r.units))split[k as keyof typeof split]+=r.units[k]
 assert(near(Object.values(split).reduce((a,b)=>a+b,0),x.helperRootUnits))
 const helperTotals={field:0,frame:0};for(const f of frames.filter(f=>f.kind==='helper')){let p=f.parent,nested=false;while(p!==undefined){const a=byId.get(p);if(a?.kind==='helper'){nested=true;break}p=a?.parent}if(!nested)helperTotals[f.name as keyof typeof helperTotals]+=f.units}
 const auditExtraColumns=[];for(let i=x.columns.length;;i++){const t=columnTerm(`⟦${i}⟧`);if(t===undefined)break;auditExtraColumns.push(t)}
 const result={auditExtraColumns,helperTotals,law:x.law,op:x.op,mode:x.mode,closed:x.closed,searchUnits:x.searchUnits,searchWallMs:x.searchWallMs,auditUnits:x.auditUnits,auditWallMs:x.auditWallMs,helperUnits:x.helperRootUnits,outsideHelpers:x.searchUnits-x.helperRootUnits,split,checks,rootSignature:x.root?hash(JSON.stringify(x.root)):null,records}
 writeFileSync(out,JSON.stringify(result)+'\n')
}else{
 const input=process.argv[2]!,manifest=JSON.parse(readFileSync(join(input,'archive-manifest.json'),'utf8')),tar=manifest.format==='tar.gz',bytes=readFileSync(join(input,tar?'receipts.tar.gz':'receipts.br'));assert.equal(hash(bytes),manifest.sha256)
 const tmp=mkdtempSync('/tmp/section18-audit-'),out=mkdtempSync(join(homedir(),'track-m-section18-audit-')),rows:any[]=[]
 const files:Record<string,string>=tar?{}:JSON.parse(brotliDecompressSync(bytes).toString())
 if(tar){const p=Bun.spawn(['tar','xzf',join(input,'receipts.tar.gz'),'-C',tmp]);assert.equal(await p.exited,0)}
 const text=(name:string)=>tar?readFileSync(join(tmp,name),'utf8'):files[name]!,integrity=JSON.parse(text('integrity.json'));assert(integrity.kernelIdentical);assert(!integrity.changed.some((p:string)=>p.startsWith('kernel/')));assert.equal(hash(text('replay.js')),text('runtime.sha256').split(/\s+/)[0])
 const names=tar?['overlap-op0','overlap-op4','star-op3','star-op5'].flatMap(s=>['control','observe'].map(m=>s+'-'+m+'/result.json')):Object.keys(files).filter(k=>k.endsWith('-result.json')).sort()
 for(const name of names){
  const raw=join(tmp,name),summary=raw+'.summary';if(!tar)writeFileSync(raw,files[name]!);const p=Bun.spawn([process.execPath,import.meta.path,raw,'--one',summary],{stdout:'inherit',stderr:'inherit'});assert.equal(await p.exited,0,name);rows.push(JSON.parse(readFileSync(summary,'utf8')))
 }
 const observed=rows.filter(r=>r.mode==='observe'),groups=new Map<string,any[]>(),eligible=new Map<string,any[]>(),rootEligible=new Map<string,any[]>()
 for(const row of observed)for(const r of row.records){if(r.emitted&&r.targetChecked){const xs=groups.get(r.key)??[];xs.push({law:row.law,op:row.op,id:r.id,statement:r.statement,statementText:r.statementText});groups.set(r.key,xs)}if(r.eligible){const key=JSON.stringify([row.law,row.rootSignature,r.key]),xs=eligible.get(key)??[];xs.push({...r,law:row.law,op:row.op,rootSignature:row.rootSignature});eligible.set(key,xs)}if(r.opIndependentRoot){const key=JSON.stringify([row.law,row.rootSignature,r.key]),xs=rootEligible.get(key)??[];xs.push({...r,law:row.law,op:row.op,rootSignature:row.rootSignature});rootEligible.set(key,xs)}}
 const estimate=(which:Map<string,any[]>)=>[...new Set(observed.map(r=>r.law))].map(law=>{const covered=observed.filter(r=>r.law===law),gs=[...which.values()].filter(xs=>xs[0].law===law),baseline=covered.reduce((n,r)=>n+r.searchUnits,0),duplicates=gs.flatMap(xs=>xs.slice(1)),saving=duplicates.reduce((n,r)=>n+r.units.source+r.units.check,0),rootCost=gs.reduce((n,xs)=>n+xs[0].rootAdmissionUnits,0),fullSaving=gs.reduce((n,xs)=>n+covered.filter(row=>row.rootSignature===xs[0].rootSignature).flatMap(row=>row.records.filter((r:any)=>r.key===xs[0].key&&!(row.op===xs[0].op&&r.id===xs[0].id))).reduce((s,r)=>s+r.units.source+r.units.failed+r.units.check,0),0);return {law,ops:covered.map(r=>r.op),baseline,eligibleFacts:gs.length,eligibleInstances:gs.reduce((n,xs)=>n+xs.length,0),duplicateInstances:duplicates.length,savedSuccessfulSourceUnits:saving,firstRootTransportUnits:rootCost,remaining:baseline-saving+rootCost,cacheAllMatchingQuerySavings:fullSaving,cacheAllMatchingQueryRemaining:baseline-fullSaving+rootCost,wholeLaw:false,fixedTraceOnly:true}})
 const counterfactual=estimate(eligible),rootCounterfactual=estimate(rootEligible)
 const overlap=[...groups].map(([key,instances])=>({key,statement:instances[0].statement,statementText:instances[0].statementText,instances,laws:[...new Set(instances.map(r=>r.law))],ops:[...new Set(instances.map(r=>r.law+':'+r.op))]})),csv=['law,op,id,helper,phase,kind,statement,literal_op,literal_guard,literal_post,proof_op,proof_guard,proof_post,source_checked,target_checked,root_checked,reusable,op_independent_root,setup_units,failed_units,source_units,check_units,transport_units']
 const quote=(v:any)=>'"'+String(v??'').replaceAll('"','""')+'"'
 for(const row of observed)for(const r of row.records)csv.push([row.law,row.op,r.id,r.helper,r.phase,r.kind,r.statementText,r.literal.op,r.literal.guard,r.literal.postState,r.proofDependence?.op,r.proofDependence?.guard,r.proofDependence?.postState,r.sourceChecked,r.targetChecked,r.rootChecked,r.eligible,r.opIndependentRoot,r.units.setup,r.units.failed,r.units.source,r.units.check,r.units.transport].map(quote).join(','))
 writeFileSync(join(out,'summary.json'),JSON.stringify({researchOnly:true,inputSha256:manifest.sha256,rows,counterfactual,rootCounterfactual,overlap,eligibleGroups:[...eligible.values()],rootEligibleGroups:[...rootEligible.values()]},null,2)+'\n');writeFileSync(join(out,'lemmas.csv'),csv.join('\n')+'\n')
 console.log(JSON.stringify({output:out,rows:rows.map(({records,...r})=>({...r,attempts:records.length,emitted:records.filter((x:any)=>x.emitted).length,checked:records.filter((x:any)=>x.targetChecked).length,reusable:records.filter((x:any)=>x.eligible).length})),counterfactual,rootCounterfactual,crossLawStatements:overlap.filter(x=>x.laws.length>1).length,crossOpStatements:overlap.filter(x=>x.ops.length>1).length}))
 const p=Bun.spawn([process.execPath,'research/track-m/pack-section10-archive.ts',join(out,'summary.json'),join(out,'lemmas.csv')],{stdout:'inherit',stderr:'inherit'});assert.equal(await p.exited,0)
 const rm=Bun.spawn(['rm','-rf','--',tmp]);assert.equal(await rm.exited,0)
}
