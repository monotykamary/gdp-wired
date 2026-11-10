// Section 6 diagnostics only. No production module imports this file.
import {type C,x} from '../../core/machine.ts'
import {type CountCert,type CountDecl,type Goal,type LemmaCut,type Path,type Tree,canon,check,facts,lemmaPath,linear,substC} from '../../kernel/kernel.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {brokenOf,clock,rowsAt,widen,withDeadline} from '../../kernel/prove.ts'
import {refuteFast,scale,sub} from '../../core/solver.ts'
import {booleanCore} from '../../core/count-recovery/boolean-core.ts'
import {piecesAt,walkLive} from '../../core/count-recovery/live-dependencies.ts'
import {countsForReads,proposeCountFacts} from '../../core/count-facts.ts'
import {proposeCountUnions} from '../../core/count-unions.ts'
import {readFileSync} from 'node:fs'
import {gunzipSync,gzipSync} from 'node:zlib'
type Packet=Pick<CountCert,'reads'|'insts'>
const json=(o:unknown)=>JSON.stringify(o)
const put=(p:Path,lin:Record<string,number>,holds:boolean):Path=>new Map(p).set(canon(lin),{lin,holds})
const opposite=(a:{lin:Record<string,number>,holds:boolean})=>{if(a.holds)return a.lin;const q=scale(a.lin,-1);q['1']=(q['1']??0)+1;return q}
const proofPath=(l:LemmaCut):Path=>{const p:Path=new Map();for(const a of [{lin:l.cut,holds:false},...l.when.map(lin=>({lin,holds:true}))]){const k=canon(a.lin);p.set(p.has(k)?`@${p.size}`:k,a)}return p}
const fast=(g:Goal,p:Path):Tree|undefined=>{const q=refuteFast(rowsAt(g,p),256);const t=q?.kind==='refuted'?{leaf:q.steps}:undefined;return t&&check(g,t,p)?t:undefined}
const goalOf=(g:Goal,cert:Packet,root:Path,index:number,ctx:C[])=>{
 const raw=g.hyps.slice(0,-cert.insts.length),inst=cert.insts[index]!,maps=new Set(cert.reads.map(r=>r[1])),ids=new Set(cert.reads.map(r=>r[0])),wits=new Set(cert.insts.map(q=>q.wit))
 const relevant=raw.flatMap(c=>piecesAt(c,root)).filter(c=>{let skip=false;walkLive(c,root,(o:any)=>{if(o.op==='get'&&maps.has(o.map)||o.op==='var'&&(ids.has(o.name)||wits.has(o.name)&&o.name!==inst.wit))skip=true});return !skip})
 const h=g.hyps[raw.length+index]!;if(h.op!=='or'||h.xs[0]?.op!=='<=')throw new Error('missing count clause')
 return {goal:{name:g.name,hyps:[...relevant,...ctx,h,{op:'not' as const,x:h.xs[0]}]},relevant,good:h.xs[0],h}
}
const profile=(file:string)=>{const xs=readFileSync(file,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l));return JSON.parse(gunzipSync(Buffer.from(xs.find(p=>p.artifact==='source-profile').data,'base64')).toString())}
export function starTests(g:Goal,cert:Packet,root:Path,file:string){
 const old=profile(file),prior=old.sources.filter((s:any)=>s.checked&&s.index<39),ctx:C[]=prior.map((s:any)=>goalOf(g,cert,root,s.index,[]).good)
 if(g.hyps.length!==406||cert.insts.length!==73||prior.length!==11)throw new Error('not the requested Inv* fixture/prefix')
 const unknown=old.sources.filter((s:any)=>!s.checked)
 for(const s of old.sources)if(json(s.terms)!==json(cert.insts[s.index]!.terms))throw new Error('captured instance changed')
 const original=old.sources.find((s:any)=>s.index===39),choices=Object.values(original.columns) as any[]
 const conditional=choices.find(c=>c.op==='if'&&c.then?.op==='get'&&c.then.key?.name==='j$')
 if(!conditional)throw new Error('missing captured ceiling expression')
 const start=clock(),wall=performance.now(),until=start+150,base=goalOf(g,cert,root,39,ctx),guards=facts(conditional.c,root),guardCuts:{split:Record<string,number>,no:Tree}[]=[]
 let guarded=new Map(root),guardChecked=true
 for(const a of guards){if(guarded.get(canon(a))?.holds===true)continue;const no=fast(base.goal,put(guarded,a,false));if(!no){guardChecked=false;break}guardCuts.push({split:a,no});guarded=put(guarded,a,true)}
 const plain:C={op:'<=',a:conditional.then,b:{op:'get',map:'CT',key:x('i')}},a=linear(plain.a,guarded)!,b=linear(plain.b,guarded)!,cut=sub(a,b)
 if(Object.keys(cut).some(k=>k.startsWith('⟦')))throw new Error('ceiling still opaque')
 const lemma:LemmaCut={when:[...root.values()].map(opposite).concat(guards),cut,tree:{leaf:[]},slice:base.relevant.map((_,i)=>i)},pp=proofPath(lemma),scalar={...base.goal,hyps:base.relevant}
 const ceilingStart=clock(),scalarProof=fast(scalar,pp),ceilingChecked=!!scalarProof,ceilingUnits=clock()-ceilingStart
 if(scalarProof)lemma.tree=scalarProof
 const path=lemmaPath([lemma],guarded),active=path.get(canon(cut))?.holds===true,events:any[]=[]
 let q:any,tree:Tree|undefined,coreSize:number|undefined,queryUnits=0,booleanUnits=0,checked=false
 if(guardChecked&&ceilingChecked&&active&&clock()<until){
  const t=clock();q=modelSequence(path)(base.goal,until);queryUnits=clock()-t
  tree='tree'in q?q.tree:undefined;coreSize=q.core?.length
  if(!tree&&q.why===REFUTED&&coreSize&&coreSize<=8&&clock()<until){
   const reduced={...base.goal,hyps:q.core.map((i:number)=>base.goal.hyps[i]!)},at=clock()
   const tiny=booleanCore(reduced,path,new Set([cert.insts[39]!.wit]),until,events,{deferCheck:true,scalarGuards:true,extended:true,model:true})
   tree=tiny&&withDeadline(until,()=>widen(reduced,base.goal,tiny,{},path,path));booleanUnits=clock()-at
  }
  if(tree&&check(base.goal,tree,path)){
   const yesPath=put(guarded,cut,true),noPath=put(guarded,cut,false)
   const yes=withDeadline(until,()=>widen(base.goal,base.goal,tree!,{},path,yesPath)),no=withDeadline(until,()=>widen(scalar,base.goal,scalarProof!,{},pp,noPath))
   let closed:Tree|undefined=yes&&no?{split:cut,yes,no}:undefined
   for(let i=guardCuts.length-1;closed&&i>=0;i--)closed={split:guardCuts[i]!.split,yes:closed,no:guardCuts[i]!.no}
   checked=!!closed&&check(base.goal,closed,root);tree=closed
  }
 }
 console.log(json({test:'T1',scope:'union source conditional on the 11 previously checked count facts',prefix:prior.map((s:any)=>s.index),sourceHyps:base.goal.hyps.length,guardChecked,guardBranches:guardCuts.length,plainCut:cut,opaqueCut:false,when:lemma.when,ceilingChecked,ceilingUnits,active,queryOutcome:q&&('tree'in q?'tree':q.stuck),queryWhy:q?.why,coreSize,queryUnits,booleanUnits,proposed:!!tree,checked,countedUnits:clock()-start,wallMs:performance.now()-wall,events}))
 if(checked)console.log(json({artifact:'T1-conditional-source-proof',encoding:'gzip-base64',data:gzipSync(json({goal:base.goal,root:[...root],tree,lemma})).toString('base64')}))
 const t2start=clock(),t2wall=performance.now(),results:any[]=[]
 // Test all 19 observed unknowns, retaining the 14/4/1 arity distinction.
 for(const s of unknown){
  const part=goalOf(g,cert,root,s.index,[...ctx,...(ceilingChecked&&guardChecked?[plain]:[])]).goal,t=clock(),w=performance.now()
  const out=modelSequence(guarded)(part,t+50),outcome='tree'in out?'tree':out.stuck
  results.push({index:s.index,arity:cert.insts[s.index]!.terms.length,wit:s.wit,hyps:part.hyps.length,outcome,why:'tree'in out?undefined:out.why,coreSize:out.core?.length,countedUnits:clock()-t,wallMs:performance.now()-w,...(!('tree'in out)&&out.stuck==='sat'&&out.witness?{model:out.witness,modelValid:brokenOf(part)(out.witness).length===0}:{})})
 }
 const first=results.find(r=>r.outcome==='sat'&&r.modelValid),reuse=first?results.filter(r=>r.index!==first.index).map(r=>{
  const part=goalOf(g,cert,root,r.index,[...ctx,...(ceilingChecked&&guardChecked?[plain]:[])]).goal
  const renamed={...part,hyps:part.hyps.map(c=>substC(c,{vars:{[r.wit]:x(first.wit)},maps:{},flags:{}}))},broken=brokenOf(renamed)(first.model),tiny=brokenOf({...renamed,hyps:renamed.hyps.slice(-2)})(first.model)
  return {index:r.index,arity:r.arity,pairSatisfied:tiny.length===0,fullSourceSatisfied:broken.length===0,broken}
 }):[]
 console.log(json({test:'T2',requested:results.length,arityCounts:results.reduce((o,r)=>(o[r.arity]=(o[r.arity]??0)+1,o),{} as Record<string,number>),ceilingChecked,countedUnits:clock()-t2start,wallMs:performance.now()-t2wall,results,reuseFrom:first?.index,reuse,reusedFull:reuse.filter(r=>r.fullSourceSatisfied).length,reusedPairs:reuse.filter(r=>r.pairSatisfied).length}))
}
export function generatorTest(g:Goal,ds:CountDecl[],cert:Packet){
 const wall=performance.now(),start=clock(),counts=countsForReads(ds,cert.reads);if(!counts||cert.reads.length!==41)throw new Error('not packet A: 41 reads')
 const last=json(g.hyps.at(-1)),own=(t:any)=>t.op==='const'||t.op==='var'&&last.includes(`"name":${json(t.name)}`),ranked=(r:any)=>own(r[2])||last.includes(json([r[1],r[2]]))
 const keyless=(r:any)=>{const d=ds.find(d=>d.map===r[1])!;return !json([d.below,d.body]).includes(`"name":${json(d.j)}`)}
 const heads=cert.reads.filter(ranked).sort((a,b)=>Number(b[1].endsWith('#'))-Number(a[1].endsWith('#'))),carried=cert.reads.filter(r=>!r[1].endsWith('#')&&keyless(r))
 const pairs:[string,string][]=heads.flatMap(a=>carried.filter(b=>a!==b&&json(counts.find(c=>c.v===a[0])!.below)===json(counts.find(c=>c.v===b[0])!.below)).map(b=>[a[0],b[0]] as [string,string]))
 const f=proposeCountFacts(counts,g,{maxFacts:4096,maxCounts:128,maxAtoms:12,reserved:cert.insts.map(i=>i.wit)}),u=proposeCountUnions(counts,pairs,Infinity)
 const signature=(terms:[number,string][])=>json([...terms].sort((a,b)=>a[1].localeCompare(b[1])))
 const targets:Record<string,[number,string][]>= {R2:[[1,'r$9'],[1,'r$16'],[-1,'r$24'],[-1,'r$25'],[-1,'r$26']],R5X:[[1,'r$7'],[-1,'r$10'],[-1,'r$11']],R5S:[[1,'r$8'],[-1,'r$12'],[-1,'r$11']]}
 const matches=Object.fromEntries(Object.entries(targets).map(([name,terms])=>[name,{terms,facts:f.insts.filter(q=>q.unit===0&&signature(q.terms)===signature(terms)),unions:u.filter(q=>q.unit===0&&signature(q.terms)===signature(terms)),reverseFacts:f.insts.filter(q=>q.unit===0&&signature(q.terms)===signature(terms.map(([k,v])=>[-k,v]))),reverseUnions:u.filter(q=>q.unit===0&&signature(q.terms)===signature(terms.map(([k,v])=>[-k,v])))}]))
 console.log(json({test:'T3',reads:cert.reads,positivePairs:pairs,pairPresent:pairs.some(([a,b])=>a==='r$16'&&b==='r$9'),legacyInstances:cert.insts.length,legacyArity5:cert.insts.filter(q=>q.terms.length===5).length,facts:f.insts.length,factsHardLimit:4096,factsLimitHit:f.insts.length===4096,skipped:f.skipped,unions:u.length,unionLimit:'Infinity',matches,countedUnits:clock()-start,wallMs:performance.now()-wall}))
}
