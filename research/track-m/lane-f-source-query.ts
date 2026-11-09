// Conditional diagnostic of one exact closure source; no new trusted facts.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {mcGoal,termColumn,linear,type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import {atPoint,clock,fullWork,fullRate,counted,withWall,withDeadline} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {walkLive,piecesAt,sourceScalarContext} from '../../core/count-recovery/live-dependencies.ts'
import {modelSequence,grow,widen,check,refuteFast,rowsAt} from '../../core/count-recovery/ops.ts'
import {foldPath} from '../../core/count-recovery/fold-path.ts'
import {booleanCore} from '../../core/count-recovery/boolean-core.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
import {sub} from '../../core/solver.ts'
import {pack,unpack} from './section18-codec.ts'
const sourceBudget=Number(process.env.LAB_SOURCE_UNITS??150);if(!(sourceBudget>0&&sourceBudget<=1000))throw Error('bounded source audit required')
const queryBudget=Number(process.env.LAB_QUERY_UNITS??250),coreBudget=Number(process.env.LAB_CORE_UNITS??sourceBudget),reconstructionPoint=process.env.LAB_POINT??'on'
if(!(queryBudget>0&&queryBudget<=250&&coreBudget>0&&coreBudget<=1000)||!['on','off'].includes(reconstructionPoint))throw Error('invalid reconstruction settings')
const [input,traceFile,mode,out]=process.argv.slice(2),context=readFileSync(input!,'utf8'),{p}=unpack(context),traceData=JSON.parse(readFileSync(traceFile!,'utf8'))
const contextSha256=createHash('sha256').update(context).digest('hex')
if(!out||!mode)throw Error('CONTEXT TRACE MODE OUT')
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
const cert=focusCountCert(p.m,p.packet.decls,certFor(p.packet.goal,p.packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.packet.goal.hyps.at(-1)}),g=mcGoal(p.packet.goal.hyps,p.packet.decls,cert)!
const triangles=cert.insts.flatMap((q,index)=>q.unit===0&&q.terms.length===3&&q.wit.startsWith('writeFrame$')?[{index,q}]:[])
const triangleMatch=mode.match(/^triangle-(\d+)-/),triangleOrdinal=triangleMatch?Number(triangleMatch[1]):undefined
if(mode.startsWith('triangle-')&&(!triangleMatch||!Number.isSafeInteger(triangleOrdinal)))throw Error('invalid triangle ordinal')
const index=triangleOrdinal===undefined?(mode.includes('-zero-')?cert.insts.findIndex(q=>q.unit===0&&q.terms.length===1&&q.terms[0]![0]===1&&q.terms[0]![1]===cert.insts[0]!.terms[0]![1]):0):triangles[triangleOrdinal]?.index
if(index===undefined||index<0)throw Error('requested source instance absent')
const scope:Path=new Map(traceData.events.filter((e:any)=>e.stage==='closure-final').at(-1).path),raw=g.hyps.slice(0,-cert.insts.length),inst=cert.insts[index]!,h=g.hyps[raw.length+index]!,good=(h as any).xs[0]
const ids=new Set(cert.reads.map(r=>r[0])),maps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(q=>q.wit))
const source=raw.flatMap(c=>piecesAt(c,scope)).filter(c=>{let skip=false;const owners=new Set<string>();walkLive(c,scope,(o:any)=>{if(o.op==='get'&&maps.has(o.map)||o.op==='var'&&ids.has(o.name))skip=true;else if(o.op==='var'&&wits.has(o.name))owners.add(o.name)});return !skip&&owners.size<=1&&(!owners.size||owners.has(inst.wit))})
const part:Goal={name:g.name,hyps:[...(mode.startsWith('tiny')?[]:source),h,{op:'not',x:good}]},events:object[]=[],start=performance.now(),work=fullWork();let tree:Tree|undefined,error:string|undefined,coreIndices:number[]|undefined,coreQueryUnits:number|undefined,coreSearchUnits:number|undefined,queryHyps=part.hyps.length,reconstructionHyps=0,coreTree=false,coreWidened=false
try{withWall(start+7000,()=>counted(fullRate,()=>withDeadline(clock()+sourceBudget+50,()=>{
 const end=clock()+sourceBudget
 if(mode.includes('-core-')){
  const queryStart=clock();let queryGoal=part
  if(mode.includes('-projected-')){
   const names=new Set<string>();walkLive(h,scope,(o:any)=>{if(o.op==='var')names.add(o.name)})
   const last=part.hyps.at(-1)!,seed={name:part.name,hyps:part.hyps.slice(-2)},projected=sourceScalarContext(part,seed,names,scope)
   queryGoal={...projected,hyps:[...projected.hyps.filter(c=>c!==last),last]}
  }
  queryHyps=queryGoal.hyps.length
  const q=modelSequence(scope)(queryGoal,Math.min(end,queryStart+queryBudget));coreQueryUnits=clock()-queryStart;events.push(q)
  if('tree'in q)tree=queryGoal===part?q.tree:widen(queryGoal,part,q.tree,{},scope,scope)
  else if(q.why==='refuted, not unfolded'&&q.core?.length){
   coreIndices=[...new Set(q.core)]
   if(coreIndices.some(i=>!Number.isInteger(i)||i<0||i>=queryGoal.hyps.length))throw Error('invalid source core')
   const reduced:Goal={name:part.name,hyps:coreIndices.map(i=>queryGoal.hyps[i]!)},small=mode.includes('-context-')?queryGoal:reduced,coreStart=clock(),coreEnd=Math.min(end,clock()+coreBudget),oldPoint=atPoint.on;let proof:Tree|undefined
   reconstructionHyps=small.hyps.length
   if(reconstructionPoint==='off')atPoint.on=false
   try{withDeadline(coreEnd,()=>{
    if(mode.endsWith('boolean'))proof=booleanCore(small,scope,new Set([inst.wit]),coreEnd,events,{deferCheck:true,extended:true,scalarGuards:true,model:true})
    else if(mode.endsWith('folded')){
     const folded=foldPath(small,scope),r=grow(folded.goal,scope,{nodes:0,until:coreEnd,units:true})
     if('tree'in r)proof=widen(folded.goal,small,r.tree,folded.opaque,scope,scope)
     else events.push({stage:'core-folded',stuck:r.stuck,why:r.why})
    }else{
     const r=grow(small,scope,{nodes:0,until:coreEnd,units:true})
     if('tree'in r)proof=r.tree
     else events.push({stage:'core-grow',stuck:r.stuck,why:r.why})
    }
    coreTree=!!proof
    if(proof)tree=widen(small,part,proof,{},scope,scope)
    coreWidened=!!tree
   })}finally{atPoint.on=oldPoint;coreSearchUnits=clock()-coreStart}
  }
 }else if(mode.endsWith('boolean'))tree=booleanCore(part,scope,new Set([inst.wit]),end,events,{deferCheck:true,extended:true,scalarGuards:true})
 else if(mode.endsWith('folded')){const folded=foldPath(part,scope),q=modelSequence(scope)(folded.goal,end);if('tree'in q)tree=widen(folded.goal,part,q.tree,folded.opaque,scope,scope);else events.push(q)}
 else if(mode.endsWith('fast')){const q=refuteFast(rowsAt(part,scope),512);if(q?.kind==='refuted')tree={leaf:q.steps}}
 else {const q=modelSequence(scope)(part,Math.min(end,clock()+(sourceBudget>150?250:sourceBudget)));if('tree'in q)tree=q.tree;else events.push(q);if(mode.endsWith('grow')&&!tree){const r=grow(part,scope,{nodes:0,until:end,units:true});if('tree'in r)tree=r.tree}}
}),true))}catch(e){error=String(e)}
const searchUnits=(fullWork()-work)/fullRate,searchWallMs=performance.now()-start,checked=!!tree&&check(part,tree,scope),a=linear(good.a,scope),b=linear(good.b,scope),lemma=checked&&a&&b?admitConditionalCut(g,part,tree!,scope,scope,sub(a,b),[],performance.now()+1000):undefined
const result={mode,sourceBudget,queryBudget,coreBudget,reconstructionPoint,queryHyps,reconstructionHyps,coreQueryUnits,coreSearchUnits,contextSha256,triangleOrdinal,triangleCandidates:triangles.map(({index,q})=>({index,inst:q})),coreIndices,coreTree,coreWidened,index,inst,hyps:part.hyps.length,checked,admissible:!!lemma,error,searchUnits,searchWallMs,units:(fullWork()-work)/fullRate,wallMs:performance.now()-start,events}
mkdirSync(out,{recursive:true});writeFileSync(join(out,'result.json'),pack({result,part,tree,scope:[...scope],lemma}));console.log(JSON.stringify({...result,events:undefined}))
