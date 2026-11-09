// Conditional diagnostic of one exact closure source; no new trusted facts.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {mcGoal,termColumn,linear,type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import {clock,fullWork,fullRate,counted,withWall,withDeadline} from '../../kernel/prove.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {walkLive,piecesAt} from '../../core/count-recovery/live-dependencies.ts'
import {modelSequence,grow,widen,check,refuteFast,rowsAt} from '../../core/count-recovery/ops.ts'
import {foldPath} from '../../core/count-recovery/fold-path.ts'
import {booleanCore} from '../../core/count-recovery/boolean-core.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
import {sub} from '../../core/solver.ts'
import {pack,unpack} from './section18-codec.ts'
const [input,traceFile,mode,out]=process.argv.slice(2),{p}=unpack(readFileSync(input!,'utf8')),traceData=JSON.parse(readFileSync(traceFile!,'utf8'))
if(!out||!mode)throw Error('CONTEXT TRACE MODE OUT')
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
const cert=focusCountCert(p.m,p.packet.decls,certFor(p.packet.goal,p.packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.packet.goal.hyps.at(-1)}),g=mcGoal(p.packet.goal.hyps,p.packet.decls,cert)!
const index=mode.includes('-zero-')?cert.insts.findIndex(q=>q.unit===0&&q.terms.length===1&&q.terms[0]![0]===1&&q.terms[0]![1]===cert.insts[0]!.terms[0]![1]):0
if(index<0)throw Error('zero-count instance absent')
const scope:Path=new Map(traceData.events.filter((e:any)=>e.stage==='closure-final').at(-1).path),raw=g.hyps.slice(0,-cert.insts.length),inst=cert.insts[index]!,h=g.hyps[raw.length+index]!,good=(h as any).xs[0]
const ids=new Set(cert.reads.map(r=>r[0])),maps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(q=>q.wit))
const source=raw.flatMap(c=>piecesAt(c,scope)).filter(c=>{let skip=false;const owners=new Set<string>();walkLive(c,scope,(o:any)=>{if(o.op==='get'&&maps.has(o.map)||o.op==='var'&&ids.has(o.name))skip=true;else if(o.op==='var'&&wits.has(o.name))owners.add(o.name)});return !skip&&owners.size<=1&&(!owners.size||owners.has(inst.wit))})
const part:Goal={name:g.name,hyps:[...(mode.startsWith('tiny')?[]:source),h,{op:'not',x:good}]},events:object[]=[],start=performance.now(),work=fullWork();let tree:Tree|undefined,error:string|undefined
try{withWall(start+2500,()=>counted(fullRate,()=>withDeadline(clock()+200,()=>{
 const end=clock()+150
 if(mode.endsWith('boolean'))tree=booleanCore(part,scope,new Set([inst.wit]),end,events,{deferCheck:true,extended:true,scalarGuards:true})
 else if(mode.endsWith('folded')){const folded=foldPath(part,scope),q=modelSequence(scope)(folded.goal,end);if('tree'in q)tree=widen(folded.goal,part,q.tree,folded.opaque,scope,scope);else events.push(q)}
 else if(mode.endsWith('fast')){const q=refuteFast(rowsAt(part,scope),512);if(q?.kind==='refuted')tree={leaf:q.steps}}
 else {const q=modelSequence(scope)(part,end);if('tree'in q)tree=q.tree;else events.push(q);if(mode.endsWith('grow')&&!tree){const r=grow(part,scope,{nodes:0,until:end,units:true});if('tree'in r)tree=r.tree}}
}),true))}catch(e){error=String(e)}
const searchUnits=(fullWork()-work)/fullRate,searchWallMs=performance.now()-start,checked=!!tree&&check(part,tree,scope),a=linear(good.a,scope),b=linear(good.b,scope),lemma=checked&&a&&b?admitConditionalCut(g,part,tree!,scope,scope,sub(a,b),[],performance.now()+1000):undefined
const result={mode,index,inst,hyps:part.hyps.length,checked,admissible:!!lemma,error,searchUnits,searchWallMs,units:(fullWork()-work)/fullRate,wallMs:performance.now()-start,events}
mkdirSync(out,{recursive:true});writeFileSync(join(out,'result.json'),pack({result,part,tree,scope:[...scope],lemma}));console.log(JSON.stringify({...result,events:undefined}))
