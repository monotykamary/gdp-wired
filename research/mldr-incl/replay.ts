// Frozen conditional safety packets. All additions are original universal
// instances; every returned numeric tree is checked against its rebuilt packet.
import {readFileSync} from 'node:fs'
import {type E,walkOnce,x} from '../../core/machine.ts'
import {countLawSeeds} from '../../core/count-focused.ts'
import {candidateWork,grammarPool,smallSelection} from '../../core/count-support.ts'
import {preferMemberInclusions,memberInclusions} from '../../core/count-recovery/member-inclusions.ts'
import {seedCountWitnessFlags} from '../../core/count-witness-flags.ts'
import {check,checkMC,countedObligations,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withWall} from '../../kernel/prove.ts'
const [file,mode='raw',msText='1000']=process.argv.slice(2),d=JSON.parse(readFileSync(file!,'utf8')),ms=Number(msText),start=performance.now(),work=fullWork()
const answer=withWall(start+Math.max(1000,ms*4),()=>counted(fullRate,()=>{
 const until=clock()+ms
 let raw=d.rawGoal,decls=d.decls,cert=d.certificateRequest,goal=typeof d.goal==='object'?d.goal:d.hyps?{name:d.goal,hyps:d.hyps}:undefined,preferred=0,seeded=false,addedLawTerms=0,poolAdded=0
 if(raw&&decls&&cert&&d.machine){
  const m=d.machine,laws=d.laws,law=laws.find((l:any)=>l.name===d.law),index=laws.indexOf(law),own:E[]=[...(law?.forall?[x(law.forall+'#')]:[]),...(law?.keys??[]).map(x)],keyed=new Set<string>()
  walkOnce([m.step,m.assume],(o:any)=>{if(o.op==='get')walkOnce(o.key,(v:any)=>{if(v.op==='var'&&m.inputs.includes(v.name))keyed.add(v.name)})})
  const terms=[...own,...m.inputs.filter((n:string)=>keyed.has(n)).map(x)].slice(0,4)
  let at=d.instances
  const rebuild=()=>{const p=countedObligations(m,laws,{[law.name]:at},index).find(p=>p.goal.name===raw.name);if(!p)throw Error('rebuilt packet missing');raw=p.goal;decls=p.decls}
  if((mode==='keyed'||mode==='seeded')&&at){const next=countLawSeeds(m,laws,at,terms,terms);addedLawTerms=Object.values(next).reduce((n:number,ts:any)=>n+ts.length,0)-Object.values(at).reduce((n:number,ts:any)=>n+ts.length,0);at=next;rebuild()}
  const select=()=>{const pool=grammarPool(raw,decls,1000,candidateWork(),true,m);poolAdded+=pool.added.filter(a=>a.reason==='guarded member inclusion').length;preferred=memberInclusions(m,decls,pool.full.reads).length;const picked=smallSelection(raw,decls,pool.full,own,{reads:[],picks:[]});return preferMemberInclusions(m,decls,pool.full,picked)}
  if(mode!=='raw')cert=select()
  if(mode==='seeded'&&at){const next=seedCountWitnessFlags(m,at,[{decls,cert}],true);seeded=next!==at;at=next;rebuild();cert=select()}
  goal=mcGoal(raw.hyps,decls,cert)
 }
 if(!goal)throw Error('missing replay goal')
 const out=grow(goal,new Map(),{nodes:0,until}),proven='tree'in out,checked=proven&&(raw&&cert?checkMC(raw.hyps,decls,{...cert,tree:out.tree}):check(goal,out.tree))
 return {mode,ms,goal:goal.name,hyps:goal.hyps.length,preferred,seeded,addedLawTerms,poolAdded,proven,checked,...(!proven?{stuck:out.stuck,why:out.why}:{}),...(raw&&cert?{selected:cert.insts.map((q:any)=>({terms:q.terms,unit:q.unit}))}:{})}
},true))
console.log(JSON.stringify({...answer,wallMs:performance.now()-start,countedMs:(fullWork()-work)/fullRate}))
