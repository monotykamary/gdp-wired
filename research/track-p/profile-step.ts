// Per-phase research replay; no changed budgets, no additional proof premises.
import {readFileSync} from 'node:fs'
import {gzipSync} from 'node:zlib'
import {type Machine,type Law,x} from '../../core/machine.ts'
import {type Goal,type CountDecl,type CountCert,type Instances,countedObligations,mcGoal,checkMC} from '../../kernel/kernel.ts'
import {candidateWork,prepareSupport,grammarPool,polaritySelection,sparseReadInstances,countedInstanceSources} from '../../core/count-support.ts'
import {clock,counted,fullRate,grow,modelInstances,withDeadline,withWall,profile} from '../../kernel/prove.ts'
import {cdclStats} from '../../kernel/cdcl.ts'
const root=process.argv[2]!,mode=process.argv[3]??'legacy',target=Number(process.argv[4]??11),ms=1500
const data=JSON.parse(readFileSync(root+'/family.json','utf8')) as {machine:Machine,laws:Law[]},m=data.machine,indices=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74],laws=indices.map(i=>data.laws[i]!),law=data.laws[target]!
const stages:Record<string,number>={},time=<T>(stage:string,f:()=>T)=>{const t=performance.now();try{return f()}finally{stages[stage]=(stages[stage]??0)+performance.now()-t}}
const numeric=(value:object)=>Object.fromEntries(Object.entries(value).filter(([,v])=>typeof v==='number')) as Record<string,number>
const delta=(a:Record<string,number>,b:Record<string,number>)=>Object.fromEntries(Object.entries(b).map(([k,v])=>[k,v-(a[k]??0)]))
cdclStats.on=true;profile.on=true
const records:object[]=[],result:{outcome:string,why?:string,checked?:boolean,last?:{raw:Goal,decls:CountDecl[],gg:Goal,cert:Pick<CountCert,'reads'|'insts'|'picks'>,instances:Instances}}={outcome:'unknown'}
const t0=performance.now()
withWall(t0+2500,()=>counted(fullRate,()=>withDeadline(clock()+ms,()=>{
 const until=clock()+ms
 if(mode==='hand'){
  const pack=JSON.parse(readFileSync(root+'/c11-goal.json','utf8')) as {raw:Goal,decls:CountDecl[],gg:Goal}
  const cert=JSON.parse(readFileSync(root+'/c11-proof.json','utf8')) as CountCert
  const gg=time('encoding',()=>mcGoal(pack.raw.hyps,pack.decls,cert)!);result.last={...pack,gg,cert,instances:{}}
  const q=time('grow',()=>grow(gg,new Map(),{nodes:0,until}));result.outcome='tree'in q?'tree':q.stuck;result.why='tree'in q?'':q.why
  if('tree'in q)result.checked=time('check',()=>checkMC(pack.raw.hyps,pack.decls,{...cert,tree:q.tree}))
  return
 }
 const budget=candidateWork(),terms=[...(law.forall?[x(law.forall+'#')]:[]),...(law.keys??[]).map(x),...m.inputs.map(x)]
 const initial:Instances=mode==='seedless'?{}:Object.fromEntries(Object.entries(m.step.flags??{}).filter(([,q])=>q.op==='all'&&!q.keys?.length).map(([f])=>['?'+f,terms]))
 const prep=time('instanceGeneration',()=>prepareSupport(m,laws,law,initial,1,budget));let at=prep.at,seedCount=prep.seedCount
 const sources=countedInstanceSources(m,laws);let cached:ReturnType<typeof grammarPool>|undefined,cachedKey='',selected:Pick<CountCert,'reads'|'insts'|'picks'>|undefined
 for(let round=0;round<6&&clock()<until;round++){
  const {goal:raw,decls}=time('encoding',()=>countedObligations(m,laws,{[law.name]:at},laws.indexOf(law))[1]!)
  const key=JSON.stringify(Object.entries(at).filter(([name])=>sources.has(name))),hit=!!cached&&cachedKey===key
  const pool=hit?cached!:time('poolConstruction',()=>grammarPool(raw,decls,1000,budget));cached=pool;cachedKey=key
  if(mode==='legacy'||!selected||!hit)selected=time('selection',()=>polaritySelection(raw,decls,pool,budget,prep.sourceMaps).pick)
  const cert=selected,gg=time('encoding',()=>mcGoal(raw.hyps,decls,cert));if(!gg){result.why='invalid count proposal';break}
  result.last={raw,decls,gg,cert,instances:at}
  const seed=seedCount<64?time('closure',()=>sparseReadInstances(m,laws,law,at,gg,cert,64-seedCount,raw.hyps.at(-1),decls,prep.sourceMaps,raw.hyps.slice(0,-1),budget)):undefined
  records.push({round,rawHyps:raw.hyps.length,encodedHyps:gg.hyps.length,insts:cert.insts.length,readCount:cert.reads.length,added:seed?.added.length??0,budget:{...budget.state}})
  if(seed?.added.length){at=seed.at;seedCount+=seed.added.length;continue}
  const before=numeric(cdclStats),q=time('grow',()=>grow(gg,new Map(),{nodes:0,until}))
  records.push({round,searchStats:delta(before,numeric(cdclStats)),outcome:'tree'in q?'tree':q.stuck,why:'tree'in q?'':q.why})
  if('tree'in q){result.outcome='tree';result.checked=time('check',()=>checkMC(raw.hyps,decls,{...cert,tree:q.tree}));break}
  result.outcome=q.stuck;result.why=q.why
  const next=q.stuck==='sat'&&q.witness?time('modelInstances',()=>modelInstances(m,laws,at,gg,q.witness!)):undefined
  if(!next)break;at=next
 }
}),true))
const totalWallMs=performance.now()-t0,stats=numeric(cdclStats),summary={mode,target,outcome:result.outcome,checked:result.checked??false,why:result.why,totalWallMs,stages,outsideMeasuredStagesMs:totalWallMs-Object.values(stages).reduce((a,b)=>a+b,0),cdcl:stats,plain:{solves:profile.solves,solveMs:profile.solveMs,rowsMs:profile.rowsMs,nodes:profile.nodes},records}
console.log(JSON.stringify(summary));if(result.last)console.log('PACK_GZIP '+gzipSync(JSON.stringify(result.last)).toString('base64'))
