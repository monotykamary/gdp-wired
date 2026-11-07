// Generic emission audit. Reference indices are CLI data, not engine rules.
import {readFileSync} from 'node:fs'
import {type E,type Law,type Machine,x} from '../../core/machine.ts'
import {type CountCert,type Instances,mcGoal,countedObligations,substE} from '../../kernel/kernel.ts'
import {candidateWork,prepareSupport,grammarPool,polaritySelection,sparseReadInstances,countedInstanceSources,instId,keyId} from '../../core/count-support.ts'
export function auditSupport(m:Machine,laws:Law[],own:Law,required:Instances,hand:CountCert,flags:'all'|'none'='all'){
 const phaseMs:Record<string,number>={},timed=<T>(name:string,f:()=>T)=>{const t=performance.now();try{return f()}finally{phaseMs[name]=(phaseMs[name]??0)+performance.now()-t}}
 const target=laws.indexOf(own),budget=candidateWork(),terms=[...(own.forall?[x(own.forall+'#')]:[]),...(own.keys??[]).map(x),...m.inputs.map(x)]
 const initial:Instances=flags==='none'?{}:Object.fromEntries(Object.entries(m.step.flags??{}).filter(([,q])=>q.op==='all'&&!q.keys?.length).map(([f])=>['?'+f,terms]))
 const prep=timed('instanceGeneration',()=>prepareSupport(m,laws,own,initial,1,budget));let at=prep.at,admitted=prep.seedCount
 const sources=countedInstanceSources(m,laws);let cached:ReturnType<typeof grammarPool>|undefined,cachedKey='',poolBuilds=0,poolHits=0
 const requiredRows=Object.entries(required).flatMap(([name,values])=>{const law=laws.find(l=>l.name===name),width=name.startsWith('?')?1:1+(law?.keys?.length??0);return Array.from({length:values.length/width},(_,i)=>({name,tuple:values.slice(i*width,(i+1)*width)}))})
 const id=(name:string,tuple:E[])=>JSON.stringify([name,tuple.map(keyId)]),expected=new Set(requiredRows.map(r=>id(r.name,r.tuple)))
 const trace:object[]=[];const firstSeen=new Map<string,string>()
 const snapshot=(phase:string,c:Pick<CountCert,'reads'|'insts'>)=>{
  const aliases:Record<string,E>={};for(const i of c.insts){const match=hand.insts.find(h=>instId(h,hand.reads)===instId(i,c.reads));if(match)aliases[i.wit]=x(match.wit)}
  const rows=Object.entries(at).flatMap(([name,values])=>{const law=laws.find(l=>l.name===name),width=name.startsWith('?')?1:1+(law?.keys?.length??0);return Array.from({length:values.length/width},(_,i)=>({name,tuple:values.slice(i*width,(i+1)*width).map(t=>substE(t,{vars:aliases,maps:{},flags:{}}))}))})
  for(const r of rows){const k=id(r.name,r.tuple);if(expected.has(k)&&!firstSeen.has(k))firstSeen.set(k,phase)}
  const present=new Set(rows.map(r=>id(r.name,r.tuple))),missing=requiredRows.filter(r=>!present.has(id(r.name,r.tuple))),extras=rows.filter(r=>!expected.has(id(r.name,r.tuple)))
  trace.push({phase,emitted:rows.length,missing,extras,aliases,insts:c.insts,reads:c.reads,work:{...budget.state}})
 }
 snapshot('prepare',{reads:[],insts:[]})
 let finalCert:Pick<CountCert,'reads'|'insts'|'picks'>={reads:[],insts:[]},finalHyps=0
 for(let round=0;round<6;round++){
  const {goal,decls}=timed('encoding',()=>countedObligations(m,laws,{[own.name]:at},target)[1]!)
  const key=JSON.stringify(Object.entries(at).filter(([name])=>sources.has(name)))
  const pool=cached&&cachedKey===key?(poolHits++,cached):timed('poolConstruction',()=>{poolBuilds++;return grammarPool(goal,decls,1000,budget)})
  cached=pool;cachedKey=key
  finalCert=timed('selection',()=>polaritySelection(goal,decls,pool,budget,prep.sourceMaps).pick)
  const gg=timed('encoding',()=>mcGoal(goal.hyps,decls,finalCert));if(!gg)throw Error('audit selected certificate rejected');finalHyps=gg.hyps.length
  const next=timed('closure',()=>sparseReadInstances(m,laws,own,at,gg,finalCert,64-admitted,goal.hyps.at(-1),decls,prep.sourceMaps,goal.hyps.slice(0,-1),budget))
  at=next.at;admitted+=next.added.length;snapshot('closure:'+round,finalCert)
  if(!next.added.length||budget.state.exhausted)break
 }
 return {name:own.name,flags,phaseMs,poolBuilds,poolHits,finalHyps,required:requiredRows.map(r=>({...r,firstSeen:firstSeen.get(id(r.name,r.tuple))??null})),trace,finalInstances:at,finalCert,generationWork:budget.state}
}
if(import.meta.main){
 const fixture=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {machine:Machine,laws:Law[]}
 const source=JSON.parse(readFileSync(process.argv[3]!,'utf8')) as {familyIndices:number[],instances:Instances}
 const cert=JSON.parse(readFileSync(process.argv[4]!,'utf8')) as CountCert
 const laws=source.familyIndices.map(i=>fixture.laws[i]!),own=fixture.laws[Number(process.env.TARGET_INDEX??11)]!
 console.log(JSON.stringify(auditSupport(fixture.machine,laws,own,source.instances,cert,process.argv[5]==='none'?'none':'all')))
}
