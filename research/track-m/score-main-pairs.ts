import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'

type Phase='search'|'broken'
type Side='base'|'cand'
export type Outcome={verdict:string,exit:number,ms?:number}
export type Pair={base:Record<Phase,Outcome>,cand:Record<Phase,Outcome>}
export function parsePairLog(text:string,id:string):Pair{
 const out={base:{},cand:{}} as Pair
 let active:{side:Side,phase:Phase,row?:any}|undefined
 for(const line of text.split('\n')){
  if(line.startsWith('PAIR begin ')){
   const m=/^PAIR begin side=(base|cand) phase=(search|broken) id=(\S+) baseline=(\S+)$/.exec(line)
   if(active||!m||m[3]!==id||!m[4]!.startsWith('6a3874d3'))throw Error(`invalid pair header: ${line}`)
   active={side:m[1] as Side,phase:m[2] as Phase}
  }else if(line.startsWith('{')&&active){
   const row=JSON.parse(line)
   if(row.id===id){if(active.row)throw Error('duplicate protocol result');active.row=row}
  }else if(line.startsWith('PAIR end ')){
   const m=/^PAIR end side=(base|cand) phase=(search|broken) exit=(\d+)$/.exec(line)
   if(!active||!m||m[1]!==active.side||m[2]!==active.phase||out[active.side][active.phase])throw Error(`invalid pair end: ${line}`)
   const exit=Number(m[3]),result=active.row?.[active.phase]
   const verdict=[124,137].includes(exit)?'timeout':exit||active.row?.error?'error':!result?'missing':!Number.isFinite(result.ms)?'missing':result.ms>60000?'overrun':result.verdict
   if(!['proven','refuted','unknown','timeout','error','missing','overrun'].includes(verdict))throw Error(`invalid verdict ${verdict}`)
   out[active.side][active.phase]={verdict,exit,...(result?.ms===undefined?{}:{ms:result.ms})};active=undefined
  }
 }
 if(active||['base','cand'].some(s=>['search','broken'].some(p=>!out[s as Side][p as Phase])))throw Error('incomplete pair')
 return out
}
export function compareOutcome(phase:Phase,base:Outcome,cand:Outcome):'match'|'improvement'|'regression'|'invalid'{
 if([base,cand].some(o=>['error','missing','overrun'].includes(o.verdict)))return 'invalid'
 if(phase==='broken'&&cand.verdict==='proven'||phase==='search'&&cand.verdict==='refuted')return 'regression'
 if(base.verdict===cand.verdict)return 'match'
 if(phase==='search'&&base.verdict==='proven'||phase==='broken'&&base.verdict==='refuted'||cand.verdict==='timeout')return 'regression'
 return 'improvement'
}
if(import.meta.main){
 const [dir,jobsFile='research/track-m/jobs-paired-main-3x.json',output]=process.argv.slice(2)
 if(!dir)throw Error('usage: score-main-pairs.ts DIR [JOBS] [OUTPUT]')
 const jobs=JSON.parse(readFileSync(jobsFile,'utf8')) as {name:string,cmd:string}[],placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8'))
 const coverage=new Map<string,number>()
 for(const job of jobs){const id=job.cmd.split(' ').at(-2)!;coverage.set(id,(coverage.get(id)??0)+1)}
 if(jobs.length!==87||coverage.size!==29||[...coverage.values()].some(n=>n!==3))throw Error('expected exactly 29 protocols with three pairs each')
 const counts:{[P in Phase]:Record<Side,Record<string,number>>}={search:{base:{},cand:{}},broken:{base:{},cand:{}}}
 const comparisons:{name:string,id:string,phase:Phase,result:string,base:Outcome,cand:Outcome}[]=[],pairs:Record<string,Pair>={}
 for(const job of jobs){
  const p=placement[job.name]
  if(!p||p.type!=='large'||p.vcpus!==8||p.vm_vcpus!==8||p.exclusive!==true||p.co_tenants!==0)throw Error(`invalid placement: ${job.name}`)
  const id=job.cmd.split(' ').at(-2)!,pair=parsePairLog(readFileSync(join(dir,job.name+'.log'),'utf8'),id);pairs[job.name]=pair
  for(const phase of ['search','broken'] as const){
   for(const side of ['base','cand'] as const){const key=pair[side][phase].verdict;counts[phase][side][key]=(counts[phase][side][key]??0)+1}
   comparisons.push({name:job.name,id,phase,result:compareOutcome(phase,pair.base[phase],pair.cand[phase]),base:pair.base[phase],cand:pair.cand[phase]})
  }
 }
 const regressions=comparisons.filter(x=>x.result==='regression'),invalid=comparisons.filter(x=>x.result==='invalid'),improvements=comparisons.filter(x=>x.result==='improvement')
 const summary={baseline:'6a3874d3',jobs:jobs.length,phaseComparisons:comparisons.length,matches:comparisons.filter(x=>x.result==='match').length,counts,regressions,invalid,improvements,verdictsIdentical:comparisons.every(x=>x.result==='match'),noRegression:!regressions.length&&!invalid.length,pairs}
 const text=JSON.stringify(summary,null,2)+'\n';if(output)writeFileSync(output,text)
 console.log(JSON.stringify({...summary,pairs:undefined},null,2))
 if(!summary.noRegression)process.exitCode=1
}
