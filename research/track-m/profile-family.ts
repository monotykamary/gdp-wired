// Sequential laws over the same machine, using the production tree-cache scope.
// This is a diagnostic, not the generated-law/all-proofs 60-second success gate.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {certFor} from '../../core/counts.ts'
import {proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,treeReuseStats,withTrees,withWall} from '../../kernel/prove.ts'
import {rowReuseStats} from '../../kernel/prover-rows.ts'
import {sourceMemoStats} from '../../core/count-recovery/source-memo.ts'
import {costMeter,costSpan} from './cost-meter.ts'
const start=performance.now(),{m,laws}=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {m:Machine,laws:Law[]}
const rowsOn=process.env.GDP_ROWS_SHARED!=='0',treesOn=process.env.GDP_COUNTS_SHARED_TREES!=='0',contextsOn=process.env.GDP_SOURCE_CONTEXTS!=='0',indexOn=process.env.GDP_SOURCE_INDEX!=='0'
const all=()=>{
 for(const [index,law]of laws.entries()){
  if(!['one primary','Inv3915','Inv1758','Inv2973','Inv*'].some(prefix=>law.name.startsWith(prefix)))continue
  costMeter.phases.clear();costMeter.sites.clear()
  const trace:Record<string,unknown>[]=[],t=performance.now(),work=fullWork(),hits=treeReuseStats.hits,rowBefore={...rowReuseStats},sourceBefore={...sourceMemoStats}
  const result=withWall(t+60000,()=>counted(fullRate,()=>costSpan('construction','family-control',()=>{
   const proof=proveFocusedCounts(m,laws,law,{},clock()+5000,(goal,decls)=>certFor(goal,decls,true,1000),process.env.TRACK_M_FAMILY_TRACE==='1'?event=>trace.push(event):undefined)
   return {proven:!!proof,checked:!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},index).every(p=>!!proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,proof.certs[p.goal.name]!))}
  }),true))
  const wallMs=performance.now()-t,snap=costMeter.snapshot(),memory=process.memoryUsage()
  console.log(JSON.stringify({mode:'family',memory:{rss:memory.rss,heapUsed:memory.heapUsed},law:law.name,rowsOn,treesOn,contextsOn,indexOn,...result,wallMs,countedMs:(fullWork()-work)/fullRate,treeHits:treeReuseStats.hits-hits,sourceReuse:Object.fromEntries(Object.entries(sourceMemoStats).map(([k,v])=>[k,v-sourceBefore[k as keyof typeof sourceBefore]])),rowReuse:Object.fromEntries(Object.entries(rowReuseStats).map(([k,v])=>[k,v-rowBefore[k as keyof typeof rowBefore]])),phases:snap.phases,sites:snap.sites,...(trace.length?{tail:trace.slice(-16)}:{})}))
 }
}
if(treesOn)withTrees(all);else all()
console.log(JSON.stringify({mode:'family-total',rowsOn,treesOn,contextsOn,indexOn,wallMs:performance.now()-start,treeReuse:treeReuseStats,rowReuse:rowReuseStats}))
