// Sequential laws over the same machine, using the production tree-cache scope.
// This is a diagnostic, not the generated-law/all-proofs 60-second success gate.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {certFor} from '../../core/counts.ts'
import {proveFocusedCounts} from '../../core/count-focus-proof.ts'
import {checkMC,countedObligations} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,treeReuseStats,withTrees,withWall} from '../../kernel/prove.ts'
import {rowReuseStats} from '../../kernel/prover-rows.ts'
import {costMeter,costSpan} from './cost-meter.ts'
const start=performance.now(),{m,laws}=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {m:Machine,laws:Law[]}
const rowsOn=process.env.GDP_ROWS_SHARED!=='0',treesOn=process.env.GDP_COUNTS_SHARED_TREES!=='0'
const all=()=>{
 for(const [index,law]of laws.entries()){
  if(!['one primary','Inv3915','Inv1758','Inv2973','Inv*'].some(prefix=>law.name.startsWith(prefix)))continue
  costMeter.phases.clear();costMeter.sites.clear()
  const t=performance.now(),work=fullWork(),hits=treeReuseStats.hits,rowBefore={...rowReuseStats}
  const result=withWall(t+60000,()=>counted(fullRate,()=>costSpan('construction','family-control',()=>{
   const proof=proveFocusedCounts(m,laws,law,{},clock()+5000,(goal,decls)=>certFor(goal,decls,true,1000))
   return {proven:!!proof,checked:!!proof&&countedObligations(m,laws,{[law.name]:proof.instances},index).every(p=>!!proof.certs[p.goal.name]&&checkMC(p.goal.hyps,p.decls,proof.certs[p.goal.name]!))}
  }),true))
  const wallMs=performance.now()-t,snap=costMeter.snapshot()
  console.log(JSON.stringify({mode:'family',law:law.name,rowsOn,treesOn,...result,wallMs,countedMs:(fullWork()-work)/fullRate,treeHits:treeReuseStats.hits-hits,rowReuse:Object.fromEntries(Object.entries(rowReuseStats).map(([k,v])=>[k,v-rowBefore[k as keyof typeof rowBefore]])),phases:snap.phases,sites:snap.sites}))
 }
}
if(treesOn)withTrees(all);else all()
console.log(JSON.stringify({mode:'family-total',rowsOn,treesOn,wallMs:performance.now()-start,treeReuse:treeReuseStats,rowReuse:rowReuseStats}))
