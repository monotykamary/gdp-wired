// Independent data checks and kernel replay of the assumed numeric cores.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {type Goal,check} from '../../kernel/kernel.ts'
import {rowsAt} from '../../kernel/prove.ts'
import {refuteFast} from '../../core/solver.ts'
const [dir]=process.argv.slice(2);if(!dir)throw new Error('DIR required')
const result=JSON.parse(readFileSync(join(dir,'results.json'),'utf8'))
const rows=readFileSync(join(dir,'t2-t3.log'),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
const numeric=rows.filter(r=>r.measurement==='T3').map(r=>{
 const goal:Goal={name:r.law,hyps:r.core.map((i:number)=>r.numeric.hyps[i])},path=new Map(),proof=refuteFast(rowsAt(goal,path),256)
 const checked=proof?.kind==='refuted'&&check(goal,{leaf:proof.steps},path)
 if(!checked)throw new Error('numeric core did not independently check')
 return {law:r.law,checked,hyps:goal.hyps.length,poolCore:r.poolCore,assumptionsOnly:true}
})
for(const law of result.laws)if(!law.verdictMatches)throw new Error('control verdict changed')
const star=result.leafAudits.find((r:any)=>r.law.startsWith('Inv*'))
const full=JSON.parse(readFileSync(join(dir,'Invstar-leaves.json'),'utf8'))
for(const row of full.rows)if(Object.values(row.provenance).reduce((n:number,v)=>n+Number(v),0)!==row.hyps)throw new Error('hypothesis provenance sum')
const frequencies=new Map<string,number>();for(const row of full.rows)frequencies.set(row.exactHash,(frequencies.get(row.exactHash)??0)+1)
if(frequencies.size!==star.sameExactCheckedLeaf.distinct||full.rows.length!==star.calls)throw new Error('repetition tally mismatch')
const selected=result.t2.find((r:any)=>r.witnessCleanup&&r.targetScope&&r.law.startsWith('Inv*'))
if(!selected?.conditionalChecked||!selected.complete.fixedPoint)throw new Error('missing checked target leaf')
console.log(JSON.stringify({verified:true,numeric,controlVerdicts:result.laws.length,exactCountedMatches:result.laws.filter((r:any)=>r.countedDelta===0).length,countedDeltas:result.laws.map((r:any)=>({law:r.law,delta:r.countedDelta})),leafCalls:star.calls,distinctCheckedLeaves:frequencies.size,checkedTargetCuts:selected.cutCount}))
