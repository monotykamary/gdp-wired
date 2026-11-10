// A/B interleaved repeats of the exact captured packet, one fresh process each.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const out=process.argv[2];if(!out)throw new Error('output directory required')
const records:any[]=[]
for(let repeat=1;repeat<=3;repeat++)for(const side of ['A','B']){
 const id=side+repeat,stdout=join(out,id+'.capture.log'),stderr=join(out,id+'.stderr.log')
 console.log(JSON.stringify({event:'start',test:'T-9A',id}))
 const start=performance.now(),child=Bun.spawn(['/usr/bin/timeout','-s','KILL','120',process.execPath,'research/track-m/active-source-probe.ts','replay-input/input.json','Inv*','5','all'],{env:{...process.env,LAB_DEMAND_PROPOSALS:'1',LAB_SOURCE_MS:'5000',LAB_SOURCE_TRACE:'1',LAB_CONDITIONAL_PROOF:'1',LAB_SECTION7_CAPTURE:'v7-input/demand-and-sources.log',LAB_SECTION7_MEASUREMENT:'T2',LAB_SECTION7_CLEAN_WITNESSES:'1',LAB_SECTION9_SIDE:side,LAB_SECTION9_REPEAT:String(repeat)},stdout:Bun.file(stdout),stderr:Bun.file(stderr)})
 const exit=await child.exited
 const rows=readFileSync(stdout,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)),r=rows.find(r=>r.test==='T-9A')
 if(exit!==0||!r)throw new Error('failed capture '+id+' exit '+exit+'; see retained capture/stderr')
 r.captureProcessWallMs=performance.now()-start
 records.push(r);writeFileSync(join(out,id+'.json'),JSON.stringify(r)+'\n')
 console.log(JSON.stringify({event:'end',id,generated:r.generated,pass:r.pass,generatorGap:r.generatorGap,units:r.countedUnits,wallMs:r.wallMs,branches:r.branches.map((b:any)=>({name:b.name,outcome:b.outcome,reason:b.reason,units:b.countedUnits,attempts:b.attempts.map((a:any)=>({index:a.originalIndex,outcome:a.outcome,core:a.coreSize,units:a.countedUnits}))}))}))
}
if(new Set(records.map(r=>r.packetHash)).size!==1)throw new Error('captured packets differ; A/B walls not comparable')
const median=(xs:number[])=>xs.slice().sort((a,b)=>a-b)[1]!,summary=Object.fromEntries(['A','B'].map(side=>{const rs=records.filter(r=>r.side===side),walls=rs.map(r=>r.wallMs);return [side,{repeats:rs.length,countedUnits:rs.map(r=>r.countedUnits),wallMedianMs:median(walls),wallMaxMs:Math.max(...walls),pass:rs.every(r=>r.pass),generatorGap:rs.every(r=>r.generatorGap),branches:rs.map(r=>r.branches.map((b:any)=>({name:b.name,outcome:b.outcome,reason:b.reason,units:b.countedUnits})))}]}))
const b=records.filter(r=>r.side==='B'),decision=b.every(r=>r.pass)?'pass':b.every(r=>r.generatorGap)?'generator-gap':'failed-or-inconsistent'
writeFileSync(join(out,'summary.json'),JSON.stringify({test:'T-9A',order:['A1','B1','A2','B2','A3','B3'],packetHash:records[0].packetHash,summary,decision,implementationAllowed:decision==='pass',laterTestsRun:false},null,2)+'\n')
console.log(JSON.stringify({event:'complete',test:'T-9A',summary,decision}))
