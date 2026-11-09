// Fresh-process A/B/A/B/A/B. A retains the captured gap; B adds one candidate.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const out=process.argv[2];if(!out)throw new Error('output directory required')
const records:any[]=[]
for(let repeat=1;repeat<=(process.env.LAB_SECTION10_DEBUG?1:3);repeat++)for(const side of (process.env.LAB_SECTION10_DEBUG?['B']:['A','B'])){
 const id=side+repeat,stdout=join(out,id+'.capture.log'),stderr=join(out,id+'.stderr.log'),start=performance.now()
 console.log(JSON.stringify({event:'start',test:'T-10A',id}))
 const child=Bun.spawn(['/usr/bin/timeout','-s','KILL','120',process.execPath,'research/track-m/active-source-probe.ts','replay-input/input.json','Inv*','5','all'],{env:{...process.env,LAB_DEMAND_PROPOSALS:'1',LAB_SOURCE_MS:'5000',LAB_SOURCE_TRACE:'1',LAB_CONDITIONAL_PROOF:'1',LAB_SECTION7_CAPTURE:'v7-input/demand-and-sources.log',LAB_SECTION7_MEASUREMENT:'T2',LAB_SECTION7_CLEAN_WITNESSES:'1',LAB_SECTION9_SIDE:'B',LAB_SECTION9_COMPLEMENT_ONLY:'1',LAB_SECTION10_SIDE:side,LAB_SECTION9_REPEAT:String(repeat)},stdout:Bun.file(stdout),stderr:Bun.file(stderr)})
 const exit=await child.exited,rows=readFileSync(stdout,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)),r=rows.find(r=>r.test===(side==='A'?'T-9A':'T-10A'))
 if(exit!==0||!r)throw new Error('capture '+id+' failed: '+exit+'; see capture/stderr')
 r.side=side;r.repeat=repeat;r.captureProcessWallMs=performance.now()-start
 records.push(r);writeFileSync(join(out,id+'.json'),JSON.stringify(r)+'\n')
 console.log(JSON.stringify({event:'end',id,pass:r.pass,generatorGap:r.generatorGap,units:r.countedUnits,wallMs:r.wallMs,source:r.attempt&&{outcome:r.attempt.outcome,core:r.attempt.coreSize,queryUnits:r.attempt.queryCountedUnits},numeric:r.numeric&&{outcome:r.numeric.outcome,core:r.numericCore,queryUnits:r.numeric.queryCountedUnits},keepsGuard:r.keepsGuard}))
}
const summary=Object.fromEntries(['A','B'].map(side=>{const rs=records.filter(r=>r.side===side),walls=rs.map(r=>r.wallMs).sort((a,b)=>a-b);return [side,{countedUnits:rs.map(r=>r.countedUnits),wallMedianMs:walls[1],wallMaxMs:walls[2],captureProcessWallMs:rs.map(r=>r.captureProcessWallMs),expected:rs.every(r=>side==='A'?r.generatorGap:r.pass)}]}))
const pass=records.length===6&&Object.values(summary).every(s=>s.expected)
writeFileSync(join(out,'summary.json'),JSON.stringify({test:'T-10A',order:['A1','B1','A2','B2','A3','B3'],summary,pass,implementationAllowed:pass,productionChanged:false},null,2)+'\n')
console.log(JSON.stringify({event:'complete',summary,pass}))
