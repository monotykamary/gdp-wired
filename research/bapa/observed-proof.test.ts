import {test,expect} from 'bun:test'
import {mkdtempSync,readFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {observeProof} from './observed-proof.ts'
test('observed worker returns a checked unseeded minimal proof and durable progress',async()=>{
 const out=mkdtempSync(join(tmpdir(),'bapa-observe-'))
 try{const r=await observeProof({out,model:'minimal',units:1_000_000,wallMs:30_000,backupMs:40_000,progressMs:20})
 expect(r).toMatchObject({terminal:'proven',proven:true,checked:true,supervisorBackupStop:false})
 expect(readFileSync(join(out,'progress.jsonl'),'utf8')).toContain('kernelCallsCoverage')
 const detail=JSON.parse(readFileSync(join(out,'worker-report.json'),'utf8'))
 expect(detail.observerFailures).toBe(0)
 const entries=new Set(['kernel choiceFree','kernel linear','kernel termId','kernel truth','kernel facts'])
 const calls=detail.siteCounts.filter((s:{site:string})=>entries.has(s.site)).reduce((n:number,s:{events:number})=>n+s.events,0)
 expect((r.lastProgress as {kernelCalls:string}).kernelCalls).toBe(String(calls))
 }finally{rmSync(out,{recursive:true,force:true})}
},45_000)
test('own work budget leaves a report rather than waiting for the job timeout',async()=>{
 const out=mkdtempSync(join(tmpdir(),'bapa-budget-'))
 try{const r=await observeProof({out,model:'minimal',units:1,wallMs:20_000,backupMs:30_000})
 expect(r).toMatchObject({terminal:'work-budget',proven:false,checked:false,supervisorBackupStop:false})
 expect(JSON.parse(readFileSync(join(out,'proof-report.json'),'utf8')).terminal).toBe('work-budget')
 }finally{rmSync(out,{recursive:true,force:true})}
},35_000)
test('own wall budget leaves an explicit non-refutation report',async()=>{
 const out=mkdtempSync(join(tmpdir(),'bapa-wall-'))
 try{const r=await observeProof({out,model:'minimal',units:1_000_000,wallMs:1,backupMs:20_000})
 expect(r).toMatchObject({terminal:'wall-budget',proven:false,checked:false,supervisorBackupStop:false})
 }finally{rmSync(out,{recursive:true,force:true})}
},25_000)
