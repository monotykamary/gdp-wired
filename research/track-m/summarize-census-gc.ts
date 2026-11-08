// Post-process preserved GC telemetry; never infer a missing raw receipt.
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
const dir=process.argv[2];if(!dir)throw new Error('measurement directory required')
const runs=JSON.parse(readFileSync(join(dir,'measurements.json'),'utf8')) as any[]
const means=(rows:any[])=>rows[0].laws.map((_:unknown,i:number)=>rows.reduce((s,r)=>s+r.laws[i].kernelMs,0)/rows.length)
const groups=[...new Set(runs.map(r=>r.variant))].map(variant=>{
 const rows=runs.filter(r=>r.variant===variant),normal=rows.filter(r=>r.runtimeControls.BUN_JSC_useConcurrentGC!=='false'),sync=rows.filter(r=>r.runtimeControls.BUN_JSC_useConcurrentGC==='false')
 const defaultKernelMs=means(normal),syncKernelMs=means(sync)
 return {variant,defaultIds:normal.map(r=>r.id),syncIds:sync.map(r=>r.id),defaultKernelMs,syncKernelMs,syncToDefault:syncKernelMs.map((ms:number,i:number)=>ms/defaultKernelMs[i])}
})
const logs=runs.map(r=>{
 const file=join(dir,r.id+'.stderr.log')
 if(!existsSync(file))return {id:r.id,rawLogRetained:false}
 const text=readFileSync(file,'utf8'),events=[...text.matchAll(/p=([\d.]+)ms \(max [^)]+\), cycle ([\d.]+)ms END\]/g)]
 return {id:r.id,rawLogRetained:true,completeCollections:events.length,reportedPauseMs:events.reduce((s,m)=>s+Number(m[1]),0),reportedCycleMs:events.reduce((s,m)=>s+Number(m[2]),0),maxReportedPauseMs:Math.max(0,...events.map(m=>Number(m[1])))}
})
const result={groups,logs,note:'Structured measurements retained for all trials. Missing raw stderr is disclosed; GC p/cycle fields are reported engine timers, not an exclusive kernel-phase decomposition.'}
writeFileSync(join(dir,'gc-analysis.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result,null,2))
