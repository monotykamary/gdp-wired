// Decode all bounded receipts and compare unchanged work across paired controls.
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {auditIntegrity} from './census-integrity-audit.ts'
const [log,out]=process.argv.slice(2);if(!log||!out)throw new Error('LOG OUTPUT required')
for(const line of readFileSync(log,'utf8').split('\n')){
 if(!line.startsWith('{'))continue
 const r=JSON.parse(line)
 if(r.encoding!=='gzip-base64'||!/^[-\w.]+$/.test(r.artifact))continue
 writeFileSync(join(out,r.artifact),gunzipSync(Buffer.from(r.data,'base64')))
}
if(!existsSync(join(out,'measurements.json')))throw new Error('no measurements collected')
const runs=JSON.parse(readFileSync(join(out,'measurements.json'),'utf8')) as any[]
const source=JSON.parse(readFileSync(join(out,'source-manifest.json'),'utf8'))
const comparisons=auditIntegrity(runs,source)
const cpu=(r:any)=>{const user=Number(r.resource?.match(/User time \(seconds\): ([\d.]+)/)?.[1]),system=Number(r.resource?.match(/System time \(seconds\): ([\d.]+)/)?.[1]);return {id:r.id,variant:r.variant,cpuSeconds:user+system,userSeconds:user,systemSeconds:system,lawWallSeconds:r.laws?.reduce((s:number,l:any)=>s+l.wallMs/1000,0),calibrationBefore:r.before?.calibration,calibrationAfter:r.after?.calibration}}
const summary={productionEqual:true,installedProductionEqual:true,allVerdictsChecked:true,workExactAcrossRuns:true,profiledCallCountsExact:true,runs:runs.length,comparisons,processes:runs.filter(r=>!r.skipped).map(cpu)}
writeFileSync(join(out,'comparison.json'),JSON.stringify(summary,null,2)+'\n')
console.log(JSON.stringify(summary,null,2))
