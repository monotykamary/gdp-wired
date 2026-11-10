import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [file,dir]=process.argv.slice(2);if(!file||!dir)throw new Error('LOG OUTPUT_DIR required')
const results:any[]=[]
for(const line of readFileSync(file,'utf8').split('\n')){
 if(!line.startsWith('{'))continue
 const r=JSON.parse(line)
 if(r.encoding!=='gzip-base64'||!['loop-star.log','loop-overlap.log'].includes(r.artifact))continue
 const text=gunzipSync(Buffer.from(r.data,'base64')).toString('utf8');writeFileSync(join(dir,r.artifact),text)
 for(const line of text.split('\n'))if(line.startsWith('{')){const d=JSON.parse(line);if(!d.diagnostic)continue;const steps=d.closureSteps??[],sources=steps.filter((s:any)=>s.stage==='closure-source'),finals=steps.filter((s:any)=>s.stage==='closure-final'),rounds=steps.filter((s:any)=>s.stage==='closure-model-round');let closure=0;const seen=new Set<string>(),duplicates:string[]=[];for(const e of steps){if(e.stage==='closure-complete')closure++;if(e.stage==='closure-source'){const key=`${closure}/${e.scope}/${e.index}`;if(seen.has(key))duplicates.push(key);seen.add(key)}}results.push({law:d.law,wallMs:d.wallMs,countedUnits:d.countedUnits,conditionalChecked:d.conditionalChecked,hyps:d.hyps,instances:d.instances,complete:steps.filter((s:any)=>s.stage==='closure-complete'),finals,rounds,sources,duplicates})}
}
writeFileSync(join(dir,'results.json'),JSON.stringify(results,null,2)+'\n')
console.log(JSON.stringify(results.map(r=>({...r,rounds:r.rounds.length,sources:r.sources.length,finals:r.finals.map((f:any)=>({...f,model:undefined,path:undefined}))})),null,2))
