// All comparisons run as fresh Bun processes on one pinned VM, no co-tenants.
import {spawnSync} from 'node:child_process'
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
const input=process.argv[2]??'replay-input/input.json',out=process.argv[3]??'/tmp/track-m-wall-evidence'
mkdirSync(out,{recursive:true})
const env={...process.env};delete env.GDP_COUNTS_GIVEN
const prefixes=['one primary','Inv3915','Inv1758','Inv2973','Inv*'],focusedOnly=process.argv.includes('--focused-only')
if(process.platform!=='linux')throw new Error('timing suite requires a disposable Linux VM')
const allowed=readFileSync('/proc/self/status','utf8').match(/^Cpus_allowed_list:\s*(.+)$/m)?.[1]?.trim()
if(!allowed)throw new Error('CPU affinity is unavailable')
const cpus=allowed.split(',').flatMap(s=>{const [lo,hi=lo]=s.split('-').map(Number) as [number,number?];return Array.from({length:hi!-lo+1},(_,i)=>lo+i)}).slice(0,4)
if(cpus.length!==4)throw new Error(`need four allowed CPUs, got ${allowed}`)
const affinity=cpus.join(',')
console.log(JSON.stringify({affinity:{allowed,selected:affinity,cpus:4},baselineRevision:process.env.TRACK_M_BASE_REVISION??'af7cb91f'}))
const run=(mode:string,prefix:string,profiled:boolean)=>{
 const start=performance.now(),child=spawnSync('taskset',['-c',affinity,'bun','research/track-m/profile-production.ts',mode,input,prefix],{env:{...env,TRACK_M_COST_PROFILE:profiled?'1':'0',TRACK_M_ROWS_PROFILE:profiled?'1':'0'},encoding:'utf8',timeout:180000,maxBuffer:8*1024*1024})
 const processWallMs=performance.now()-start,tag=`${mode}-${prefix.replaceAll(/[^a-z0-9]/gi,'_')}-${profiled?'profiled':'baseline'}`
 writeFileSync(`${out}/${tag}.stdout`,child.stdout??'');writeFileSync(`${out}/${tag}.stderr`,child.stderr??'')
 const lines=(child.stdout??'').trim().split('\n'),record=lines.reverse().map(s=>{try{return JSON.parse(s)}catch{return undefined}}).find(r=>r?.mode===mode)
 if(child.status!==0||!record){console.log(JSON.stringify({mode,prefix,profiled,status:child.status,signal:child.signal,error:child.error?.message,processWallMs,stderr:child.stderr?.slice(-2000)}));return}
 const total=Object.values(record.phases as Record<string,number>).reduce((a,b)=>a+b,0),result={...record,processWallMs,idleGcResidualMs:processWallMs-total,sumMs:total+(processWallMs-total)}
 writeFileSync(`${out}/${tag}.json`,JSON.stringify(result,null,2));console.log(JSON.stringify(result))
}
for(const prefix of prefixes)run('focused',prefix,false)
if(!focusedOnly){run('generation','mldr',false);run('production','mldr',false)}
const install=spawnSync('bun',['research/track-m/install-cost-meter.ts',`${out}/originals`],{env:{...env,TRACK_M_DISPOSABLE_PROFILE:'1'},encoding:'utf8',timeout:30000,maxBuffer:1024*1024})
writeFileSync(`${out}/install.stdout`,install.stdout??'');writeFileSync(`${out}/install.stderr`,install.stderr??'')
if(install.status!==0)throw new Error(`instrumentation install failed: ${install.stderr}`)
console.log(JSON.stringify({installation:JSON.parse(install.stdout),baselineRevision:process.env.TRACK_M_BASE_REVISION??'af7cb91f'}))
const tests=spawnSync('bun',['test','research/track-m/cost-meter.test.ts','core/count-recovery/rename-proof.test.ts','core/count-cases.test.ts','kernel/countmachine.test.ts'],{env:{...env,TRACK_M_COST_PROFILE:'1'},encoding:'utf8',timeout:120000,maxBuffer:1024*1024})
writeFileSync(`${out}/instrumented-tests.log`,(tests.stdout??'')+(tests.stderr??''));console.log(JSON.stringify({instrumentedTests:{status:tests.status,tail:tests.stderr?.slice(-1500)}}))
if(tests.status!==0)throw new Error('instrumented kernel/prover regression failed')
for(const prefix of prefixes)run('focused',prefix,true)
if(!focusedOnly){run('generation','mldr',true);run('production','mldr',true)}
console.log(JSON.stringify({manifest:JSON.parse(readFileSync(`${out}/originals/manifest.json`,'utf8'))}))
