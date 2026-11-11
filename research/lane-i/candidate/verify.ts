import {createHash} from 'node:crypto'
import {mkdtempSync, readFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('candidate-input'), mode=process.argv[2]!, root=mkdtempSync(join(tmpdir(),'mldr-candidate-'))
const env={...process.env,GDP_WORK_FULL:mode==='tripwire'?'1':'0',GDP_WORK_STEPS:'0'}
function run(command:string,args:string[]){const result=spawnSync(command,args,{cwd:root,env,encoding:'utf8',maxBuffer:64*1024*1024,timeout:1_100_000});process.stdout.write(result.stdout??'');process.stderr.write(result.stderr??'');if(result.error)throw result.error;if(result.status!==0)throw Error(`${command} failed: ${result.status}`)}
function trusted(){let files=0;for(const line of readFileSync(join(input,'trusted-tree.txt'),'utf8').trim().split('\n')){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line);if(!m)throw Error('bad tree identity');if(m[2]==='kernel/prove.ts')continue;const bytes=readFileSync(join(root,m[2]!));const hash=createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');if(hash!==m[1])throw Error(`trusted overlay mismatch ${m[2]}`);files++}console.log(JSON.stringify({kind:'PENDING_D_TRUSTED_IDENTITY',files,exceptions:['kernel/prove.ts','kernel/meter.ts','kernel/work-budget.test.ts']}))}
try{
 for(const file of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,`${file}.tar`),'-C',root])
 trusted();run('bun',['install','--frozen-lockfile'])
 if(mode==='check')run('bun',['run','check'])
 else if(mode==='tripwire')run('bun',['test','--preload','./core/clock-tripwire-preload.ts','core/clock-tripwire.test.ts'])
 else{const tests=['core/count-generation-budget.test.ts','core/count-tier-budget.test.ts','core/count-tier-integration.test.ts','core/count-strategies.test.ts','core/count-strategy-clock.test.ts','core/count-lifted-shape.test.ts','core/count-lifted-transports.test.ts','core/count-frames.test.ts','core/count-frames.lane-f.test.ts','core/count-case-compose.test.ts','core/count-guard-shape.test.ts','core/count-guard-shape.lane-f.test.ts','kernel/frame-cut.test.ts','kernel/cdcl-root.test.ts','lean-kernel/frame-export.test.ts','lean-kernel/linear-export.test.ts'];for(const p of tests)readFileSync(join(root,p));run('bun',['test',...tests])}
 trusted();console.log(JSON.stringify({kind:'CANDIDATE_VALIDATION_PASS',status:'PENDING-D',mode,source:readFileSync(join(input,'source.txt'),'utf8').trim()}))
}finally{rmSync(root,{recursive:true,force:true})}
