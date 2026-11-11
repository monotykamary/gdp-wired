import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),root=mkdtempSync('/tmp/merge-0480-'),mode=process.argv[2]
function run(cmd:string,args:string[]){const r=spawnSync(cmd,args,{cwd:root,encoding:'utf8',timeout:800000,maxBuffer:32*1024*1024});process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');if(r.error||r.status!==0)throw Error(`${cmd}: ${r.status} ${r.error??''}`)}
function identities(){let preserved=0,safety=0;for(const [file,kind]of[['frozen-tree.txt','protected'],['release-safety-tree.txt','safety']])for(const line of readFileSync(join(input,file!),'utf8').trim().split('\n')){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line)!;if(kind==='protected'&&['kernel/prove.ts','kernel/prover-rows.ts'].includes(m[2]!))continue;const bytes=readFileSync(join(root,m[2]!));a.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),m[1],m[2]!);if(kind==='protected')preserved++;else safety++}console.log('MERGE_IDENTITIES '+JSON.stringify({preserved,safety,untrustedExceptions:['kernel/prove.ts','kernel/prover-rows.ts']}))}
try{
 for(const file of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,file+'.tar'),'-C',root])
 identities();run('bun',['install','--frozen-lockfile'])
 if(mode==='check'){run('bun',['run','check']);run('bun',['scripts/test-shards.ts','--list'])}
 else if(mode==='native')run('bun',['test','core/source-check.test.ts','core/source-diagnostic.test.ts','core/cli.test.ts','core/extract-ci-method-scope.test.ts','core/security.test.ts'])
 else if(mode==='extract')run('bun',['test','core/extract.test.ts','core/extract-standalone.test.ts','core/extract-py.test.ts','core/extract-py-mro.test.ts','core/extract-py-hasattr.test.ts','core/extract-orm.test.ts','core/extract-sol.test.ts','core/sol-concrete.test.ts'])
 else if(mode==='inference')run('bun',['test','core/infer.test.ts','core/relational.test.ts','core/effect.test.ts','core/effect-queue.test.ts','core/effect-stm.test.ts','core/effect-schedule.test.ts','core/calendar.test.ts'])
 else if(mode==='counted'){run('bun',['test','core/count-tier-budget.test.ts','core/count-attempt-expiration.test.ts','core/prover-row-budget.test.ts','kernel/prover-rows.test.ts','core/i6-meter.test.ts','core/work-admission-perf.test.ts','core/work-observe.test.ts','core/hard-cap.test.ts','core/common-counted.test.ts','core/check.test.ts','kernel/count.test.ts','kernel/countmachine.test.ts','kernel/cdcl-root.test.ts','kernel/frame-cut.test.ts','lean-kernel/frame-export.test.ts','lean-kernel/linear-export.test.ts']);run('env',['GDP_WORK_FULL=1','bun','test','core/count-attempt-expiration.test.ts'])}
 else throw Error('bad verification mode')
 identities();console.log('MERGE_GATE '+JSON.stringify({source:readFileSync(join(input,'source.txt'),'utf8').trim(),mode}))
}finally{rmSync(root,{recursive:true,force:true})}
