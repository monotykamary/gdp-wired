// Unchanged timeout cases on the baseline and merged candidate.
import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
const cases={search:{file:'core/search.test.ts',args:['test','./core/search.test.ts'],ms:5000},fold:{file:'core/extract-py.test.ts',args:['test','./core/extract-py.test.ts','--test-name-pattern','^a loop over a list the request carries: a fold, exact for every length$'],ms:60000}}
const kind=process.argv[2]
if(kind!=='search'&&kind!=='fold')throw Error('search or fold required')
const selected=cases[kind]
const expected:Record<string,string>=JSON.parse(readFileSync('frozen-paxos/checksums.json','utf8'))
const digest=(s:string)=>createHash('sha256').update(s).digest('hex')
for(const [path,hash]of Object.entries(expected))if(createHash('sha256').update(readFileSync(path)).digest('hex')!==hash)throw Error('input hash mismatch: '+path)
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const input=resolve('paxos-input'),config=JSON.parse(readFileSync(join(input,'gate.json'),'utf8')),dir=mkdtempSync('/tmp/lane-i-search-pair-')
const cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
let failed=false
try{
 const dirs={base:join(dir,'base'),candidate:join(dir,'candidate')},meta={base:restore(input,dirs.base,config.baseline),candidate:restore(input,dirs.candidate,config.candidate)}
 const hashes={base:harnessHashes(dirs.base),candidate:harnessHashes(dirs.candidate)}
 for(const side of ['base','candidate']as const)command('bun',['install','--frozen-lockfile'],dirs[side])
 for(let repeat=1;repeat<=3;repeat++){
  const order=repeat%2?['base','candidate']as const:['candidate','base']as const,outcomes:Record<string,unknown>={}
  for(const side of order){
   const testSha256=createHash('sha256').update(readFileSync(join(dirs[side],selected.file))).digest('hex')
   const start=performance.now(),run=spawnSync('bun',selected.args,{cwd:dirs[side],encoding:'utf8',timeout:90000,maxBuffer:8*1024*1024,env:{...process.env,CI:'1'}}),stdout=run.stdout??'',stderr=run.stderr??''
   outcomes[side]={exit:run.status,signal:run.signal,error:run.error?.message,wallMs:performance.now()-start,testSha256,stdoutSha256:digest(stdout),stderrSha256:digest(stderr),traceGzipBase64:gzipSync(stdout+'\n---stderr---\n'+stderr).toString('base64')}
   if(run.status!==0)failed=true
  }
  console.log('TIMEOUT_PAIR '+JSON.stringify({repeat,case:kind,cpu,config,meta,hashes,command:['bun',...selected.args],testTimeoutMs:selected.ms,order,outcomes}))
 }
}finally{rmSync(dir,{recursive:true,force:true})}
if(failed)process.exitCode=1
