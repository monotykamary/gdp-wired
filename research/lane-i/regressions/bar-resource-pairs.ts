// Original bar task budgets, on the same CPU in alternating main/b09 order.
import {mkdtempSync,readFileSync,writeFileSync,mkdirSync,rmSync,existsSync} from 'node:fs'
import {join,resolve,dirname} from 'node:path'
import {tmpdir} from 'node:os'
import {runResourceMeasured} from './resource-run.ts'
import {gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const roster: {view:string,task:string}[]=JSON.parse(readFileSync(resolve('regression-driver/bar-roster.json'),'utf8'))
const index=Number(process.argv[2]),row=roster[index]
if(!row)throw new Error('invalid roster index')
const input=resolve('gate-inputs'),config=JSON.parse(readFileSync(join(input,'gate.json'),'utf8'))
const temp=mkdtempSync(join(tmpdir(),'lane-i-bar-')),digest=(s:string)=>createHash('sha256').update(s).digest('hex')
const inputs:Record<string,string>={}
async function download(url:string,path:string){const response=await fetch(url,{signal:AbortSignal.timeout(60000)});if(!response.ok)throw new Error('input fetch '+response.status+' '+url);const text=await response.text();mkdirSync(dirname(path),{recursive:true});writeFileSync(path,text);inputs[url]=digest(text);return text}
try{
  let file=join(temp,'input',row.task),expected:string|undefined
  if(row.view==='chc'){
    const root='https://raw.githubusercontent.com/chc-comp/chc-comp26-benchmarks/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc/'
    const yaml=await download(root+row.task,file),relative=/^input_files:\s*(\S+)/m.exec(yaml)?.[1]
    if(!relative)throw new Error('missing CHC input_files')
    expected=/expected_verdict:\s*(\S+)/.exec(yaml)?.[1]==='true'?'sat':'unsat'
    const key=join(dirname(row.task),relative);file=join(temp,'input',key);await download(root+key,file)
  }else if(row.view.startsWith('its'))await download('https://raw.githubusercontent.com/TermCOMP/TPDB-ARI/183f29db5ec7702215c6aabe12732bf3e836fced/'+row.task,file)
  else await download('https://raw.githubusercontent.com/tip-org/benchmarks/bace5b2f0e45d526ec82ce5de6b25fe024984161/benchmarks/'+row.task,file)
  let bun='bun'
  if(row.view==='tip'){
    if(existsSync('/opt/bun-1.4.4/bin/bun'))bun='/opt/bun-1.4.4/bin/bun'
    else if(command('bun',['--version']).trim()!=='1.4.4'){
      const response=await fetch('https://github.com/oven-sh/bun/releases/download/bun-v1.4.4/bun-linux-x64.zip',{signal:AbortSignal.timeout(60000)})
      if(!response.ok)throw new Error('pinned TIP runtime unavailable '+response.status)
      const archive=join(temp,'bun.zip');writeFileSync(archive,Buffer.from(await response.arrayBuffer()));command('unzip',['-q',archive,'-d',join(temp,'runtime')]);bun=join(temp,'runtime/bun-linux-x64/bun')
    }
  }
  const version=command(bun,['--version']).trim(),cpu=/^model name\s*:\s*(.+)$/m.exec(readFileSync('/proc/cpuinfo','utf8'))?.[1]?.trim()
  const dirs={base:join(temp,'base'),candidate:join(temp,'candidate')},meta={base:restore(input,dirs.base,config.baseline),candidate:restore(input,dirs.candidate,config.candidate)}
  const hashes={base:harnessHashes(dirs.base),candidate:harnessHashes(dirs.candidate)}
  for(const side of ['base','candidate'] as const)command('bun',['install','--frozen-lockfile'],dirs[side])
  const solve=row.view==='chc'?['compare/chc/solve.ts',file,'--runs-ms','5000','--houdini-ms','58000']:row.view==='tip'?['compare/tip/solve.ts',file,'--ms','57000']:['compare/term/solve.ts',file,'--limit','60',...(row.view==='its-scc'?['--scc']:[])]
  for(let repeat=1;repeat<=3;repeat++){
    const order=(index+repeat)%2?['candidate','base'] as const:['base','candidate'] as const,outcomes:Record<string,unknown>={}
    for(const side of order){
      const result=await runResourceMeasured(bun,solve,dirs[side],`${index}-${repeat}-${side}`),wallMs=result.wallMs,stdout=result.stdout,stderr=result.stderr
      const stages=stdout.split('\n').flatMap(line=>{try{return[JSON.parse(line)]}catch{return[]}})
      const last=row.view.startsWith('its')?[...stages].reverse().find(stage=>'answer'in stage):stages.at(-1)
      const answer=(row.view==='tip'&&last?.stage!=='answer'?undefined:last?.answer)??(result.status===124?'timeout':'error')
      outcomes[side]={resources:result.resources,exit:result.status,signal:result.signal,error:result.error?.message,answer,wallMs,stages,expected,wrong:expected!==undefined&&['sat','unsat'].includes(answer)&&answer!==expected,stderrSha256:digest(stderr),stdoutSha256:digest(stdout),stderrTail:answer==='error'?stderr.slice(-3000):undefined,traceGzipBase64:gzipSync(Buffer.from(stdout+'\n---stderr---\n'+stderr)).toString('base64'),trackedChanges:command('git',['status','--porcelain','--untracked-files=no'],dirs[side])}
    }
    console.log('BAR_PAIR '+JSON.stringify({index,...row,repeat,order,cpu,bun:version,strictSeconds:60,solve,inputs,meta,hashes,outcomes}))
  }
}finally{rmSync(temp,{recursive:true,force:true})}
