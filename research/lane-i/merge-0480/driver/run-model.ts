import {createHash} from 'node:crypto'
import {existsSync,mkdtempSync,readFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {gunzipSync} from 'node:zlib'
const input=resolve('port-input'),[target,id,amount]=process.argv.slice(2)
if(!['candidate','baseline'].includes(target!))throw Error('bad target')
const root=mkdtempSync(join(tmpdir(),'candidate-original-'))
const source=target==='candidate'?readFileSync(join(input,'source.txt'),'utf8').trim():'5aa7681815e41a939fed137783b656abeeacc1e6'
const env={...Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',GDP_COUNT_STRATEGIES:'1',GDP_COUNT_TIERS:'1',GDP_COUNT_FRAMES:'1'}
function command(cmd:string,args:string[]){const r=spawnSync(cmd,args,{cwd:root,env,encoding:'utf8',maxBuffer:32*1024*1024,timeout:180000});if(r.status!==0)throw Error(`${cmd}: ${r.stderr}`)}
try{
 command('tar',['-xf',join(input,target==='candidate'?'source.tar':'baseline.tar'),'-C',root])
 for(const module of ['gdp-ts','handwired'])command('tar',['-xf',join(input,`${module}.tar`),'-C',root])
 command('bun',['install','--frozen-lockfile'])
 const file=join(root,'measurement.json.gz')
 const run=spawnSync('bun',[...(process.env.GDP_CENSUS_TRIPWIRE==='1'?['--preload',join(input,'census-preload.ts')]:[]),join(input,'measure.ts'),root,id!,amount!,file,source,target!],{cwd:root,env,encoding:'utf8',timeout:480000,maxBuffer:32*1024*1024})
 if(run.stdout)process.stdout.write(run.stdout)
 if(run.stderr)process.stderr.write(run.stderr)
 if(run.error||run.status!==0||!existsSync(file)){console.log('CANDIDATE_CASE '+JSON.stringify({target,id,source,allowance:Number(amount),status:run.error?'driver-timeout':'driver-error',exit:run.status,signal:run.signal,error:run.error?.message}));process.exitCode=1}
 else{
  const bytes=readFileSync(file),data=JSON.parse(gunzipSync(bytes).toString())
  const roots=data.phases.filter((p:any)=>p.parentId===null)
  if(roots.length!==1||Object.keys(data.raw).some(k=>roots[0].raw[k]!==data.raw[k]))throw Error('root phase ledger differs from raw totals')
  const summary={target,id,source,allowance:data.allowance,result:data.result,units:data.units,searchUnits:data.searchUnits,raw:data.raw,generated:data.generated,phaseCount:data.phases.length,eventCount:data.events.length,queryCount:data.queries.length,bytes:bytes.length,sha256:createHash('sha256').update(bytes).digest('hex')}
  console.log('CANDIDATE_CASE '+JSON.stringify(summary))
  console.log('CANDIDATE_RECEIPT '+JSON.stringify({target,id,source,allowance:data.allowance,sha256:summary.sha256,gzipBase64:bytes.toString('base64')}))
 }
}finally{rmSync(root,{recursive:true,force:true})}
