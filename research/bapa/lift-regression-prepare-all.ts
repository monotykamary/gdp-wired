import {spawnSync} from 'node:child_process'
import {join} from 'node:path'
import {writeFileSync} from 'node:fs'
import {assert,hashFile,json,type Input} from './lift-regression.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR;assert(out,'remote output directory required')
const rows:unknown[]=[]
for(const e of json<Input[]>('research/bapa/lift-regression-inputs.json').filter(e=>e.sourceScope==='frozen-capsule-original')){
  const child=spawnSync(process.execPath,['research/bapa/lift-regression-prepare.ts',e.id],{env:process.env,encoding:'utf8',timeout:180000,maxBuffer:8*1024*1024,killSignal:'SIGKILL'})
  const log=join(out,e.id+'.prepare.log');writeFileSync(log,(child.stdout??'')+'\n'+(child.stderr??''),{flag:'wx'})
  rows.push({id:e.id,exitCode:child.status,signal:child.signal,error:child.error?.message,logSha256:hashFile(log)})
}
writeFileSync(join(out,'FIXTURE-PREPARATION.json'),JSON.stringify({schema:'gdp-lift-fixture-preparation/v1',noSearch:true,noLean:true,rows},null,2)+'\n',{flag:'wx'})
if(rows.some((r:any)=>r.exitCode!==0||r.signal||r.error))process.exitCode=1
