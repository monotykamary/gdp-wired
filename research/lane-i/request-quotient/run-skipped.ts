import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),id=process.argv[2],root=mkdtempSync('/tmp/quotient-skipped-')
const env={...Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0',QUOTIENT_SOURCE:readFileSync(join(input,'source.txt'),'utf8').trim()}
function run(cmd:string,args:string[]){const p=spawnSync(cmd,args,{cwd:root,env,encoding:'utf8',timeout:840000,maxBuffer:32*1024*1024});process.stdout.write(p.stdout??'');process.stderr.write(p.stderr??'');if(p.error||p.status!==0)throw Error(`${cmd} failed (${p.status}): ${p.error??''}`)}
try{for(const name of['source','gdp-ts','handwired'])run('tar',['-xf',join(input,name+'.tar'),'-C',root]);run('bun',['install','--frozen-lockfile']);run('bun',[join(input,'audit-skipped.ts'),root,id!])}finally{rmSync(root,{recursive:true,force:true})}
