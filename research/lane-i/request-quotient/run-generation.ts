import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),[id,kind,repeatsText='1']=process.argv.slice(2),root=mkdtempSync('/tmp/quotient-generation-')
const clean=Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_')))
function run(cmd:string,args:string[],env=clean){const p=spawnSync(cmd,args,{cwd:root,env,encoding:'utf8',timeout:600000,maxBuffer:32*1024*1024});process.stdout.write(p.stdout??'');process.stderr.write(p.stderr??'');if(p.error||p.status!==0)throw Error(`${cmd} failed (${p.status}): ${p.error??''}`)}
try{
 for(const name of['source','gdp-ts','handwired'])run('tar',['-xf',join(input,name+'.tar'),'-C',root])
 run('bun',['install','--frozen-lockfile'])
 for(let repeat=0;repeat<Number(repeatsText);repeat++)for(const flag of(kind==='classes'?['1']:repeat%2?['1','0']:['0','1'])){
  console.log('QUOTIENT_MEASUREMENT_CONTEXT '+JSON.stringify({source:readFileSync(join(input,'source.txt'),'utf8').trim(),id,kind,repeat,flag}))
  run('bun',[join(input,'measure-generation.ts'),root,id!,kind!],{...clean,GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',GDP_REQUEST_QUOTIENT:flag})
 }
}finally{rmSync(root,{recursive:true,force:true})}
