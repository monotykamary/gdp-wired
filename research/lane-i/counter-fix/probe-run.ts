import {mkdtempSync,readFileSync,writeFileSync,copyFileSync,mkdirSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),[target,...args]=process.argv.slice(2)
if(!['candidate','baseline'].includes(target!))throw Error('unknown source')
const source=readFileSync(join(input,target==='candidate'?'source.txt':'baseline-source.txt'),'utf8').trim()
const root=mkdtempSync('/tmp/counter-probe-')
function command(cmd:string,argv:string[],timeout=120000){const r=spawnSync(cmd,argv,{cwd:root,encoding:'utf8',timeout,maxBuffer:32*1024*1024});process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');if(r.status!==0||r.error)throw Error(cmd+': '+r.status+' '+String(r.error))}
try {
 command('tar',['-xf',join(input,target==='candidate'?'source.tar':'baseline.tar'),'-C',root])
 for(const module of ['gdp-ts','handwired'])command('tar',['-xf',join(input,module+'.tar'),'-C',root])
 command('bun',['install','--frozen-lockfile'])
 const at=join(root,'research/track-fable');mkdirSync(at,{recursive:true})
 copyFileSync(join(input,'fixture.json'),join(at,'counter-fixture.json'))
 copyFileSync(join(input,'engine-probe.ts.source'),join(at,'engine-tiny.ts'))
 const env={...Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',COUNTER_SOURCE:source}
 const r=spawnSync('bun',[join(at,'engine-tiny.ts'),...args],{cwd:root,env,encoding:'utf8',timeout:2100000,maxBuffer:32*1024*1024})
 process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');if(r.status!==0||r.error)throw Error('probe failed '+r.status+' '+String(r.error))
 if(!(r.stdout??'').includes('COUNTER_PROBE '))throw Error('missing terminal receipt')
 writeFileSync(join(root,'probe-complete.txt'),source)
} finally {rmSync(root,{recursive:true,force:true})}
