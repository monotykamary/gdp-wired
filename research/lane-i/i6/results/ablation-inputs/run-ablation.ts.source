import {mkdtempSync,readFileSync,existsSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const input=resolve('port-input'),[id,w,mode]=process.argv.slice(2),root=mkdtempSync('/tmp/i6-ablation-')
const env={...Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',GDP_COUNT_STRATEGIES:'1',GDP_COUNT_TIERS:'1',GDP_COUNT_FRAMES:'1'}
function run(command:string,args:string[],timeout=120000){const r=spawnSync(command,args,{cwd:root,env,encoding:'utf8',timeout,maxBuffer:32*1024*1024});if(r.status!==0||r.error)throw Error(`${command}: ${r.status} ${r.error} ${r.stderr}`);return r.stdout}
try{for(const name of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,name+'.tar'),'-C',root]);run('bun',['install','--frozen-lockfile']);const out=join(root,'ablation.json.gz'),source=readFileSync(join(input,'source.txt'),'utf8').trim();process.stdout.write(run('bun',['--preload',join(input,'census-preload.ts'),join(input,'ablate-writers.ts'),root,id!,w!,mode!,out,source],650000));if(!existsSync(out))throw Error('missing receipt');const b=readFileSync(out);console.log('I6_ABLATION_RECEIPT '+JSON.stringify({id,w,mode,source,sha256:createHash('sha256').update(b).digest('hex'),gzipBase64:b.toString('base64')}))}finally{rmSync(root,{recursive:true,force:true})}
