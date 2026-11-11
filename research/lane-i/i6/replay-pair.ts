import {strict as a} from 'node:assert'
import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),target=process.argv[2],roots:Record<string,string>={}
if(!['star','row'].includes(target!))throw Error('unknown B9 target')
function run(command:string,args:string[],cwd:string,env=process.env){const r=spawnSync(command,args,{cwd,env,encoding:'utf8',timeout:600000,maxBuffer:32*1024*1024});if(r.status!==0||r.error)throw Error(`${command}: ${r.status} ${r.error} ${r.stderr}\n${r.stdout}`);return r.stdout}
try{
 for(const tag of ['baseline','candidate']){const root=roots[tag]=mkdtempSync('/tmp/i6-replay-'+tag+'-');run('tar',['-xf',join(input,tag==='baseline'?'baseline.tar':'source.tar'),'-C',root],root);for(const vendor of ['gdp-ts','handwired'])run('tar',['-xf',join(input,vendor+'.tar'),'-C',root],root);run('bun',['install','--frozen-lockfile'],root)}
 type Row={tag:string,target:string,phase:string,inputSha:string,checked:boolean,wallMs:number,units:number,raw:Record<string,number>}
 const rows:Row[]=[],hosts:{bootId:string,models:string[]}[]=[]
 for(const tag of ['baseline','candidate','candidate','baseline']){
  const env={...Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'}
  const output=run('bun',[join(input,'replay-check.ts'),roots[tag]!,tag,join(input,target!+'-step.json'),join(input,target!+'-init.json')],roots[tag]!,env)
  process.stdout.write(output)
  for(const line of output.split('\n')){if(line.startsWith('I6_CHECK '))rows.push(JSON.parse(line.slice(9)));if(line.startsWith('I6_REPLAY_HOST '))hosts.push(JSON.parse(line.slice(15)))}
 }
 a.equal(hosts.length,4);for(const host of hosts)a.equal(host.bootId,hosts[0]!.bootId)
 for(const phase of ['step','init']){
  const cases=rows.filter(r=>r.phase===phase),base=cases.find(r=>r.tag==='baseline')!;a.equal(cases.length,4)
  for(const row of cases){a(row.checked);a.equal(row.inputSha,base.inputSha);for(const key of Object.keys(base.raw))if(!['tableCells','checkSteps','cubeTests'].includes(key))a.equal(row.raw[key],base.raw[key],key);if(row.tag==='baseline')for(const key of ['tableCells','checkSteps','cubeTests'])a.equal(row.raw[key],0);else {a(row.raw.tableCells!>0);a(row.raw.checkSteps!>0)}}
 }
 console.log('I6_REPLAY_PAIR '+JSON.stringify({target,baseline:readFileSync(join(input,'baseline-source.txt'),'utf8').trim(),candidate:readFileSync(join(input,'source.txt'),'utf8').trim(),otherColumnsIdentical:true,emptyDerivationsRejected:true,hosts,rows}))
}finally{for(const root of Object.values(roots))rmSync(root,{recursive:true,force:true})}
