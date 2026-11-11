import {strict as a} from 'node:assert'
import {mkdtempSync,rmSync,readFileSync,copyFileSync,mkdirSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {join,resolve} from 'node:path'
import {cpus} from 'node:os'
const input=resolve('port-input'),roots:Record<string,string>={},mode=process.argv[2]
function run(cmd:string,args:string[],cwd:string,env=process.env){const r=spawnSync(cmd,args,{cwd,env,encoding:'utf8',timeout:2100000,maxBuffer:32*1024*1024});if(r.status!==0||r.error)throw Error(`${cmd}: ${r.status} ${r.error} ${r.stderr}`);return r.stdout}
try{
 for(const key of ['baseline','candidate']){const root=roots[key]=mkdtempSync('/tmp/admission-native-'+key+'-');run('tar',['-xf',join(input,key==='baseline'?'baseline.tar':'source.tar'),'-C',root],root);for(const vendor of ['gdp-ts','handwired'])run('tar',['-xf',join(input,vendor+'.tar'),'-C',root],root);run('bun',['install','--frozen-lockfile'],root);const at=join(root,'research/track-fable');mkdirSync(at,{recursive:true});copyFileSync(join(input,'fixture.json'),join(at,'counter-fixture.json'));copyFileSync(join(input,'engine-probe.ts.source'),join(at,'engine-tiny.ts'))}
 const rows:{tag:string,wallMs:number,raw:unknown,units:number,outcome:unknown,profile:unknown,result:unknown}[]=[]
 console.log('NATIVE_HOST '+JSON.stringify({models:[...new Set(cpus().map(c=>c.model))],bootId:readFileSync('/proc/sys/kernel/random/boot_id','utf8').trim()}))
 for(const tag of ['baseline','candidate','candidate','baseline']){
  const env={...Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',COUNTER_SOURCE:readFileSync(join(input,tag==='baseline'?'baseline-source.txt':'source.txt'),'utf8').trim()}
  const text=run('bun',[join(roots[tag]!,'research/track-fable/engine-tiny.ts'),'reach','1','2',...(mode==='compiled'?['compiled']:[])],roots[tag]!,env)
  process.stdout.write(text);const terminal=text.split('\n').find(s=>s.startsWith('COUNTER_PROBE ')),resultLine=text.split('\n').find(s=>s.startsWith('RESULT '));a(terminal);a(resultLine);const r=JSON.parse(terminal.slice(14)),result=JSON.parse(resultLine.slice(7));delete result.ms;rows.push({tag,...r,result})
 }
 for(const r of rows){a.deepEqual(r.raw,rows[0]!.raw);a.equal(r.units,rows[0]!.units);a.deepEqual(r.outcome,rows[0]!.outcome);a.deepEqual(r.result,rows[0]!.result);a.deepEqual(r.profile,rows[0]!.profile)}
 const mean=(tag:string)=>rows.filter(r=>r.tag===tag).reduce((n,r)=>n+r.wallMs,0)/2
 console.log('NATIVE_PAIR '+JSON.stringify({mode,baseline:readFileSync(join(input,'baseline-source.txt'),'utf8').trim(),candidate:readFileSync(join(input,'source.txt'),'utf8').trim(),baselineMs:mean('baseline'),candidateMs:mean('candidate'),speedup:mean('baseline')/mean('candidate'),rawIdentical:true,rows}))
}finally{for(const root of Object.values(roots))rmSync(root,{recursive:true,force:true})}
