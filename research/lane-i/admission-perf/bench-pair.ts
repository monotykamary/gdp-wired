import {strict as a} from 'node:assert'
import {mkdtempSync,rmSync,readFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {join,resolve} from 'node:path'
const input=resolve('port-input'),roots:Record<string,string>={}
function run(cmd:string,args:string[],cwd:string,env=process.env){const r=spawnSync(cmd,args,{cwd,env,encoding:'utf8',timeout:550000,maxBuffer:32*1024*1024});if(r.status!==0||r.error)throw Error(`${cmd}: ${r.status} ${r.error} ${r.stderr}`);return r.stdout}
try {
 for(const key of ['baseline','candidate']){const root=roots[key]=mkdtempSync('/tmp/admit-'+key+'-');run('tar',['-xf',join(input,key==='baseline'?'baseline.tar':'source.tar'),'-C',root],root);for(const vendor of ['gdp-ts','handwired'])run('tar',['-xf',join(input,vendor+'.tar'),'-C',root],root);run('bun',['install','--frozen-lockfile'],root)}
 const env={...Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'}
 const rows:{tag:string,raw:Record<string,number>,units:number,checksum:number,bootId:string,admissionCallsPerNode:number,wallMs:number}[]=[]
 for(const tag of ['baseline','candidate','candidate','baseline']){
  const text=run('bun',[join(input,'bench-child.ts'),roots[tag]!,tag,'200000'],roots[tag]!,env)
  process.stdout.write(text);const line=text.split('\n').find(s=>s.startsWith('ADMISSION_MEASURE '));a(line);rows.push(JSON.parse(line.slice(18)))
 }
 for(const r of rows){a.deepEqual(r.raw,rows[0].raw);a.equal(r.units,rows[0].units);a.equal(r.checksum,rows[0].checksum);a.equal(r.bootId,rows[0].bootId);a.equal(r.admissionCallsPerNode,1)}
 const mean=(tag:string)=>rows.filter(r=>r.tag===tag).reduce((n,r)=>n+r.wallMs,0)/2
 console.log('ADMISSION_PAIR '+JSON.stringify({baseline:readFileSync(join(input,'baseline-source.txt'),'utf8').trim(),candidate:readFileSync(join(input,'source.txt'),'utf8').trim(),baselineMs:mean('baseline'),candidateMs:mean('candidate'),speedup:mean('baseline')/mean('candidate'),rawIdentical:true,units:rows[0].units,rows}))
}finally{for(const root of Object.values(roots))rmSync(root,{recursive:true,force:true})}
