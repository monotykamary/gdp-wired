// Six sequential fresh processes on one exclusive VM. No later gate is run.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync,readdirSync,statSync} from 'node:fs'
import {join} from 'node:path'
const [root,baseline,input,out]=process.argv.slice(2)
if(!root||!baseline||!input||!out)throw new Error('ROOT BASELINE INPUT OUT required')
const hash=(p:string)=>createHash('sha256').update(readFileSync(p)).digest('hex')
const files=(dir:string,prefix=''):string[]=>readdirSync(dir).sort().flatMap(n=>statSync(join(dir,n)).isDirectory()?files(join(dir,n),prefix+n+'/'):[prefix+n])
const kernel=files(join(root,'kernel')),kernelEqual=kernel.every(p=>hash(join(root,'kernel',p))===hash(join(baseline,'kernel',p)))
const harness='research/track-m/profile-family.ts',harnessEqual=hash(join(root,harness))===hash(join(baseline,harness))
if(!kernelEqual||!harnessEqual)throw new Error('kernel or existing harness changed')
for(const p of ['package.json','bun.lock'])if(hash(join(root,p))!==hash(join(baseline,p)))throw new Error('dependency drift: '+p)
const modified=files(join(root,'core')).filter(p=>{try{return hash(join(root,'core',p))!==hash(join(baseline,'core',p))}catch{return true}})
writeFileSync(join(out,'manifest.json'),JSON.stringify({baselineCommit:readFileSync(join(root,'baseline-input/baseline.commit'),'utf8').trim(),kernelEqual,harnessEqual,harnessSha256:hash(join(root,harness)),inputSha256:hash(input),modifiedCore:modified,bun:Bun.version,bunRevision:Bun.revision},null,2)+'\n')
const cases:any[]=[]
for(const repeat of [1,2,3])for(const side of ['A','B']){
 const id=side+repeat,cwd=side==='A'?baseline:root,stdout=join(out,id+'.log'),stderr=join(out,id+'.stderr.log')
 console.log(JSON.stringify({event:'start',id,side,repeat,at:new Date().toISOString()}))
 const child=Bun.spawn(['/usr/bin/timeout','-s','KILL','360',process.execPath,'research/track-m/profile-cost-wins.ts',input],{cwd,env:{...process.env,TRACK_M_FAMILY_TRACE:'0',TRACK_M_COST_PROFILE:'0'},stdout:Bun.file(stdout),stderr:Bun.file(stderr)})
 const exitCode=await child.exited,rows=readFileSync(stdout,'utf8').split('\n').filter(s=>s.startsWith('{')).map(s=>JSON.parse(s)),laws=rows.filter(r=>r.mode==='family').map(r=>({...r,cache:rows.find(s=>s.mode==='cost-win-stats'&&s.law===r.law)?.stats??null}))
 const result={id,side,repeat,exitCode,laws,total:rows.find(r=>r.mode==='family-total')}
 cases.push(result);writeFileSync(join(out,'measurements.json'),JSON.stringify(cases,null,2)+'\n')
 console.log(JSON.stringify({event:'end',id,exitCode,laws:laws.map(r=>({law:r.law,proven:r.proven,checked:r.checked,units:r.countedMs,wallMs:r.wallMs,cache:r.cache}))}))
 if(exitCode!==0||laws.length!==5)throw new Error('incomplete process '+id)
}
const names=cases[0].laws.map((r:any)=>r.law),median=(xs:number[])=>[...xs].sort((a,b)=>a-b)[1]!,verdict=(r:any)=>[r.proven,r.checked]
const laws=names.map((law:string)=>{
 const a=cases.filter(r=>r.side==='A').map(r=>r.laws.find((x:any)=>x.law===law)),b=cases.filter(r=>r.side==='B').map(r=>r.laws.find((x:any)=>x.law===law))
 const project=(rows:any[])=>({verdicts:rows.map(verdict),countedUnits:rows.map(r=>r.countedMs),wallMedianMs:median(rows.map(r=>r.wallMs)),wallMaxMs:Math.max(...rows.map(r=>r.wallMs)),cache:rows.map(r=>r.cache)})
 return {law,verdictsIdentical:[...a,...b].every(r=>JSON.stringify(verdict(r))===JSON.stringify(verdict(a[0]))),A:project(a),B:project(b)}
})
const summary={test:'default-on cost wins',order:cases.map(r=>r.id),baseline:'50109a36',kernelEqual,harnessEqual,laws,allVerdictsIdentical:laws.every((r:any)=>r.verdictsIdentical),laterGatesRun:false}
writeFileSync(join(out,'summary.json'),JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify(summary))
if(!summary.allVerdictsIdentical)throw new Error('verdict regression')
