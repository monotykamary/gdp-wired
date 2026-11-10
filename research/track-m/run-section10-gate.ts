// Five-law replay only. No later gate or generated-family success is implied.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync,readdirSync,statSync} from 'node:fs'
import {join} from 'node:path'
const [root,baseline,input,out]=process.argv.slice(2)
if(!root||!baseline||!input||!out)throw new Error('ROOT BASELINE INPUT OUT required')
const hash=(p:string)=>createHash('sha256').update(readFileSync(p)).digest('hex')
const files=(dir:string,prefix=''):string[]=>readdirSync(dir).sort().flatMap(n=>statSync(join(dir,n)).isDirectory()?files(join(dir,n),prefix+n+'/'):[prefix+n])
const kernel=files(join(root,'kernel')),kernelEqual=kernel.every(p=>hash(join(root,'kernel',p))===hash(join(baseline,'kernel',p))),harness='research/track-m/profile-family.ts',harnessEqual=hash(join(root,harness))===hash(join(baseline,harness))
if(!kernelEqual||!harnessEqual)throw new Error('kernel or existing harness changed')
for(const p of ['package.json','bun.lock'])if(hash(join(root,p))!==hash(join(baseline,p)))throw new Error('dependency drift')
const modifiedCore=files(join(root,'core')).filter(p=>{try{return hash(join(root,'core',p))!==hash(join(baseline,'core',p))}catch{return true}})
writeFileSync(join(out,'manifest.json'),JSON.stringify({baselineCommit:readFileSync(join(root,'baseline-input/baseline.commit'),'utf8').trim(),kernelEqual,harnessEqual,harnessSha256:hash(join(root,harness)),inputSha256:hash(input),modifiedCore,bun:Bun.version},null,2)+'\n')
const cases:any[]=[]
for(const repeat of [1,2,3])for(const side of ['A','B']){
 const id=side+repeat,cwd=side==='A'?baseline:root,stdout=join(out,id+'.log'),stderr=join(out,id+'.stderr.log')
 console.log(JSON.stringify({event:'start',id}))
 const child=Bun.spawn(['/usr/bin/timeout','-s','KILL','360',process.execPath,'research/track-m/profile-cost-wins.ts',input],{cwd,env:{...process.env,TRACK_M_FAMILY_TRACE:'0',TRACK_M_COST_PROFILE:'0'},stdout:Bun.file(stdout),stderr:Bun.file(stderr)})
 const exitCode=await child.exited,rows=readFileSync(stdout,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)),laws=rows.filter(r=>r.mode==='family').map(r=>({...r,cache:rows.find(s=>s.mode==='cost-win-stats'&&s.law===r.law)?.stats??null})),total=rows.find(r=>r.mode==='family-total')
 cases.push({id,side,repeat,exitCode,laws,total});writeFileSync(join(out,'measurements.json'),JSON.stringify(cases,null,2)+'\n')
 console.log(JSON.stringify({event:'end',id,exitCode,laws:laws.map(r=>({law:r.law,proven:r.proven,checked:r.checked,units:r.countedMs,wallMs:r.wallMs})),familyWallMs:total?.wallMs}))
 if(exitCode!==0||laws.length!==5||!total)throw new Error('incomplete process '+id)
}
const names=cases[0].laws.map((r:any)=>r.law),median=(xs:number[])=>[...xs].sort((a,b)=>a-b)[1]!,verdict=(r:any)=>[r.proven,r.checked]
const laws=names.map((law:string)=>{
 const a=cases.filter(r=>r.side==='A').map(r=>r.laws.find((v:any)=>v.law===law)),b=cases.filter(r=>r.side==='B').map(r=>r.laws.find((v:any)=>v.law===law)),project=(rs:any[])=>({verdicts:rs.map(verdict),countedUnits:rs.map(r=>r.countedMs),wallMedianMs:median(rs.map(r=>r.wallMs)),wallMaxMs:Math.max(...rs.map(r=>r.wallMs)),cache:rs.map(r=>r.cache)})
 return {law,A:project(a),B:project(b),noRegression:a.every((r:any,i:number)=>!r.checked||b[i].checked),verdictsIdentical:[...a,...b].every(r=>JSON.stringify(verdict(r))===JSON.stringify(verdict(a[0])))}
})
const b=cases.filter(r=>r.side==='B'),allFiveEveryRepeat=b.every(r=>r.laws.every((l:any)=>l.proven&&l.checked)),under60EveryFamily=b.every(r=>r.total.wallMs<60000),summary={test:'Section 10 five-law replay',baseline:'50109a36',order:cases.map(r=>r.id),kernelEqual,harnessEqual,laws,noRegression:laws.every((l:any)=>l.noRegression),allFiveEveryRepeat,under60EveryFamily,gate1ReplayPass:allFiveEveryRepeat&&under60EveryFamily,familyWallMs:{A:cases.filter(r=>r.side==='A').map(r=>r.total.wallMs),B:b.map(r=>r.total.wallMs)},laterGatesRun:false,originalGeneratedHarnessRun:false}
writeFileSync(join(out,'summary.json'),JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify(summary))
