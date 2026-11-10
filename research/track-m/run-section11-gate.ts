// The existing five-law harness, byte-identical on A and B. No later gates.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync,readdirSync,statSync} from 'node:fs'
import {join} from 'node:path'
const [root,baseline,input,out]=process.argv.slice(2)
if(!root||!baseline||!input||!out)throw new Error('ROOT BASELINE INPUT OUT required')
const hash=(p:string)=>createHash('sha256').update(readFileSync(p)).digest('hex')
const files=(dir:string,prefix=''):string[]=>readdirSync(dir).sort().flatMap(n=>statSync(join(dir,n)).isDirectory()?files(join(dir,n),prefix+n+'/'):[prefix+n])
const baselineCommit=readFileSync(join(root,'baseline-input/baseline.commit'),'utf8').trim(),candidateCommit=process.env.TRACK_M_CANDIDATE
if(!baselineCommit.startsWith('192ebbe2')||!candidateCommit)throw new Error('revision binding missing')
const kernel=files(join(root,'kernel')),kernelEqual=kernel.every(p=>hash(join(root,'kernel',p))===hash(join(baseline,'kernel',p))),harness='research/track-m/profile-family.ts',harnessEqual=hash(join(root,harness))===hash(join(baseline,harness))
if(!kernelEqual||!harnessEqual)throw new Error('kernel or existing harness changed')
for(const p of ['package.json','bun.lock'])if(hash(join(root,p))!==hash(join(baseline,p)))throw new Error('dependency drift')
const changedCore=files(join(root,'core')).filter(p=>hash(join(root,'core',p))!==hash(join(baseline,'core',p)))
const expected=['count-recovery/derivability-closure.ts','count-recovery/derivability-closure.test.ts','count-recovery/leaf-allowance.ts','count-recovery/leaf-allowance.test.ts'].sort()
if(JSON.stringify(changedCore)!==JSON.stringify(expected))throw new Error('unexpected core diff: '+JSON.stringify(changedCore))
const manifest={baselineCommit,candidateCommit,kernelEqual,harnessEqual,harnessSha256:hash(join(root,harness)),inputSha256:hash(input),changedCore,sourceHashes:Object.fromEntries(changedCore.map(p=>[p,hash(join(root,'core',p))])),bun:Bun.version}
writeFileSync(join(out,'manifest.json'),JSON.stringify(manifest,null,2)+'\n')
const records:any[]=[]
for(const repeat of [1,2,3])for(const side of ['A','B']){
 const id=side+repeat,cwd=side==='A'?baseline:root
 console.log(JSON.stringify({event:'start',id}))
 const child=Bun.spawn(['/usr/bin/timeout','-s','KILL','360',process.execPath,'research/track-m/profile-cost-wins.ts',input],{cwd,env:{...process.env,TRACK_M_FAMILY_TRACE:'0',TRACK_M_COST_PROFILE:'0'},stdout:Bun.file(join(out,id+'.log')),stderr:Bun.file(join(out,id+'.stderr.log'))})
 const exitCode=await child.exited,rows=readFileSync(join(out,id+'.log'),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)),laws=rows.filter(r=>r.mode==='family'),total=rows.find(r=>r.mode==='family-total')
 records.push({id,side,repeat,exitCode,laws,total});writeFileSync(join(out,'measurements.json'),JSON.stringify(records,null,2)+'\n')
 console.log(JSON.stringify({event:'end',id,exitCode,laws:laws.map(r=>({law:r.law,proven:r.proven,checked:r.checked,units:r.countedMs,wallMs:r.wallMs})),familyWallMs:total?.wallMs}))
 if(exitCode!==0||laws.length!==5||!total)throw new Error('incomplete process '+id)
}
const median=(xs:number[])=>[...xs].sort((a,b)=>a-b)[1]!,project=(rs:any[])=>({verdicts:rs.map(r=>({proven:r.proven,checked:r.checked})),countedUnits:rs.map(r=>r.countedMs),wallMedianMs:median(rs.map(r=>r.wallMs)),wallMaxMs:Math.max(...rs.map(r=>r.wallMs))})
const laws=records[0].laws.map((first:any)=>{const law=first.law,a=records.filter(r=>r.side==='A').map(r=>r.laws.find((l:any)=>l.law===law)),b=records.filter(r=>r.side==='B').map(r=>r.laws.find((l:any)=>l.law===law));return {law,A:project(a),B:project(b),noRegression:a.every((r:any,i:number)=>!r.checked||b[i].checked)}})
const families=Object.fromEntries(['A','B'].map(side=>{const rs=records.filter(r=>r.side===side),wallMs=rs.map(r=>r.total.wallMs);return [side,{wallMs,wallMedianMs:median(wallMs),wallMaxMs:Math.max(...wallMs),checkedCounts:rs.map(r=>r.laws.filter((l:any)=>l.proven&&l.checked).length)}]}))
const summary={test:'Section 11 two-defect repair',...manifest,order:records.map(r=>r.id),laws,families,noRegression:laws.every((l:any)=>l.noRegression),laterGatesRun:false}
writeFileSync(join(out,'summary.json'),JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify(summary))
