import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {parseMldrPair} from '../../../research/lane-i/validation-audit.ts'
const digest=(text:string)=>createHash('sha256').update(text).digest('hex')
const read=(path:string)=>readFileSync(path,'utf8')
const identity=JSON.parse(read('runs/lane-i/rebased-4497/input/identity.json'))
const root='runs/lane-i/rebased-4497/mldr',placement=JSON.parse(read(root+'/placement.json'))
const rows=read(root+'/summary.tsv').trim().split('\n').map(line=>line.split('\t')),issues:string[]=[]
if(rows.length!==3||new Set(rows.map(row=>row[0])).size!==3||rows.some(row=>!['mldr-r1','mldr-r2','mldr-r3'].includes(row[0]!)))issues.push('MLDR roster mismatch')
const jobs=[1,2,3].map(repeat=>{
 const name=`mldr-r${repeat}`,outer=read(`${root}/${name}.log`),p=placement[name],row=rows.find(row=>row[0]===name)
 if(row?.[1]!=='0'||row?.[3]!=='boat'||p?.exclusive!==true||p.co_tenants!==0||p.type!=='large'||!p.cpu)issues.push(`${name}: status/placement`)
 const encoded=[...outer.matchAll(/^LANE_I_CAPTURE_GZIP (\S+)$/gm)],metas=[...outer.matchAll(/^LANE_I_CAPTURE_META (.+)$/gm)]
 if(encoded.length!==1||metas.length!==1)throw Error(`${name}: invalid envelope`)
 const meta=JSON.parse(metas[0]![1]!),log=gunzipSync(Buffer.from(encoded[0]![1]!,'base64')).toString('utf8')
 if(meta.exit!==0||digest(log)!==meta.sha256)throw Error(`${name}: capture exit/hash mismatch`)
 if(!log.includes(identity.baseline)||!log.includes(identity.candidate))issues.push(`${name}: source identity`)
 writeFileSync(`${root}/${name}.full.log`,log)
 const parsed=parseMldrPair(log,repeat)
 issues.push(...parsed.issues.map(issue=>`${name}: ${issue}`))
 return {name,placement:p,outerSha256:digest(outer),rawSha256:meta.sha256,remoteRawPath:meta.path,...parsed}
})
writeFileSync('runs/lane-i/rebased-4497/mldr-audit.json',JSON.stringify({finalGate:false,scope:'Pre-consensus-fix original MLDR pairs only',identity,issues,jobs},null,2)+'\n')
console.log(JSON.stringify({scope:'MLDR',issues,jobs:jobs.map(job=>({name:job.name,sides:job.sides.map(side=>({side:side.side,result:side.result,generationWallMs:side.generationWallMs,attempts:side.attempts?.length}))}))}))
const full='runs/lane-i/combined-4497/validation',pFull=JSON.parse(read(full+'/placement.json')),rFull=read(full+'/summary.tsv').trim().split('\n').map(line=>line.split('\t')),fullIssues:string[]=[]
const names=['combined-check',...Array.from({length:7},(_,i)=>`combined-tests-${i+1}`)]
if(rFull.length!==8||new Set(rFull.map(row=>row[0])).size!==8||rFull.some(row=>!names.includes(row[0]!)))fullIssues.push('combined roster mismatch')
const fullJobs=names.map(name=>{
 const row=rFull.find(row=>row[0]===name),p=pFull[name],log=read(`${full}/${name}.log`)
 if(row?.[1]!=='0')fullIssues.push(`${name}: exit ${row?.[1]}`)
 if(row?.[3]!=='boat'||p?.exclusive!==true||p.co_tenants!==0||p.type!=='large'||!p.cpu)fullIssues.push(`${name}: placement`)
 const pass=[...log.matchAll(/^\s*(\d+) pass\s*$/gm)],fail=[...log.matchAll(/^\s*(\d+) fail\s*$/gm)],assertions=[...log.matchAll(/^\s*(\d+) expect\(\) calls\s*$/gm)]
 if(name!=='combined-check'&&(!pass.length||pass.length!==fail.length||fail.some(row=>Number(row[1])!==0)||/^\s*[1-9]\d* errors?\s*$/m.test(log)))fullIssues.push(`${name}: invalid test summaries`)
 if(name==='combined-check'&&!/^Found 0 warnings and 0 errors\.$/m.test(log))fullIssues.push('combined-check: no clean check summary')
 return {name,exit:Number(row?.[1]),placement:p,sha256:digest(log),testGroups:pass.length,passed:pass.reduce((n,row)=>n+Number(row[1]),0),assertions:assertions.reduce((n,row)=>n+Number(row[1]),0)}
})
const report={finalGate:false,source:'399c328a8a646958a1a9c24cb19bf68532bf9df9',snapshot:'d0c41b3366da',scope:'Pre-consensus-fix combined source; original failed check retained',issues:fullIssues,passed:fullJobs.reduce((n,row)=>n+row.passed,0),assertions:fullJobs.reduce((n,row)=>n+row.assertions,0),jobs:fullJobs}
writeFileSync('runs/lane-i/combined-4497/validation-audit.json',JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({scope:'combined',issues:fullIssues,passed:report.passed,assertions:report.assertions}))
if(issues.length||fullIssues.length)process.exitCode=1
