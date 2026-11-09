import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
import {parseTestSummary} from '../../../research/lane-i/validation-audit.ts'
const [dir,jobsPath,identityPath]=process.argv.slice(2)
if(!dir||!jobsPath||!identityPath)throw Error('directory, jobs and identity required')
const identity=JSON.parse(readFileSync(identityPath,'utf8')),spec=JSON.parse(readFileSync(jobsPath,'utf8')) as {name:string}[],names=spec.map(row=>row.name)
const rows=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),issues:string[]=[]
if(rows.length!==names.length||new Set(rows.map(row=>row[0])).size!==names.length||rows.some(row=>!names.includes(row[0]!)))issues.push('roster mismatch')
const jobs=names.map(name=>{
 const row=rows.find(row=>row[0]===name),p=placement[name],log=readFileSync(join(dir,name+'.log'),'utf8')
 if(row?.[1]!=='0')issues.push(`${name}: exit ${row?.[1]}`)
 if(row?.[3]!=='boat'||p?.exclusive!==true||p.co_tenants!==0||p.type!=='large'||!p.cpu)issues.push(`${name}: placement`)
 for(const archive of ['main.tar','handwired.tar','gdp-ts.tar'])if(!log.includes(archive+': OK'))issues.push(`${name}: archive check`)
 const isCheck=name.endsWith('check'),parsed=isCheck?{issues:[] as string[],passed:0,assertions:0}:parseTestSummary(log)
 if(isCheck){
  if(!/^Found 0 warnings and 0 errors\.$/m.test(log))parsed.issues.push('no clean type/lint summary')
  const hashes=[...log.matchAll(/^COUNT_RUNTIME_IDENTICAL ([a-f0-9]{64})$/gm)]
  if(hashes.length!==1||hashes[0]?.[1]!==identity.runtimeSha256)parsed.issues.push('missing/mismatched emitted runtime identity')
 }
 issues.push(...parsed.issues.map(issue=>`${name}: ${issue}`))
 return {name,exit:Number(row?.[1]),placement:p,sha256:createHash('sha256').update(log).digest('hex'),...parsed}
})
const report={finalGate:false,identity,issues,passed:jobs.reduce((n,row)=>n+row.passed,0),assertions:jobs.reduce((n,row)=>n+row.assertions,0),jobs}
writeFileSync(join(dir,'validation-audit.json'),JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({candidate:identity.candidate,issues,passed:report.passed,assertions:report.assertions,finalGate:false}))
if(issues.length)process.exitCode=1
