import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {parseTestSummary} from '../../../research/lane-i/validation-audit.ts'
const root='runs/lane-i/consensus-fixes/validation',names=['fixes-check','fixes-count-tests','fixes-finite-tests']
const rows=readFileSync(root+'/summary.tsv','utf8').trim().split('\n').map(line=>line.split('\t')),placement=JSON.parse(readFileSync(root+'/placement.json','utf8')),issues:string[]=[]
if(rows.length!==3||new Set(rows.map(row=>row[0])).size!==3||rows.some(row=>!names.includes(row[0]!)))issues.push('roster mismatch')
const jobs=names.map(name=>{
 const row=rows.find(row=>row[0]===name),p=placement[name],log=readFileSync(`${root}/${name}.log`,'utf8')
 if(row?.[1]!=='0')issues.push(`${name}: exit ${row?.[1]}`)
 if(row?.[3]!=='boat'||p?.exclusive!==true||p.co_tenants!==0||p.type!=='large'||!p.cpu)issues.push(`${name}: placement`)
 const parsed=name==='fixes-check'?{issues:/^Found 0 warnings and 0 errors\.$/m.test(log)?[]:['no clean check summary'],passed:0,assertions:0}:parseTestSummary(log)
 issues.push(...parsed.issues.map(issue=>`${name}: ${issue}`))
 return {name,exit:Number(row?.[1]),placement:p,sha256:createHash('sha256').update(log).digest('hex'),...parsed}
})
const report={finalGate:false,source:'44ad3947d887aa9e5269bb8ca98ed9b1fea2ad8b',snapshot:'2a77bdce4309',issues,passed:jobs.reduce((n,row)=>n+row.passed,0),assertions:jobs.reduce((n,row)=>n+row.assertions,0),jobs}
writeFileSync('runs/lane-i/consensus-fixes/validation-audit.json',JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({issues,passed:report.passed,assertions:report.assertions}))
if(issues.length)process.exitCode=1
