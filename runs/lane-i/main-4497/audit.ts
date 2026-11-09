import {readFileSync, writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {execFileSync} from 'node:child_process'
import {parseTestSummary} from '../../../research/lane-i/validation-audit'
const root = 'runs/lane-i/main-4497/validation'
const names = ['main4497-check', 'main4497-runtime', 'main4497-extraction']
const rows = readFileSync(`${root}/summary.tsv`, 'utf8').trim().split('\n').map(line => line.split('\t'))
const placement = JSON.parse(readFileSync(`${root}/placement.json`, 'utf8'))
const issues: string[] = []
if (rows.length !== names.length || new Set(rows.map(row=>row[0])).size !== names.length || rows.some(row=>!names.includes(row[0]!))) issues.push('roster mismatch')
const jobs = names.map(name => {
 const row = rows.find(row=>row[0]===name), p = placement[name]
 const log = readFileSync(`${root}/${name}.log`, 'utf8')
 if (row?.[1] !== '0' || row?.[3] !== 'boat' || !Number.isFinite(Number(row?.[2]))) issues.push(`${name}: invalid exit/backend/wall`)
 if (!p?.exclusive || p.co_tenants !== 0 || p.type !== 'large' || !p.cpu) issues.push(`${name}: invalid placement`)
 for (const archive of ['main.tar','handwired.tar','gdp-ts.tar']) if (!log.includes(`${archive}: OK`)) issues.push(`${name}: missing archive check ${archive}`)
 const parsed = name === 'main4497-check' ? {issues: /^Found 0 warnings and 0 errors\.$/m.test(log) ? [] : ['missing clean check summary'], passed: 0, assertions: 0} : parseTestSummary(log)
 issues.push(...parsed.issues.map(issue=>`${name}: ${issue}`))
 return {name, exit:Number(row?.[1]), seconds:Number(row?.[2]), placement:p, sha256:createHash('sha256').update(log).digest('hex'), ...parsed}
})
const report = {finalGate:false, scope:'Mechanical main-merge qualification only, before later lane-tip integrations', source:execFileSync('git',['rev-parse','91f2d2d9'],{encoding:'utf8'}).trim(), snapshot:'60b56e8cdad1', batch:'20261110-033045-5mxrqt', issues, passed:jobs.reduce((sum,job)=>sum+job.passed,0), assertions:jobs.reduce((sum,job)=>sum+job.assertions,0), jobs}
writeFileSync('runs/lane-i/main-4497/validation-audit.json',JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({issues,passed:report.passed,assertions:report.assertions,source:report.source}))
if (issues.length) process.exitCode=1
