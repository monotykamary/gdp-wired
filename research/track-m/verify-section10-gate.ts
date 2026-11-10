import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
import {auditSection10Gate} from './section10-gate-audit.ts'
const [dir,input,commit]=process.argv.slice(2);if(!dir||!input||!commit)throw new Error('DIR INPUT COMMIT required')
const manifest=JSON.parse(readFileSync(join(dir,'manifest.json'),'utf8')),rows=JSON.parse(readFileSync(join(dir,'measurements.json'),'utf8')),summary=JSON.parse(readFileSync(join(dir,'summary.json'),'utf8'))
if(manifest.baselineCommit!==readFileSync(commit,'utf8').trim()||manifest.inputSha256!==createHash('sha256').update(readFileSync(input)).digest('hex'))throw new Error('baseline or fixture changed')
const audit=auditSection10Gate(rows,manifest)
for(const law of audit.laws){const original=summary.laws.find((l:any)=>l.law===law.law);if(!original)throw new Error('missing summary law')
 for(const side of ['A','B'] as const){const value=law[side],saved=original[side]
  for(const field of ['countedUnits','wallMedianMs','wallMaxMs'] as const)if(JSON.stringify(value[field])!==JSON.stringify(saved[field]))throw new Error('summary mismatch: '+law.law+' '+side+' '+field)
  if(JSON.stringify(value.verdicts.map(v=>[v.proven,v.checked]))!==JSON.stringify(saved.verdicts))throw new Error('verdict mismatch')
 }
}
if(audit.noRegression!==summary.noRegression||audit.gate1ReplayPass!==summary.gate1ReplayPass||summary.laterGatesRun!==false||summary.originalGeneratedHarnessRun!==false)throw new Error('gate status mismatch')
console.log(JSON.stringify({test:'section10-final-validation',records:rows.length,lawVerdicts:rows.length*5,...audit},null,2))
