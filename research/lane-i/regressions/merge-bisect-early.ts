// Tiny, deterministic receipt decoding only; does not run any experiment.
import {readFileSync,writeFileSync} from 'node:fs'
import {decodeReceipt,auditSummary,summarize} from './merge-bisect-audit.ts'
const file=process.argv[2]!,revision=process.argv[3]!,receipt=JSON.parse(readFileSync(file,'utf8'))
if(!receipt.success||receipt.stdoutTruncated)throw new Error('incomplete API read')
const {summary,traces}=decodeReceipt(receipt.stdout),issues=auditSummary(summary,traces,revision),metrics=summarize([summary])
writeFileSync(file+'.audited.json',JSON.stringify({issues,metrics},null,2)+'\n')
console.log(JSON.stringify({issues,metrics:metrics.map(row=>({...row,lawDeltas:row.lawDeltas.slice(0,8)}))},null,2))
if(issues.length)process.exitCode=1
