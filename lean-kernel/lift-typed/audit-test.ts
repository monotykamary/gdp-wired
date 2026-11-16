import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {auditLiftLog} from '../axiom-audit.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
const result=auditLiftLog(readFileSync(join(out,'audit.log'),'utf8'),[readFileSync(join(out,'project/BapaProof.lean'),'utf8')],JSON.parse(readFileSync(join(out,'required.json'),'utf8')))
writeFileSync(join(out,'AUDIT.json'),JSON.stringify(result,null,2))
console.log(result.length,'required declarations checked with standard axioms only')
