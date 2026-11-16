import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {asked,auditLiftLog} from '../axiom-audit.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
const sources=['TypedControls.lean','FullRoleControl.lean'].map(n=>readFileSync(join(out,'controls',n),'utf8'))
const logs=['typed-controls.log','full-role-control.log'].map(n=>readFileSync(join(out,n),'utf8')).join('\n')
const rows=auditLiftLog(logs,sources,sources.flatMap(asked))
writeFileSync(join(out,'CONTROLS-CHECKED.json'),JSON.stringify({status:'CONTROLS_CHECKED',theorems:rows},null,2))
console.log('independent-sort and complete-checker role-swap controls passed')
