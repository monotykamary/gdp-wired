// Fresh-process ordinary kernel check of the exact conditional STEP proof.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {termColumn,countedObligations,checkMC} from '../../../kernel/kernel.ts'
const bytes=readFileSync(process.argv[2]!),p=JSON.parse(gunzipSync(bytes).toString())
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column identity changed')
const packets=countedObligations(p.m,p.laws,{[p.laws[p.index].name]:p.proof.instances},p.index).filter(({goal})=>goal.name.endsWith('@step'))
const checked=packets.length===1&&packets.every(({goal,decls})=>!!p.proof.certs[goal.name]&&checkMC(goal.hyps,decls,p.proof.certs[goal.name]))
console.log('UPPER_VERIFY '+JSON.stringify({checked,sha256:createHash('sha256').update(bytes).digest('hex'),conditional:p.meta.conditional}))
if(!checked)process.exitCode=1
