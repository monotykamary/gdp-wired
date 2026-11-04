// Cold check only: no prover imports or calls.
import {readFileSync} from 'node:fs'
import {checkMC,mcGoal,type CountCert} from '../../../kernel/kernel.ts'
import {p3Context,sha} from './p3-context.ts'
const c=p3Context(),proof=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {cert:CountCert,goalSha256:string}
if(proof.goalSha256!==c.goalSha256)throw Error('proof source pin')
const rebuilt=mcGoal(c.base.goal.hyps,c.base.decls,proof.cert)
if(!rebuilt||JSON.stringify(rebuilt.hyps.slice(0,c.original.hyps.length))!==JSON.stringify(c.original.hyps))throw Error('original context not retained')
const source=JSON.stringify([c.input.m,c.input.laws])
if(proof.cert.insts.some(i=>source.includes(JSON.stringify(i.wit))))throw Error('source witness collision')
const checked=checkMC(c.base.goal.hyps,c.base.decls,proof.cert)
console.log('P3_COLD_CHECK',JSON.stringify({checked,originalGoalSha256:c.goalSha256,proofSha256:sha(readFileSync(process.argv[2]!)),originalRows:c.original.hyps.length,rows:rebuilt.hyps.length}))
if(!checked)process.exitCode=1
