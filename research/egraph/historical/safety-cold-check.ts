// Fresh verification only; no prover imports.
import {readFileSync} from 'node:fs'
import {countedObligations,checkMC,mcGoal,type CountCert,type Instances} from '../../../kernel/kernel.ts'
import {safetyContext,sha} from './safety-context.ts'
const c=safetyContext(),proof=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {goalSha256:string,instances:Instances,cert:CountCert}
if(proof.goalSha256!==c.goalSha256)throw Error('source goal pin')
for(const [name,terms]of Object.entries(c.metadata.instances))if(JSON.stringify(proof.instances[name]?.slice(0,terms.length))!==JSON.stringify(terms))throw Error('old instances removed')
if(JSON.stringify([proof.cert.reads,proof.cert.insts,proof.cert.picks])!==JSON.stringify([c.metadata.reads,c.metadata.insts,c.metadata.picks]))throw Error('old count metadata changed')
const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:proof.instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
const full=mcGoal(base.goal.hyps,base.decls,proof.cert);if(!full)throw Error('invalid counts')
const available=new Map<string,number>();for(const row of full.hyps){const k=JSON.stringify(row);available.set(k,(available.get(k)??0)+1)}
for(const row of c.original.hyps){const k=JSON.stringify(row),n=available.get(k)??0;if(!n)throw Error('original row dropped');available.set(k,n-1)}
const source=JSON.stringify([c.input.m,c.input.laws]);if(proof.cert.insts.some(i=>source.includes(JSON.stringify(i.wit))))throw Error('source witness collision')
const checked=checkMC(base.goal.hyps,base.decls,proof.cert)
console.log('SAFETY_COLD_CHECK',JSON.stringify({checked,goalSha256:c.goalSha256,originalRows:202,rows:full.hyps.length,proofSha256:sha(readFileSync(process.argv[2]!))}))
if(!checked)process.exitCode=1
