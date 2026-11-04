// Cold counted-certificate verification; does not import a prover.
import {readFileSync} from 'node:fs'
import {countedObligations,checkMC,mcGoal,type CountCert,type Instances} from '../../../kernel/kernel.ts'
import {safetyContext,sha} from './safety-context.ts'
import {directSafety,originalFocusInstances} from './safety-direct-context.ts'
const c=safetyContext(),proof=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {goalSha256:string,directEnabled:boolean,instances:Instances,cert:CountCert}
const focus=originalFocusInstances(c),expected=proof.directEnabled?directSafety(c,focus):{...c.metadata,instances:focus}
if(proof.goalSha256!==c.goalSha256||JSON.stringify(proof.instances)!==JSON.stringify(expected.instances)||JSON.stringify([proof.cert.reads,proof.cert.insts,proof.cert.picks])!==JSON.stringify([expected.reads,expected.insts,expected.picks]))throw Error('schema/preservation mismatch')
const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:proof.instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
const goal=mcGoal(base.goal.hyps,base.decls,proof.cert);if(!goal)throw Error('counts')
const available=new Map<string,number>();for(const row of goal.hyps){const k=JSON.stringify(row);available.set(k,(available.get(k)??0)+1)}
for(const row of c.original.hyps){const k=JSON.stringify(row),n=available.get(k)??0;if(!n)throw Error('old row lost');available.set(k,n-1)}
if(proof.cert.insts.some(i=>JSON.stringify([c.input.m,c.input.laws]).includes(JSON.stringify(i.wit))))throw Error('witness freshness')
const checked=checkMC(base.goal.hyps,base.decls,proof.cert)
console.log('SAFETY_COLD_CHECK',JSON.stringify({checked,originalRows:202,rows:goal.hyps.length,goalSha256:c.goalSha256,proofSha256:sha(readFileSync(process.argv[2]!))}));if(!checked)process.exitCode=1
