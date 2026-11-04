// Independent start verification; no prover imported.
import {readFileSync} from 'node:fs'
import {checkMC,type CountCert} from '../../../kernel/kernel.ts'
import {frozenStart,sha} from './start-context.ts'
const bytes=readFileSync(process.argv[2]!),p=JSON.parse(bytes.toString()) as {id:string,inputSha256:string,goalSha256:string,instances:Record<string,unknown>,cert:CountCert},c=frozenStart(p.id)
if(p.inputSha256!==c.inputSha256||p.goalSha256!==c.goalSha256||Object.keys(p.instances).length||p.cert.reads.length||p.cert.insts.length||p.cert.picks?.length)throw Error('start context altered')
const checked=checkMC(c.base.goal.hyps,c.base.decls,p.cert)
console.log('START_COLD',JSON.stringify({id:p.id,goalSha256:c.goalSha256,checked,proofSha256:sha(bytes),noProverInvoked:true}));if(!checked)process.exitCode=1
