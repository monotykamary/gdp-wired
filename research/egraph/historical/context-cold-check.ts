// Independent context reconstruction only; no prover imports.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {E,Law,Machine} from '../../../core/machine.ts'
import {countedObligations,mcGoal,type Instances,type CountInst,type MapRead,type Goal} from '../../../kernel/kernel.ts'
const sha=(b:Buffer|string)=>createHash('sha256').update(b).digest('hex')
if(sha(readFileSync('kernel/kernel.ts'))!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('kernel pin')
const packet=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {name:string,goalSha256:string,metadata:{instances:Instances,reads:MapRead[],insts:CountInst[],picks:[string,E[]][]}}
const expected:Record<string,string>={'one-value-decided':'58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca','decision-quorum':'a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357'}
if(packet.goalSha256!==expected[packet.name])throw Error('unknown context')
const input=JSON.parse(gunzipSync(readFileSync(`research/egraph/historical/inputs/m2/${packet.name}.json.gz`)).toString()) as {m:Machine,laws:Law[],law:Law,failure:{goal:Goal}}
if(sha(JSON.stringify(input.failure.goal))!==packet.goalSha256)throw Error('source goal pin')
const base=countedObligations(input.m,input.laws,{[input.law.name]:packet.metadata.instances},input.laws.findIndex(l=>l.name===input.law.name)).find(x=>x.goal.name.endsWith('@step'))
if(!base)throw Error('missing base')
const goal=mcGoal(base.goal.hyps,base.decls,packet.metadata);if(!goal)throw Error('invalid metadata')
goal.name=input.failure.goal.name
if(sha(JSON.stringify(goal))!==packet.goalSha256)throw Error('not exact original context')
console.log('COLD_CONTEXT',JSON.stringify({name:packet.name,matched:true,goalSha256:packet.goalSha256,rows:goal.hyps.length,proofChecked:false}))
