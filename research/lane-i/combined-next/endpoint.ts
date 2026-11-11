import {strict as assert} from 'node:assert'
import {protocols} from '../../protocols/ic3syn/models.ts'
import {proveRule} from '../../../core/dsl.ts'
import {countsDump} from '../../../core/counts.ts'
import {fullWork} from '../../../kernel/prove.ts'
import {rawWork,workKeys} from '../../../core/work-meter.ts'
const protocol=protocols.find(p=>p.id==='mldr')!,rule=protocol.make(),laws=protocol.laws(rule),W=225000000
let candidates=0,postRejection=0,uncheckedInvProposals=0
const phases:Record<string,unknown>[]=[]
countsDump.on=(event:object)=>{const e=event as {phase:string,laws?:unknown[],law?:string,proposed?:boolean,checked?:boolean,status?:string,complete?:boolean,remaining?:number};if(e.phase==='candidates')candidates=e.laws!.length;if(e.phase==='post-rejection-candidates')postRejection=e.laws!.length;if(e.phase==='count-generation-result'||e.phase==='count-rejection-result')phases.push({phase:e.phase,complete:e.complete,remaining:e.remaining});if(e.phase==='count-strategy-result'&&e.law==='inX: no quorum canVote/3'&&e.proposed===true&&e.checked===false&&e.status==='unchecked')uncheckedInvProposals++}
const before=rawWork(),start=fullWork()
Object.defineProperty(performance,'now',{configurable:true,value:()=>{throw Error('clock read in combined endpoint')}})
const verdict=proveRule(rule,laws,{search:{work:W}}),used=fullWork()-start,after=rawWork()
countsDump.on=undefined
console.log('COMBINED_ENDPOINT '+JSON.stringify({W,used,within:used<=W,candidates,postRejection,uncheckedInvProposals,phases,verdict:{proven:verdict.proven,checked:verdict.checked},flags:Object.fromEntries(Object.entries(process.env).filter(([key])=>key.startsWith('GDP_'))),raw:Object.fromEntries(workKeys.map(key=>[key,after[key]-before[key]]))}))
assert(used<=W,'combined endpoint exceeded W: '+used)
assert.equal(candidates,49);assert.equal(postRejection,47)
if(verdict.proven)assert.equal(verdict.checked,true)
