// Research-only packet construction. A substitution is a proposal until the
// ordinary fresh-process native replay checks every goal of the joint family.
import {type Law,type Machine} from '../../../core/machine.ts'
import {type Instances} from '../../../kernel/kernel.ts'
import {type CountStrategyProof} from '../../../core/count-strategy.ts'
import {prepareCountStrategyMachine} from '../../../core/count-strategies.ts'
import {clock} from '../../../kernel/prove.ts'
import {type PortableCountCert,captureCountCert} from './portable-count-cert.ts'
export type ClosedFamily={machine:Machine,family:Law[],proof:{instances:Record<string,Instances>,certs:Record<string,PortableCountCert>}}
const stable=(value:unknown):string=>JSON.stringify(value,(_key,v)=>v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v)
const withoutCounts=(m:Machine)=>{const {counts:_counts,...rest}=m;return rest}
export function bindClosedFamily(original:Machine,candidates:Law[],closed:ClosedFamily):Law[]{
 if(!closed.family.length||new Set(closed.family.map(law=>law.name)).size!==closed.family.length)throw Error('invalid closed family')
 if(stable(withoutCounts(original))!==stable(withoutCounts(closed.machine)))throw Error('original machine semantics changed')
 if(Object.entries(original.counts??{}).some(([name,body])=>stable(body)!==stable(closed.machine.counts?.[name])))throw Error('original count changed')
 const bound=closed.family.map(law=>{const source=candidates.find(candidate=>candidate.name===law.name);if(!source||stable(source)!==stable(law))throw Error('law not from original admission: '+law.name);return source})
 const prepared=prepareCountStrategyMachine(original,closed.family,clock()+2000)
 if(stable(prepared)!==stable(closed.machine))throw Error('prepared machine does not match the closed family')
 const names=closed.family.flatMap(law=>[law.name+' @start',law.name+' @step'])
 if(Object.keys(closed.proof.certs).length!==names.length||names.some(name=>!Object.hasOwn(closed.proof.certs,name)))throw Error('incomplete closed family')
 return bound
}
export function substituteClosedFamily(closed:ClosedFamily,law:Law,proof:CountStrategyProof):ClosedFamily{
 if(proof.status||!closed.family.some(original=>stable(original)===stable(law)))throw Error('unverified or foreign replacement')
 const names=[law.name+' @start',law.name+' @step']
 if(Object.keys(proof.certs).length!==2||names.some(name=>!proof.certs[name]||!closed.proof.certs[name]))throw Error('replacement must cover exactly INIT and STEP')
 const certs=Object.fromEntries(names.map(name=>[name,captureCountCert(proof.certs[name]!)]))
 return {...closed,proof:{...closed.proof,instances:{...closed.proof.instances,[law.name]:proof.instances},certs:{...closed.proof.certs,...certs}}}
}
