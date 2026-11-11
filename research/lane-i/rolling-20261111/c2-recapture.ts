// A separate research candidate, NOT relaxed bindClosedFamily admission.
// The runner must replay all packets, the whole fresh family and mutations
// in a fresh process before this proposal can become its NEW fixture.
import {gzipSync} from 'node:zlib'
import {type Law,type Machine} from '../../../core/machine.ts'
import {prepareCountStrategyMachine} from '../../../core/count-strategies.ts'
import {clock} from '../../../kernel/prove.ts'
import {type ClosedFamily} from './c2-closed-family.ts'
import {alphaStepKey,alphaCountKey,sameAlphaCounts} from './c2-alpha-audit.ts'
const stable=(value:unknown):string=>JSON.stringify(value,(_key,v)=>v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v)
const withoutStepAndCounts=(machine:Machine)=>{const {counts:_counts,step:_step,...rest}=machine;return rest}
export function proposeRecapturedFamily(original:Machine,candidates:Law[],closed:ClosedFamily):ClosedFamily{
 if(!closed.family.length||new Set(candidates.map(law=>law.name)).size!==candidates.length||new Set(closed.family.map(law=>law.name)).size!==closed.family.length)throw Error('ambiguous or empty recapture family')
 const family=closed.family.map(law=>{const source=candidates.find(candidate=>candidate.name===law.name);if(!source)throw Error('missing freshly admitted law: '+law.name);return source})
 const prepared=prepareCountStrategyMachine(original,family,clock()+2000)
 const pair={original,family,prepared,captured:closed.machine,capturedFamily:closed.family}
 console.log('C2_ALPHA_PAIR_GZIP_BASE64 '+gzipSync(Buffer.from(JSON.stringify(pair))).toString('base64'))
 const outsideStepExact=stable(withoutStepAndCounts(original))===stable(withoutStepAndCounts(closed.machine))
 const entireStepAlpha=alphaStepKey(original.step)===alphaStepKey(closed.machine.step)
 const freshLawsExact=family.every((law,index)=>stable(law)===stable(closed.family[index]))
 const originalCountsAlpha=Object.entries(original.counts??{}).every(([name,body])=>Object.hasOwn(closed.machine.counts??{},name)&&alphaCountKey(body)===alphaCountKey(closed.machine.counts![name]))
 const derivedCountsAlpha=sameAlphaCounts(prepared.counts??{},closed.machine.counts??{})
 const report={outsideStepExact,entireStepAlpha,freshLawsExact,originalCountsAlpha,derivedCountsAlpha,laws:family.length,counts:Object.keys(prepared.counts??{}).length,scope:'C.all + step.maps.MapUpdate.each/value only',countDeclarationBinders:'literal',strictBinderUnchanged:true,nativeChecked:false,leanClearance:false}
 console.log('C2_ALPHA_AUDIT '+JSON.stringify(report))
 if(!outsideStepExact||!entireStepAlpha||!freshLawsExact||!originalCountsAlpha||!derivedCountsAlpha)throw Error('recapture alpha audit refused')
 const names=family.flatMap(law=>[law.name+' @start',law.name+' @step'])
 if(Object.keys(closed.proof.certs).length!==names.length||names.some(name=>!Object.hasOwn(closed.proof.certs,name)))throw Error('incomplete recapture certificates')
 // OLD certificates remain untrusted proposals. No rename or smaller view.
 return {machine:prepared,family,proof:closed.proof}
}
