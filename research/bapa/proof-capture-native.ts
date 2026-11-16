// Attach this wrapper around the ONE existing public proveRule invocation.
// It neither creates a work root nor invokes the public call itself a second time.
import {workLedger} from '../../core/work-admission.ts'
import {completeWorkProfile} from '../../core/work-profile.ts'
import {snapshotKernelTermState,snapshotKernelTermMemo} from '../../kernel/kernel.ts'
import {snapshotProofClock} from '../../kernel/prove.ts'
import {proofOutput} from '../../core/proof-output.ts'
import {captureInvocation,type CaptureIdentity,type OriginalInput,type Verdict} from './proof-capture.ts'
import {writeFamilyCapsule} from './proof-codec.ts'

export function captureFinalInvocation<T extends Verdict>(directory:string,identity:CaptureIdentity,original:OriginalInput|(()=>OriginalInput),invoke:()=>T,nativeSucceeded:()=>boolean=()=>true) {
  if(!completeWorkProfile.enabled)throw Error('final capture requires the full-work profile')
  const relevant=(k:string)=>k.startsWith('GDP_')||k.startsWith('BUN_JSC_')||k.startsWith('JSC_')
  const actual=Object.fromEntries(Object.entries(process.env).filter(([k,v])=>relevant(k)&&v!==undefined))
  const expected=Object.fromEntries(Object.entries(identity.flags).filter(([k])=>relevant(k)))
  const keys=Object.keys(actual).sort(),wanted=Object.keys(expected).sort()
  if(JSON.stringify(keys)!==JSON.stringify(wanted)||keys.some(k=>actual[k]!==expected[k]))throw Error('capture flags differ from frozen identity')
  return captureInvocation(identity,original,invoke,{
    proofObserver:proofOutput,nativeSucceeded,
    quiescent:()=>{
      const clock=snapshotProofClock()
      return !workLedger.bounded()&&clock.rate===0&&clock.budgetUnitsEnd===undefined
    },
    snapshotTerms:snapshotKernelTermState,
    write:bundle=>writeFamilyCapsule(directory,bundle,object=>{
      const termId=snapshotKernelTermMemo(object)
      return termId===undefined?undefined:{termId}
    })
  })
}
