// Synthetic observer controls are not native proof evidence.
import {expect,test} from 'bun:test'
import {captureInvocation,inspectProvenance,lawCoverage,type CaptureHooks,type CaptureIdentity,type ClosedFamily,type NativeBundle} from './proof-capture.ts'
import type {Machine,Law} from '../../core/machine.ts'
import type {ProofOutputNode} from '../../core/proof-output.ts'
const identity:CaptureIdentity={protocol:'fixture',invocation:'one',sourceCommit:'a'.repeat(40),sourceTree:'b'.repeat(40),driverSha256:'c'.repeat(64),inputSha256:'d'.repeat(64),runtimeSha256:'e'.repeat(64),profileSha256:'f'.repeat(64),workBudget:'100',flags:{GDP_WORK_FULL:'1'}}
function fixture(){
 const law={name:'fixture law',holds:{op:'=',a:{op:'const',value:0},b:{op:'const',value:0}}} as Law
 const original={machine:{} as Machine,laws:[law]},verdict={proven:true,checked:true}
 const cert={reads:[],insts:[],tree:{leaf:[]}},final:ClosedFamily={phase:'closed-family',checked:true,machine:original.machine,laws:[law],proof:{instances:{},certs:{'fixture law @start':cert,'fixture law @step':cert}}}
 let quiet=true,writes=0,snapshots=0,bundle:NativeBundle|undefined
 const hooks:CaptureHooks={proofObserver:{},quiescent:()=>quiet,snapshotTerms:()=>{expect(quiet).toBe(true);snapshots++;return {terms:[],identities:[]}},write:b=>{expect(quiet).toBe(true);expect(hooks.proofObserver.on).toBeUndefined();writes++;bundle=b;return {manifestSha256:'0'.repeat(64)}}}
 const emit=(proof:ProofOutputNode={kind:'counted',machine:final.machine,laws:final.laws,proof:final.proof},result=verdict)=>hooks.proofObserver.on!({result,original,proof})
 return {original,verdict,final,hooks,emit,enter:()=>{quiet=false},exit:()=>{quiet=true},stats:()=>({writes,snapshots,bundle})}
}
test('one call, exact returned object, serialization after work exits',()=>{
 const f=fixture();let calls=0
 const result=captureInvocation(identity,()=>{expect(f.hooks.quiescent()).toBe(true);return f.original},()=>{calls++;f.enter();f.emit();expect(f.stats().snapshots).toBe(0);expect(f.stats().writes).toBe(0);f.exit();return f.verdict},f.hooks)
 expect(calls).toBe(1);expect(result.verdict).toBe(f.verdict);expect(result.retention.complete).toBe(true);expect(f.stats().snapshots).toBe(1)
 if(result.retention.complete)expect(result.retention.projection.kind).toBe('same-machine')
})
test('missing or duplicate public events and multiple counted leaves fail closed',()=>{
 for(const count of [0,2]){const f=fixture();const r=captureInvocation(identity,f.original,()=>{for(let i=0;i<count;i++)f.emit();return f.verdict},f.hooks);expect(r.retention.complete).toBe(false);expect(f.stats().writes).toBe(0)}
 const f=fixture(),leaf:ProofOutputNode={kind:'counted',machine:f.final.machine,laws:f.final.laws,proof:f.final.proof}
 const r=captureInvocation(identity,f.original,()=>{f.emit({kind:'derived',parents:[leaf,{...leaf}],context:{kind:'projection'}});return f.verdict},f.hooks)
 expect(r.retention.complete).toBe(false)
})
test('output failure preserves native result and restores observer',()=>{
 const f=fixture();f.hooks.write=()=>{throw Error('disk full')}
 const r=captureInvocation(identity,f.original,()=>{f.emit();return f.verdict},f.hooks)
 expect(r.verdict).toBe(f.verdict);expect(r.retention).toEqual({complete:false,error:'disk full'});expect(f.hooks.proofObserver.on).toBeUndefined()
})
test('native exception is not converted into output failure or retried',()=>{
 const f=fixture(),fault=Error('native stop');let seen:unknown,calls=0
 try{captureInvocation(identity,f.original,()=>{calls++;throw fault},f.hooks)}catch(e){seen=e}
 expect(seen).toBe(fault);expect(calls).toBe(1);expect(f.hooks.proofObserver.on).toBeUndefined();expect(f.stats().writes).toBe(0)
})
test('unsettled root, unproven result, missing certificate and stale result fail closed',()=>{
 for(const change of ['root','verdict','cert','stale']){const f=fixture();const r=captureInvocation(identity,f.original,()=>{if(change==='root')f.enter();if(change==='verdict')f.verdict.checked=false;if(change==='cert')delete f.final.proof.certs['fixture law @step'];f.emit(undefined,change==='stale'?{...f.verdict}:f.verdict);return f.verdict},f.hooks);expect(r.retention.complete).toBe(false);expect(f.stats().writes).toBe(0)}
})
test('foreign observer refused before any work',()=>{
 const f=fixture();f.hooks.proofObserver.on=()=>{};let calls=0
 expect(()=>captureInvocation(identity,f.original,()=>{calls++;return f.verdict},f.hooks)).toThrow('unexpected proof output observer');expect(calls).toBe(0)
})
test('law coverage is structural, not name-only; missing/cyclic producers refused',()=>{
 const f=fixture();expect(lawCoverage(f.original.laws,f.final.laws)).toEqual([0]);expect(()=>lawCoverage(f.original.laws,[{...f.original.laws[0]!,keys:['new']}])).toThrow('unchanged')
 expect(()=>inspectProvenance({kind:'derived',parents:[undefined],context:{kind:'projection'}})).toThrow('missing')
 const cycle:any={kind:'derived',parents:[],context:{kind:'projection'}};cycle.parents=[cycle];expect(()=>inspectProvenance(cycle)).toThrow('cyclic')
})
test('counted family with changed public laws is retained but unqualified',()=>{
 const f=fixture();f.final.laws=[]
 const r=captureInvocation(identity,f.original,()=>{f.emit();return f.verdict},f.hooks)
 expect(r.retention.complete).toBe(true)
 if(r.retention.complete)expect(r.retention.projection.kind).toBe('unqualified')
 expect(f.stats().bundle?.route).toBe('counted-family')
 if(f.stats().bundle?.route==='counted-family')expect((f.stats().bundle as import('./proof-capture.ts').FamilyBundle).publicLawIndices).toBeNull()
})
test('non-counted data retained, but witnesses and unrelated families never get qualified projections',()=>{
 for(const change of ['same','inference','witness','machine','law']){
  const f=fixture(),leaf:ProofOutputNode={kind:'usual',machine:change==='machine'?{unrelated:true} as unknown as Machine:f.original.machine,laws:change==='law'?[]:f.original.laws,proof:{instances:{},trees:{}}}
  const proof:ProofOutputNode={kind:'derived',parents:[leaf],context:{kind:change==='witness'?'witness':change==='inference'?'inference':'projection'}}
  const r=captureInvocation(identity,f.original,()=>{f.emit(proof);return f.verdict},f.hooks)
  expect(r.retention.complete).toBe(true)
  if(r.retention.complete)expect(r.retention.projection.kind).toBe(['same','inference'].includes(change)?'same-machine':'unqualified')
 }
})
