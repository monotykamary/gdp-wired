// Opt-in OUTPUT provenance only. No checker, proof constructor, budget or search.
// Records are reachable only through the actual returned result object; never
// fall back to a last proof, and never treat this observation as Lean evidence.
import type {E,Machine,Law} from './machine.ts'
import type {AggregateCertificate} from './aggregate-search.ts'
import type {AggregateKinds} from './aggregate-kinds.ts'
import {snapshotKernelTermState} from '../kernel/kernel.ts'
import type {Instances,Liveness,StepLaw,Tree} from '../kernel/kernel.ts'
import type {proveLaws, proveLiveness, proveProgress, proveStepLaws} from '../kernel/prove.ts'
export type ProofOutputNode =
  | {kind:'aggregate',machine:Machine,law:Law,certificate:AggregateCertificate,kinds?:AggregateKinds,terms:E[]}
  | {kind:'counted',machine:Machine,laws:Law[],proof:{instances:Record<string,Instances>,certs:Record<string,import('../kernel/kernel.ts').CountCert>}}
  | {kind:'usual',machine:Machine,laws:Law[],proof:{instances:Record<string,Instances>,trees:Record<string,Tree>}}
  | {kind:'derived',parents:(ProofOutputNode|undefined)[],context:unknown}
export type PublicProofOutput={result:object,original:{machine:Machine,laws:Law[]},proof:ProofOutputNode|undefined}
// Synchronous public rule invocations can recursively prove a Skolem family.
let publicRuleDepth=0
export function withPublicRule<T>(run:(outermost:boolean)=>T):T {
  const outermost=publicRuleDepth++===0
  try{return run(outermost)}finally{publicRuleDepth--}
}
let observer:((event:PublicProofOutput)=>void)|undefined
let records=new WeakMap<object,ProofOutputNode>()
// Every installation/clear starts a fresh custody window, even if a callback
// function is reused. Results from a previous invocation cannot be inherited.
export const proofOutput:{on?: (event:PublicProofOutput)=>void}={
  get on(){return observer},
  set on(value){records=new WeakMap<object,ProofOutputNode>();observer=value}
}
// Step proof evidence is attached to the actual verdict, never to a last
// attempt. Translation refusal must not publish a successful model packet.
type StepProofPacket = {machine: Machine, family: Law[], step: StepLaw, report: ReturnType<typeof proveStepLaws>, kindProof?: {laws: Law[], proof: NonNullable<ReturnType<typeof proveLaws>['proof']>}}
let stepObserver: ((entry: StepProofPacket) => void) | undefined
let stepRecords = new WeakMap<object, StepProofPacket>()
export const stepProofOutput = {
  get on() { return stepObserver },
  set on(value: typeof stepObserver) { stepRecords = new WeakMap(); stepObserver = value },
}
export function retainStepProof<T extends object>(result: T, packet: StepProofPacket): T {
  if (stepObserver) stepRecords.set(result, packet)
  return result
}
export function publishStepProof<T extends {proven: boolean, checked: boolean}>(result: T, model: object): T {
  if (stepObserver && result.proven && result.checked) {
    const packet = stepRecords.get(model)
    if (packet) stepObserver(packet)
  }
  return result
}

export type LiveProofPacket = {machine: Machine, laws: Law[], liveness: Liveness, report: ReturnType<typeof proveLiveness>, progress?: ReturnType<typeof proveProgress>}
let liveObserver: ((entry: LiveProofPacket) => void) | undefined
let liveRecords = new WeakMap<object, LiveProofPacket>()
export const liveProofOutput = {
  get on() { return liveObserver },
  set on(value: typeof liveObserver) { liveRecords = new WeakMap(); liveObserver = value },
}
export function retainLiveProof<T extends object>(result: T, packet?: LiveProofPacket): T {
  if (liveObserver && packet) liveRecords.set(result, packet)
  return result
}
export function publishLiveProof<T extends {proven: boolean, checked: boolean}>(result: T, model: object): T {
  if (liveObserver && result.proven && result.checked) {
    const packet = liveRecords.get(model)
    if (packet) liveObserver(packet)
  }
  return result
}

export function retainFamily<T extends {proven:boolean,checked:boolean}>(result:T,machine:Machine,laws:Law[],proof:{instances:Record<string,Instances>,trees:Record<string,Tree>}|undefined):T {
  if(proofOutput.on&&result.proven&&result.checked&&proof)records.set(result,{kind:'usual',machine,laws,proof})
  return result
}
export function retainCounted<T extends object>(result:T,family:{proven:boolean,m:Machine,laws:Law[],proof?:{instances:Record<string,Instances>,certs:Record<string,import('../kernel/kernel.ts').CountCert>}}):T {
  if(proofOutput.on&&family.proven&&family.proof)records.set(result,{kind:'counted',machine:family.m,laws:family.laws,proof:family.proof})
  return result
}
export function retainAggregate<T extends object>(result:T,machine:Machine,law:Law,certificate:AggregateCertificate,kinds?:AggregateKinds):T {
  if (proofOutput.on) records.set(result,{kind:'aggregate',machine,law,certificate,...(kinds ? {kinds} : {}),terms:snapshotKernelTermState().terms as E[]})
  return result
}
export function retainFrom<T extends object>(result:T,parents:object[],context:unknown={kind:'projection'}):T {
  if(proofOutput.on)records.set(result,{kind:'derived',parents:parents.map(parent=>records.get(parent)),context})
  return result
}
export function publishProof<T extends object>(result:T,machine:Machine,laws:Law[]):T {
  proofOutput.on?.({result,original:{machine,laws},proof:records.get(result)})
  return result
}
