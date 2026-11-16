// Opt-in OUTPUT provenance only. No checker, proof constructor, budget or search.
// Records are reachable only through the actual returned result object; never
// fall back to a last proof, and never treat this observation as Lean evidence.
import type {Machine,Law} from './machine.ts'
import type {Instances,Tree} from '../kernel/kernel.ts'
export type ProofOutputNode =
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
export function retainFamily<T extends {proven:boolean,checked:boolean}>(result:T,machine:Machine,laws:Law[],proof:{instances:Record<string,Instances>,trees:Record<string,Tree>}|undefined):T {
  if(proofOutput.on&&result.proven&&result.checked&&proof)records.set(result,{kind:'usual',machine,laws,proof})
  return result
}
export function retainCounted<T extends object>(result:T,family:{proven:boolean,m:Machine,laws:Law[],proof?:{instances:Record<string,Instances>,certs:Record<string,import('../kernel/kernel.ts').CountCert>}}):T {
  if(proofOutput.on&&family.proven&&family.proof)records.set(result,{kind:'counted',machine:family.m,laws:family.laws,proof:family.proof})
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
