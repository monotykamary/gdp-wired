// Final-invocation retention only. Never calls a checker, constructor of goals,
// prover, exporter, or allocator. The observer retains references, nothing else.
import type {Machine, Law, C, E} from '../../core/machine.ts'
import type {CountCert, Instances} from '../../kernel/kernel.ts'
import type {PublicProofOutput,ProofOutputNode} from '../../core/proof-output.ts'

export type FamilyProof = {instances: Record<string, Instances>, certs: Record<string, CountCert>}
export type ClosedFamily = {phase: 'closed-family', checked: true, machine: Machine, laws: Law[], proof: FamilyProof}
export type TermPrelude = {terms: (E | C)[], identities: [string, number][]}
export type Verdict = {proven: boolean, checked: boolean}
// BAPA rerun identity, not an assertion that this is a historical final29 run.
export type CaptureIdentity = Readonly<{
  protocol: string, invocation: string,
  sourceCommit: string, sourceTree: string,
  driverSha256: string, inputSha256: string, runtimeSha256: string, profileSha256: string,
  workBudget: string, flags: Readonly<Record<string, string>>
}>
export type Projection = {kind:'same-machine', publicLawIndices:number[]} | {kind:'unqualified', reason:string}
export type FamilyBundle = {
  schema: 'bapa-family/v1', route: 'counted-family', identity: CaptureIdentity,
  original: {machine: Machine, laws: Law[]}, final: ClosedFamily,
  verdict: Verdict, terms: TermPrelude, publicLawIndices: number[] | null, projection: Projection
}
export type ProvenanceBundle = {
  schema:'bapa-proof/v1', route:'plain'|'inferred'|'witness', identity:CaptureIdentity,
  original:FamilyBundle['original'], verdict:Verdict, terms:TermPrelude, proof:ProofOutputNode, projection:Projection
}
export type NativeBundle = FamilyBundle | ProvenanceBundle
export type OriginalInput = FamilyBundle['original'] | {laws:Law[]}
export type CaptureHooks = {
  proofObserver: {on?: (event:PublicProofOutput)=>void},
  quiescent: () => boolean,
  nativeSucceeded?: () => boolean,
  snapshotTerms: () => TermPrelude,
  write: (bundle: NativeBundle) => {manifestSha256: string}
}

// Structural identity of the public law AST, not a name-only coverage claim.
// This is output-phase validation, and deliberately does not call termId.
function ast(value: unknown, active = new Set<object>()): string {
  if (value === undefined) return 'u'
  if (value === null) return 'null'
  if (typeof value === 'string' || typeof value === 'boolean') return JSON.stringify(value)
  if (typeof value === 'number') { const b = Buffer.alloc(8); b.writeDoubleBE(value); return `n:${b.toString('hex')}` }
  if (typeof value !== 'object' || active.has(value)) throw Error('unsupported or cyclic law AST')
  const p = Object.getPrototypeOf(value)
  if (p !== Object.prototype && p !== null && p !== Array.prototype) throw Error('unsupported law AST prototype')
  active.add(value)
  try {
    if (Array.isArray(value)) {
      for (let i=0;i<value.length;i++) if (!Object.hasOwn(value,i)) throw Error('sparse law AST')
      return '[' + value.map(v=>ast(v,active)).join(',') + ']'
    }
    return '{' + Reflect.ownKeys(value).map(key=>{
      if (typeof key !== 'string') throw Error('symbol law AST')
      const d=Object.getOwnPropertyDescriptor(value,key)!
      if (!('value' in d)) throw Error('accessor law AST')
      return [key,d.value] as const
    }).sort(([a],[b])=>a<b?-1:a>b?1:0).map(([key,v])=>JSON.stringify(key)+':'+ast(v,active)).join(',') + '}'
  } finally { active.delete(value) }
}
export function retainedLawCoverage(original:Law[],final:Law[]):number[]|null {
  try{return lawCoverage(original,final)}catch{return null}
}
export function lawCoverage(original: Law[], final: Law[]): number[] {
  const names = new Set<string>()
  for (const law of final) {
    if (names.has(law.name)) throw Error('duplicate final law name')
    names.add(law.name)
  }
  const seen = new Set<string>()
  return original.map(law=>{
    if (seen.has(law.name)) throw Error('duplicate public law name')
    seen.add(law.name)
    const i=final.findIndex(candidate=>candidate.name===law.name)
    if (i<0 || ast(final[i])!==ast(law)) throw Error(`public law is not present unchanged: ${law.name}`)
    return i
  })
}
function validIdentity(x: CaptureIdentity): void {
  for (const key of ['protocol','invocation'] as const)
    if (!x[key] || typeof x[key] !== 'string') throw Error(`missing capture identity: ${key}`)
  for (const key of ['sourceCommit','sourceTree'] as const)
    if (!/^[0-9a-f]{40}$/.test(x[key])) throw Error(`invalid capture identity: ${key}`)
  for (const key of ['driverSha256','inputSha256','runtimeSha256','profileSha256'] as const)
    if (!/^[0-9a-f]{64}$/.test(x[key])) throw Error(`invalid capture identity: ${key}`)
  if (!/^[1-9][0-9]*$/.test(x.workBudget)) throw Error('invalid work budget')
  if (!x.flags || Object.values(x.flags).some(v=>typeof v!=='string')) throw Error('invalid flag closure')
}

export function inspectProvenance(root:ProofOutputNode):{route:'plain'|'inferred'|'witness'|'counted-family',counted:Extract<ProofOutputNode,{kind:'counted'}>[],usual:Extract<ProofOutputNode,{kind:'usual'}>[]} {
  const visited=new Set<ProofOutputNode>(),active=new Set<ProofOutputNode>(),stack:[ProofOutputNode,boolean][]=[[root,false]],counted:Extract<ProofOutputNode,{kind:'counted'}>[]=[]
  const usual:Extract<ProofOutputNode,{kind:'usual'}>[]=[]
  let inferred=false,witness=false
  while(stack.length) {
    const [node,exit]=stack.pop()!
    if(!node||typeof node!=='object')throw Error('missing producer provenance')
    if(exit){active.delete(node);visited.add(node);continue}
    if(active.has(node))throw Error('cyclic producer provenance')
    if(visited.has(node))continue
    active.add(node);stack.push([node,true])
    if(node.kind==='derived') {
      const kind=(node.context as {kind?:unknown})?.kind
      if(!['projection','inference','witness','skolem','some-key'].includes(String(kind)))throw Error('unsupported derivation context')
      inferred ||= kind==='inference';witness ||= ['witness','skolem','some-key'].includes(String(kind))
      if(!node.parents.length)throw Error('derivation without a producer')
      for(const parent of node.parents){if(!parent)throw Error('missing producer link');stack.push([parent,false])}
    } else if(node.kind==='usual'||node.kind==='counted') {
      if(!node.machine||!Array.isArray(node.laws)||!node.proof?.instances)throw Error('incomplete producer family')
      if(node.kind==='counted'){if(!node.proof.certs)throw Error('missing counted certificates');counted.push(node)}
      else {if(!node.proof.trees)throw Error('missing usual trees');usual.push(node)}
    } else throw Error('unsupported proof producer')
  }
  if(!usual.length&&!counted.length)throw Error('no complete producer family')
  return {route:witness?'witness':inferred?'inferred':counted.length&&!usual.length?'counted-family':'plain',counted,usual}
}

// This is deliberately a narrow structural source projection, not a new prover.
// Keep other complete data for later checked bridges, but never qualify it here.
export function qualifyProjection(original:FamilyBundle['original'], machine:Machine, laws:Law[]):Projection {
  try {
    if(ast(original.machine)!==ast(machine))return {kind:'unqualified',reason:'producer machine differs from public machine'}
    return {kind:'same-machine',publicLawIndices:lawCoverage(original.laws,laws)}
  } catch(error) {return {kind:'unqualified',reason:error instanceof Error?error.message:String(error)}}
}
export function projectionOf(bundle:NativeBundle):Projection {
  if(bundle.route==='counted-family')return qualifyProjection(bundle.original,bundle.final.machine,bundle.final.laws)
  const found=inspectProvenance(bundle.proof)
  if(found.route==='witness')return {kind:'unqualified',reason:'witness source projection requires a checked bridge'}
  if(found.usual.length!==1||found.counted.length)return {kind:'unqualified',reason:'no unique usual family'}
  return qualifyProjection(bundle.original,found.usual[0]!.machine,found.usual[0]!.laws)
}

export function captureInvocation<T extends Verdict>(
  identity: CaptureIdentity, original: OriginalInput | (()=>OriginalInput), invoke: () => T, hooks: CaptureHooks
): {verdict:T, retention:{complete:true,manifestSha256:string,projection:Projection}|{complete:false,error:string}} {
  validIdentity(identity)
  if (!hooks.quiescent()) throw Error('capture must start outside every work endpoint')
  if (hooks.proofObserver.on !== undefined) throw Error('unexpected proof output observer')
  let replaced=false, publicResult:PublicProofOutput|undefined, events=0
  const proofObserver=(event:PublicProofOutput)=>{publicResult=event;events++}
  hooks.proofObserver.on=proofObserver
  let verdict:T
  try {verdict=invoke()} finally {
    replaced=hooks.proofObserver.on!==proofObserver
    hooks.proofObserver.on=undefined
  }
  try {
    if(!hooks.quiescent())throw Error('output attempted before the work root exited')
    if(!verdict||typeof verdict!=='object'||'then'in verdict)throw Error('native invocation must return synchronously')
    if(verdict.proven!==true||verdict.checked!==true||hooks.nativeSucceeded&&!hooks.nativeSucceeded())throw Error('native invocation did not return proven and checked')
    if(replaced||events!==1)throw Error('missing, replaced or ambiguous public output observer')
    // Snapshot before all validation/traversal, outside the completed work root.
    const terms=hooks.snapshotTerms(), supplied=typeof original==='function'?original():original
    const input='machine'in supplied?supplied:publicResult?{machine:publicResult.original.machine,laws:supplied.laws}:undefined
    if(!input||publicResult?.result!==verdict||publicResult.original.machine!==input.machine||publicResult.original.laws!==input.laws)throw Error('no exact final public-result provenance')
    const provenance=publicResult.proof
    if(!provenance)throw Error('no final family: refusing a stale or reconstructed proof')
    const inspected=inspectProvenance(provenance)
    let bundle:NativeBundle
    if(inspected.route==='counted-family') {
      if(inspected.counted.length!==1)throw Error('ambiguous counted producer family')
      const leaf=inspected.counted[0]!
      const final:ClosedFamily={phase:'closed-family',checked:true,machine:leaf.machine,laws:leaf.laws,proof:leaf.proof}
      for(const law of final.laws)for(const suffix of [' @start',' @step'])if(!Object.hasOwn(final.proof.certs,law.name+suffix))throw Error('missing family certificate: '+law.name+suffix)
      const publicLawIndices=retainedLawCoverage(input.laws,final.laws)
      bundle={schema:'bapa-family/v1',route:'counted-family',identity,original:input,final,verdict,terms,publicLawIndices,projection:qualifyProjection(input,final.machine,final.laws)}
    } else {
      bundle={schema:'bapa-proof/v1',route:inspected.route,identity,original:input,verdict,terms,proof:provenance,projection:{kind:'unqualified',reason:'not yet inspected'}}
      bundle.projection=projectionOf(bundle)
    }
    const receipt=hooks.write(bundle)
    return {verdict,retention:{complete:true,manifestSha256:receipt.manifestSha256,projection:bundle.projection}}
  } catch(error) {
    return {verdict,retention:{complete:false,error:error instanceof Error?error.message:String(error)}}
  }
}
