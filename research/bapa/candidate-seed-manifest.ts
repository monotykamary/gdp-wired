// Input data only. Neither capture provenance nor a lifted candidate is proof
// authority for the target machine; every kept candidate is kernel checked.
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {dirname, isAbsolute, join, resolve} from 'node:path'
import type {Law, Machine, SomeWitness} from '../../core/machine.ts'
import {ghostedMachine, type Ghosted} from '../../kernel/kernel.ts'
import {adaptCandidateSeedWitness, type WitnessSeedAudit, type WitnessSeedProposal} from './candidate-seed-witness.ts'
import {readCertificateGraph} from './proof-codec.ts'
import {restateSeeds, type SeedAudit, type SeedBindings} from './candidate-seed-restatement.ts'
import {restateCountSeeds, type CountSeedBinding, type CountSeedAudit} from './counted-seed-restatement.ts'
import {restateSumSeeds, type SumSeedAudit} from './sum-seed.ts'

export type CandidateSeedManifest = {schema:'candidate-seed-manifest/v1', protocol:string, capture:string, captureSha256:string, bindings:SeedBindings, countBindings?:Record<string,CountSeedBinding>, existentials?:string[]}
type Audit = {schema:'candidate-seed-audit/v1', protocol:string, manifestSha256:string, captureSha256:string, graphManifestSha256:string, sourceIdentity:unknown, laws:SeedAudit[], counts?:CountSeedAudit[], sums?:SumSeedAudit[], witnesses?:(WitnessSeedAudit|{status:'dropped',reason:string})[]}
export type LoadedCandidateSeeds = {kind:'usual', laws:Law[], witnesses?:Record<string,SomeWitness>, ghosts?:Pick<Ghosted,'vars'|'maps'>, audit:Audit} | {kind:'counted', laws:Law[], counts:NonNullable<Machine['counts']>, audit:Audit}
const sha=(x:Uint8Array)=>createHash('sha256').update(x).digest('hex')
const digest=(s:unknown):s is string=>typeof s==='string' && /^[a-f0-9]{64}$/.test(s)
export function loadCandidateSeedManifest(path:string, targetMachine:Machine, native:{kindLaws?:Law[],publicLaws?:Law[]} = {}):LoadedCandidateSeeds {
  const bytes=readFileSync(path), manifest=JSON.parse(bytes.toString()) as CandidateSeedManifest
  if(manifest.schema!=='candidate-seed-manifest/v1' || typeof manifest.protocol!=='string' || !manifest.protocol || typeof manifest.capture!=='string' || !digest(manifest.captureSha256) || !manifest.bindings?.maps || !manifest.bindings.domains) throw Error('invalid candidate manifest')
  const dir=isAbsolute(manifest.capture)?manifest.capture:resolve(dirname(path),manifest.capture)
  const capture=readFileSync(join(dir,'CAPTURE.json'))
  if(sha(capture)!==manifest.captureSha256)throw Error('capture custody hash mismatch')
  const header=JSON.parse(capture.toString())
  if(header.schema!=='final29-native-certificate/v1' || header.complete!==true || !['plain','inferred','witness','counted-family'].includes(header.route) || header.identity?.protocol!==manifest.protocol || !digest(header.graphManifestSha256)) throw Error('unsupported capture identity or route')
  const data=readCertificateGraph(join(dir,'graph'),header.graphManifestSha256,{maxBytes:512*1024*1024,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048},()=>{}) as any
  if(!data || data.route!==header.route || JSON.stringify(data.identity)!==JSON.stringify(header.identity) || data.verdict?.proven!==true || data.verdict?.checked!==true || data.terms?.terms?.length!==header.terms) throw Error('capture envelope mismatch')
  const baseAudit={schema:'candidate-seed-audit/v1' as const,protocol:manifest.protocol,manifestSha256:sha(bytes),captureSha256:manifest.captureSha256,graphManifestSha256:header.graphManifestSha256,sourceIdentity:header.identity}
  if(header.route==='counted-family') {
    if(manifest.existentials?.length)throw Error('counted witness proposals require a separate projection')
    const leaf=data.final
    if(!leaf?.machine || !Array.isArray(leaf.laws) || !leaf.proof?.certs)throw Error('no retained counted family')
    const countAudit=restateCountSeeds(leaf.machine.counts??{},targetMachine,manifest.bindings,manifest.countBindings??{})
    const counts=Object.fromEntries(countAudit.flatMap(a=>a.status==='candidate'?[[a.target,a.definition]]:[]))
    const producer={...targetMachine,counts:{...targetMachine.counts,...counts}}
    // A manifest cannot alias an unverified source count to a pre-existing
    // target count (or mutable map). Only newly translated definitions bind.
    const maps={...manifest.bindings.maps}
    for(const source of Object.keys(leaf.machine.counts??{})) {
      const accepted=countAudit.find(a=>a.source===source && a.status==='candidate')
      if(!accepted || accepted.status!=='candidate' || maps[source]?.target!==accepted.target) delete maps[source]
    }
    const bound={...manifest.bindings,maps}, sums=restateSumSeeds(leaf.machine,producer,bound)
    const audit=restateSeeds(leaf.laws,producer,bound,{...native,sumVariables:sums.substitutions,tupleSums:sums.tupleSums,sourceMachine:leaf.machine})
    return {kind:'counted',laws:audit.flatMap(a=>a.status==='candidate'?[a.law]:[]),counts,audit:{...baseAudit,laws:audit,counts:countAudit,sums:sums.audit}}
  }
  const todo=[data.proof], seen=new Set<object>(), leaves:any[]=[], contexts:any[]=[]
  while(todo.length) {
    const node=todo.pop()
    if(!node || typeof node!=='object')throw Error('missing producer')
    if(seen.has(node))continue
    seen.add(node)
    if(node.kind==='usual')leaves.push(node)
    else if(node.kind==='derived' && Array.isArray(node.parents) && node.parents.length){if(node.context?.kind==='skolem')contexts.push(node.context);todo.push(...node.parents)}
    else throw Error('unsupported family provenance')
  }
  if(!leaves.length || leaves.some(l=>!Array.isArray(l.laws)||!l.machine||!l.proof?.trees))throw Error('no retained usual families')
  // A union of independently restated proposals is not a union of assumptions.
  // Each leaf keeps its own machine and global candidate names remain unique.
  const audit:SeedAudit[]=[], sumAudit:SumSeedAudit[]=[]
  let witness:WitnessSeedProposal|undefined
  const witnessAudit:NonNullable<Audit['witnesses']>=[]
  if(manifest.existentials?.length) {
    try {
      if(!Array.isArray(manifest.existentials)||new Set(manifest.existentials).size!==manifest.existentials.length||manifest.existentials.some(n=>typeof n!=='string'))throw Error('invalid existential proposal selection')
      if(contexts.length!==1||leaves.length!==1)throw Error('witness proposal requires one retained Skolem producer')
      const selected=native.publicLaws?.filter(l=>manifest.existentials!.includes(l.name))??[]
      if(selected.length!==manifest.existentials.length)throw Error('native public existential laws are required')
      witness=adaptCandidateSeedWitness({...contexts[0],family:leaves[0].laws},targetMachine,selected,manifest.bindings)
      witnessAudit.push(...witness.audit)
    } catch(error) {witnessAudit.push({status:'dropped',reason:error instanceof Error?error.message:String(error)})}
  }
  for(const [sourceFamily,leaf] of leaves.entries()) {
    const producer=witness?ghostedMachine({orig:targetMachine,...witness.ghosts}):targetMachine
    const bindings=witness?.bindings??manifest.bindings
    const sums=restateSumSeeds(leaf.machine,producer,bindings)
    sumAudit.push(...sums.audit)
    for(const item of restateSeeds(witness?.laws??leaf.laws,producer,bindings,{...native,sumVariables:sums.substitutions,tupleSums:sums.tupleSums,sourceMachine:leaf.machine})) {
      const index=audit.length,base={...item,index,sourceFamily,sourceIndex:item.index}
      audit.push(item.status==='candidate'?{...base,status:'candidate',bindings:item.bindings,law:{...item.law,name:`retained:${index}:${item.source}`}}:base)
    }
  }
  return {kind:'usual',laws:audit.flatMap(a=>a.status==='candidate'?[a.law]:[]),...(witness?{witnesses:witness.witnesses,ghosts:witness.ghosts}:{}),audit:{...baseAudit,laws:audit,sums:sumAudit,...(manifest.existentials?.length?{witnesses:witnessAudit}:{})}}
}
