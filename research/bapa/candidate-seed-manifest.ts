// Input data only. Neither capture provenance nor a lifted candidate is proof
// authority for the target machine; every kept candidate is kernel checked.
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {dirname, isAbsolute, join, resolve} from 'node:path'
import type {Law, Machine} from '../../core/machine.ts'
import {readCertificateGraph} from './proof-codec.ts'
import {restateSeeds, type SeedAudit, type SeedBindings} from './candidate-seed-restatement.ts'

export type CandidateSeedManifest = {schema:'candidate-seed-manifest/v1', protocol:string, capture:string, captureSha256:string, bindings:SeedBindings}
export type LoadedCandidateSeeds = {laws:Law[], audit:{schema:'candidate-seed-audit/v1', protocol:string, manifestSha256:string, captureSha256:string, graphManifestSha256:string, sourceIdentity:unknown, laws:SeedAudit[]}}
const sha=(x:Uint8Array)=>createHash('sha256').update(x).digest('hex')
const digest=(s:unknown):s is string=>typeof s==='string' && /^[a-f0-9]{64}$/.test(s)
export function loadCandidateSeedManifest(path:string, targetMachine:Machine):LoadedCandidateSeeds {
  const bytes=readFileSync(path), manifest=JSON.parse(bytes.toString()) as CandidateSeedManifest
  if(manifest.schema!=='candidate-seed-manifest/v1' || typeof manifest.protocol!=='string' || !manifest.protocol || typeof manifest.capture!=='string' || !digest(manifest.captureSha256) || !manifest.bindings?.maps || !manifest.bindings.domains) throw Error('invalid candidate manifest')
  const dir=isAbsolute(manifest.capture)?manifest.capture:resolve(dirname(path),manifest.capture)
  const capture=readFileSync(join(dir,'CAPTURE.json'))
  if(sha(capture)!==manifest.captureSha256)throw Error('capture custody hash mismatch')
  const header=JSON.parse(capture.toString())
  if(header.schema!=='final29-native-certificate/v1' || header.complete!==true || !['plain','inferred','witness'].includes(header.route) || header.identity?.protocol!==manifest.protocol || !digest(header.graphManifestSha256)) throw Error('unsupported capture identity or route')
  const data=readCertificateGraph(join(dir,'graph'),header.graphManifestSha256,{maxBytes:512*1024*1024,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048},()=>{}) as any
  if(!data || data.route!==header.route || JSON.stringify(data.identity)!==JSON.stringify(header.identity) || data.verdict?.proven!==true || data.verdict?.checked!==true || data.terms?.terms?.length!==header.terms) throw Error('capture envelope mismatch')
  const todo=[data.proof], seen=new Set<object>(), leaves:any[]=[]
  while(todo.length) {
    const node=todo.pop()
    if(!node || typeof node!=='object')throw Error('missing producer')
    if(seen.has(node))continue
    seen.add(node)
    if(node.kind==='usual')leaves.push(node)
    else if(node.kind==='derived' && Array.isArray(node.parents) && node.parents.length)todo.push(...node.parents)
    else throw Error('unsupported family provenance')
  }
  if(leaves.length!==1 || !Array.isArray(leaves[0].laws) || !leaves[0].machine || !leaves[0].proof?.trees)throw Error('no unique retained usual family')
  const audit=restateSeeds(leaves[0].laws,targetMachine,manifest.bindings)
  return {laws:audit.flatMap(a=>a.status==='candidate'?[a.law]:[]),audit:{schema:'candidate-seed-audit/v1',protocol:manifest.protocol,manifestSha256:sha(bytes),captureSha256:manifest.captureSha256,graphManifestSha256:header.graphManifestSha256,sourceIdentity:header.identity,laws:audit}}
}
