/// <reference types="node" />
// Strict, data-only import of historical final29 capsules. Keep their schema and
// identity verbatim; only the checked structural proof data is shared with lifts.
import {join} from 'node:path'
import {readCertificateGraph,type ReadLimits} from './lift/proof-codec.ts'
import {inspectProvenance,retainedLawCoverage,type ClosedFamily,type FamilyBundle,type TermPrelude,type Verdict} from './lift/proof-capture.ts'
import type {ProofOutputNode} from '../core/proof-output.ts'
import {readBoundedData,dataText,readLiftSource,sha256,sourceStructure,type GenericLiftSource} from './lift/source.ts'
import {defaultReadLimits,type GenericLiftOptions} from './lift/index.ts'

export type LegacyIdentity=Readonly<Record<string,unknown>&{
  protocol:string,invocation:string,sourceCommit:string,sourceTree:string,
  driverSha256:string,inputSha256:string,runtimeSha256:string,profileSha256:string,
  workNumerator:string,workDenominator:string,flags:Readonly<Record<string,string>>
}>
type LegacyCommon={identity:LegacyIdentity,original:FamilyBundle['original'],verdict:Verdict,terms:TermPrelude}
export type LegacyBundle=LegacyCommon&(
  {schema:'final29-family/v1',route:'counted-family',final:ClosedFamily,publicLawIndices:number[]|null}|
  {schema:'final29-proof/v1',route:'plain'|'inferred'|'witness',proof:ProofOutputNode}
)
export type LegacyCaptureManifest={
  schema:'final29-native-certificate/v1',complete:true,route:LegacyBundle['route'],identity:LegacyIdentity,
  graphManifestSha256:string,terms:number,publicLawIndices?:number[]|null,familyLaws?:number,certificateKeys?:string[]
}
export type LegacyLiftInput={
  format:'legacy',manifest:LegacyCaptureManifest,bundle:LegacyBundle,metadata:[object,unknown][],
  source:GenericLiftSource,sourceSha256:string,capsuleSha256:string
}
const object=(v:unknown):v is Record<string,unknown>=>!!v&&typeof v==='object'&&!Array.isArray(v)
const hash=(v:unknown)=>typeof v==='string'&&/^[0-9a-f]{64}$/.test(v)
const same=(a:unknown,b:unknown)=>sourceStructure(a)===sourceStructure(b)
function identity(value:unknown):asserts value is LegacyIdentity {
  if(!object(value))throw Error('invalid historical capture identity')
  for(const key of ['protocol','invocation'])if(typeof value[key]!=='string'||!value[key])throw Error('missing historical identity '+key)
  for(const key of ['sourceCommit','sourceTree'])if(typeof value[key]!=='string'||! /^[0-9a-f]{40}$/.test(value[key]))throw Error('invalid historical identity '+key)
  for(const key of ['driverSha256','inputSha256','runtimeSha256','profileSha256'])if(!hash(value[key]))throw Error('invalid historical identity '+key)
  if(typeof value.workNumerator!=='string'||!/^(0|[1-9][0-9]*)$/.test(value.workNumerator)||typeof value.workDenominator!=='string'||! /^[1-9][0-9]*$/.test(value.workDenominator))throw Error('invalid historical work fraction')
  if(!object(value.flags)||Object.values(value.flags).some(v=>typeof v!=='string'))throw Error('invalid historical flag closure')
  sourceStructure(value)
}
export function validateLegacyManifest(value:unknown):LegacyCaptureManifest {
  if(!object(value)||value.schema!=='final29-native-certificate/v1'||value.complete!==true||!['counted-family','plain','inferred','witness'].includes(String(value.route)))throw Error('incomplete or unsupported historical capsule')
  identity(value.identity)
  if(!hash(value.graphManifestSha256)||!Number.isSafeInteger(value.terms)||Number(value.terms)<0)throw Error('invalid historical graph or term binding')
  return value as LegacyCaptureManifest
}
/** Does not restore terms, execute source, search, or reinterpret the schema. */
export function validateLegacyEnvelope(manifest:LegacyCaptureManifest,value:unknown):LegacyBundle {
  if(!object(value)||value.route!==manifest.route||!same(value.identity,manifest.identity)||!object(value.verdict)||value.verdict.proven!==true||value.verdict.checked!==true)throw Error('historical capture envelope mismatch')
  if(!object(value.terms)||!Array.isArray(value.terms.terms)||!Array.isArray(value.terms.identities)||value.terms.terms.length!==manifest.terms||value.terms.identities.length!==manifest.terms)throw Error('historical term table mismatch')
  const ids=new Set<string>()
  for(const [i,pair]of value.terms.identities.entries()){
    if(!Array.isArray(pair)||pair.length!==2||typeof pair[0]!=='string'||pair[1]!==i||ids.has(pair[0]))throw Error('noncanonical historical term identities')
    ids.add(pair[0])
  }
  if(!object(value.original)||!object(value.original.machine)||!Array.isArray(value.original.laws)||!value.original.laws.length)throw Error('missing historical public source')
  sourceStructure(value.original)
  if(manifest.route==='counted-family'){
    if(value.schema!=='final29-family/v1'||!object(value.final)||value.final.phase!=='closed-family'||value.final.checked!==true||!object(value.final.machine)||!Array.isArray(value.final.laws)||!value.final.laws.length||!object(value.final.proof)||!object(value.final.proof.certs)||!object(value.final.proof.instances))throw Error('incomplete historical counted family')
    const bundle=value as unknown as Extract<LegacyBundle,{route:'counted-family'}>,f=bundle.final
    if(f.laws.length!==manifest.familyLaws||!Array.isArray(manifest.certificateKeys)||!same(Object.keys(f.proof.certs),manifest.certificateKeys))throw Error('historical family manifest mismatch')
    if(f.laws.some(l=>!l||typeof l.name!=='string'||!l.name)||new Set(f.laws.map(l=>l.name)).size!==f.laws.length)throw Error('ambiguous historical law family')
    const expected=f.laws.flatMap(l=>[l.name+' @start',l.name+' @step'])
    if(expected.length!==manifest.certificateKeys.length||expected.some(k=>!Object.hasOwn(f.proof.certs,k)))throw Error('incomplete historical primary obligations')
    if(!Object.hasOwn(manifest,'publicLawIndices')||!Object.hasOwn(value,'publicLawIndices')||!same(value.publicLawIndices,manifest.publicLawIndices)||!same(retainedLawCoverage(bundle.original.laws,f.laws),manifest.publicLawIndices))throw Error('historical public law coverage mismatch')
    return bundle
  }
  if(value.schema!=='final29-proof/v1'||!object(value.proof))throw Error('missing historical proof provenance')
  const bundle=value as unknown as Extract<LegacyBundle,{schema:'final29-proof/v1'}>
  if(inspectProvenance(bundle.proof).route!==manifest.route)throw Error('historical provenance route mismatch')
  return bundle
}
export function readLegacyLiftInput(capsuleDirectory:string,sourceFile:string,options:GenericLiftOptions={}):LegacyLiftInput {
  const bytes=readBoundedData(join(capsuleDirectory,'CAPTURE.json'),1024*1024),capsuleSha256=sha256(bytes)
  if(options.expectedManifestSha256!==undefined&&options.expectedManifestSha256!==capsuleSha256)throw Error('capture manifest binding mismatch')
  const manifest=validateLegacyManifest(JSON.parse(dataText(bytes))),metadata:[object,unknown][]=[]
  const limits:ReadLimits={...defaultReadLimits,...options.limits}
  const raw=readCertificateGraph(join(capsuleDirectory,'graph'),manifest.graphManifestSha256,limits,(o,m)=>metadata.push([o,m]))
  const bundle=validateLegacyEnvelope(manifest,raw),{source,sourceSha256}=readLiftSource(sourceFile,options.maxSourceBytes)
  return {format:'legacy',manifest,bundle,metadata,source,sourceSha256,capsuleSha256}
}
