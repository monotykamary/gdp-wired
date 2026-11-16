/// <reference types="node" />
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {liftProject as leanProject} from './project.ts'
import {asked} from '../axiom-audit.ts'
import {readFamilyCapsule,type ReadLimits,type CaptureManifest} from './proof-codec.ts'
import type {NativeBundle,CaptureIdentity,Projection} from './proof-capture.ts'
import {restoreTermPrelude} from './proof-prelude.ts'
import {emitAlphaSource} from './source-projection.ts'
import {exportWitnessSource,type WitnessPathReceipt,type WitnessAlphaReceipt} from './proof-witness.ts'
import {countedSourceProject} from './proof-counted-source.ts'
import type {PartOptions} from './proof-parts.ts'
import {readBoundedData,readLiftSource,assertSourceMatches,sha256,sourceLeanId,type GenericLiftSource} from './source.ts'
import {selectGenericLiftRoute,assertGenericBridgeShape,type GenericLiftRoute} from './shape.ts'

export type {GenericLiftSource} from './source.ts'
export {readLiftSource,assertSourceMatches} from './source.ts'
export {selectGenericLiftRoute} from './shape.ts'
export {restoreTermPrelude} from './proof-prelude.ts'
export type {GenericLiftRoute} from './shape.ts'
export type {ReadLimits} from './proof-codec.ts'
export type {PartOptions} from './proof-parts.ts'
export type GenericLiftOptions={
  /** Pin CAPTURE.json to an independently retained hash, when available. */
  expectedManifestSha256?:string
  limits?:Partial<ReadLimits>
  parts?:Partial<PartOptions>
  maxSourceBytes?:number
}
export type GenericLiftManifest={
  schema:'gdp-lift-emission/v1'
  status:'EMITTED_NOT_CHECKED'
  inputSha256:string
  capsuleSha256:string
  sourceSha256:string
  sourceId:string
  identity:CaptureIdentity
  route:NativeBundle['route']
  projection:Projection
  familyTheorem:string
  requiredTheorems:string[]
  files:Record<string,string>
  sourceProjection:{kind:GenericLiftRoute,status:'EMITTED_NOT_CHECKED',sourceTheorems:string[],publicLawNames:string[],publicLawIndices?:number[],parentPaths?:WitnessPathReceipt[],alphaTransports?:WitnessAlphaReceipt[]}
  parts?:ReturnType<typeof countedSourceProject>['parts']
  leanVersion:'4.34.0'
  leanExecuted:false
  allSizesProven:false
  publicSourceAcceptance:'REQUIRES_LEAN_SOURCE_PROJECTION_CHECK'
}
export const defaultReadLimits:Readonly<ReadLimits>=Object.freeze({maxBytes:512*1024*1024,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048})
export const defaultPartOptions:Readonly<PartOptions>=Object.freeze({weightLimit:1000000n,maxOutputBytes:256*1024*1024,maxFiles:20000,heartbeats:200000000,recursionDepth:100000})

export type LiftInput={manifest:CaptureManifest,bundle:NativeBundle,metadata:[object,unknown][],source:GenericLiftSource,sourceSha256:string,capsuleSha256:string}

/** Data and integrity only: no source equality assertion or term restoration. */
export function readLiftInput(capsuleDirectory:string,sourceFile:string,options:GenericLiftOptions={}):LiftInput {
  const {source,sourceSha256}=readLiftSource(sourceFile,options.maxSourceBytes)
  const capsuleSha256=sha256(readBoundedData(join(capsuleDirectory,'CAPTURE.json'),1024*1024))
  const expected=options.expectedManifestSha256??capsuleSha256
  if(expected!==capsuleSha256)throw Error('capture manifest binding mismatch')
  const metadata:[object,unknown][]=[]
  const {manifest,data}=readFamilyCapsule(capsuleDirectory,expected,{...defaultReadLimits,...options.limits},(o,m)=>metadata.push([o,m]))
  return {manifest,bundle:data as NativeBundle,metadata,source,sourceSha256,capsuleSha256}
}

/**
 * Data-only retained-certificate export. Run once in a fresh process: term
 * restoration is deliberately single-use, even on failure. No proof search,
 * protocol registry, source evaluation, Lean invocation or checked receipt.
 * Covers the 24 generic shapes (10 alpha, 9 counted, 5 witness), not the three
 * separately qualified special transports.
 */
export function emitGenericLift(capsuleDirectory:string,sourceFile:string,outputDirectory:string,options:GenericLiftOptions={}):GenericLiftManifest {
  const input=readLiftInput(capsuleDirectory,sourceFile,options)
  assertSourceMatches(input.source,input.bundle)
  selectGenericLiftRoute(input.bundle)
  restoreTermPrelude(input.bundle.terms,input.metadata)
  const generated=generateGenericLift(input,options)
  writeLiftProject(outputDirectory,generated.project,generated.manifest)
  return generated.manifest
}

export type GenericLiftProject={project:Record<string,string>,manifest:GenericLiftManifest}
/** After exactly one term restoration by the caller; never reads, restores, or writes. */
export function generateGenericLift(input:LiftInput,options:GenericLiftOptions={}):GenericLiftProject {
  const {source,sourceSha256,capsuleSha256,manifest,bundle}=input
  assertSourceMatches(source,bundle)
  const kind=selectGenericLiftRoute(bundle)
  assertGenericBridgeShape(bundle,kind)
  const id=sourceLeanId(source.id),familyTheorem=id+'_laws'
  let project:Record<string,string>,sourceTheorems:string[],publicLawIndices:number[]|undefined
  let parentPaths:WitnessPathReceipt[]|undefined,alphaTransports:WitnessAlphaReceipt[]|undefined,parts:GenericLiftManifest['parts']
  if(kind==='counted') {
    const emitted=countedSourceProject(id,bundle,{...defaultPartOptions,...options.parts})
    project=emitted.project;sourceTheorems=emitted.sourceTheorems;publicLawIndices=emitted.publicLawIndices;parts=emitted.parts
  } else {
    let body:string
    if(kind==='witness'){
      const emitted=exportWitnessSource(bundle,id)
      body=emitted.body+'\n'+emitted.publicBridge
      sourceTheorems=emitted.sourceTheorems.map(t=>t.name)
      publicLawIndices=emitted.publicLawIndices;parentPaths=emitted.parentPaths;alphaTransports=emitted.alphaTransports
    } else {
      body=emitAlphaSource(id,bundle)
      sourceTheorems=bundle.original.laws.map((_,j)=>id+'_source_law'+j+'_holds')
    }
    const printed=[familyTheorem,...sourceTheorems,...(parentPaths??[]).flatMap(p=>[p.familyTheorem,...p.sourceTheorems]),...(kind==='alpha'?[id+'_source_laws',id+'_alpha_valid',id+'_row_valid',id+'_alpha_result']:[]),...(alphaTransports??[]).flatMap(a=>a.theorems)]
    const bodyRequests=new Set(asked(body))
    const text='import QAlpha\nimport Ghost\nimport GhostMap\nopen Kern Cert\nset_option maxHeartbeats 200000000\nset_option maxRecDepth 100000\n'+body+'\n'+[...new Set(printed)].filter(t=>!bodyRequests.has(t)).map(t=>'#print axioms '+t).join('\n')+'\n'
    project=leanProject(text,{name:'BapaProof'})
  }
  if(!sourceTheorems.length||sourceTheorems.length!==source.laws.length)throw Error('incomplete public source theorem coverage')
  // Check generated code, not library comments (which can discuss axioms).
  for(const [name,text]of Object.entries(project))if(name.endsWith('.lean')&&!['lakefile.lean'].includes(name)&&(/^(?:bapa_|BapaProof)/.test(name))&&/\b(?:sorry|axiom|native_decide)\b/.test(text))throw Error('unapproved generated Lean construct')
  const requiredTheorems=[...new Set([familyTheorem,...sourceTheorems,...[...project['BapaProof.lean']!.matchAll(/^#print axioms ([A-Za-z_][A-Za-z0-9_'.]*)\s*$/gm)].map(m=>m[1]!)])]
  const maxOutputBytes=options.parts?.maxOutputBytes??defaultPartOptions.maxOutputBytes,maxFiles=options.parts?.maxFiles??defaultPartOptions.maxFiles
  for(const v of [maxOutputBytes,maxFiles])if(!Number.isSafeInteger(v)||v<1)throw Error('finite positive output limits required')
  if(Object.keys(project).length>maxFiles||Object.values(project).reduce((n,s)=>n+Buffer.byteLength(s),0)>maxOutputBytes)throw Error('complete project output limit exceeded')
  const files=Object.fromEntries(Object.entries(project).map(([name,text])=>[name,sha256(text)]))
  const receipt:GenericLiftManifest={schema:'gdp-lift-emission/v1',status:'EMITTED_NOT_CHECKED',inputSha256:capsuleSha256,capsuleSha256,sourceSha256,sourceId:source.id,identity:manifest.identity,route:bundle.route,projection:manifest.projection,familyTheorem,requiredTheorems,files,
    sourceProjection:{kind,status:'EMITTED_NOT_CHECKED',sourceTheorems,publicLawNames:source.laws.map(l=>l.name),...(publicLawIndices?{publicLawIndices}:{}),...(parentPaths?{parentPaths}:{}),...(alphaTransports?.length?{alphaTransports}:{})},...(parts?{parts}:{}),leanVersion:'4.34.0',leanExecuted:false,allSizesProven:false,publicSourceAcceptance:'REQUIRES_LEAN_SOURCE_PROJECTION_CHECK'}
  return {project,manifest:receipt}
}

export type LiftEmissionRecord={schema:'gdp-lift-emission/v1',status:'EMITTED_NOT_CHECKED',files:Record<string,string>}

/** Commit emission files only, never a checked receipt. Accepts specialized transports. */
export function writeLiftProject(outputDirectory:string,project:Record<string,string>,receipt:LiftEmissionRecord):void {
  if(receipt.schema!=='gdp-lift-emission/v1'||receipt.status!=='EMITTED_NOT_CHECKED'||('leanExecuted'in receipt&&receipt.leanExecuted!==false)||('allSizesProven'in receipt&&receipt.allSizesProven!==false))throw Error('only unchecked emission receipts may be written')
  if(Object.keys(receipt.files).sort().join('\n')!==Object.keys(project).sort().join('\n'))throw Error('project file manifest mismatch')
  for(const [name,text]of Object.entries(project)){
    if(!/^[A-Za-z0-9_.-]+$/.test(name)||name==='.'||name==='..'||name==='EMITTED.json')throw Error('unsafe generated project filename')
    if(receipt.files[name]!==sha256(text))throw Error('project file hash mismatch: '+name)
  }
  // New directory and exclusive file creation: never overwrite earlier evidence.
  mkdirSync(outputDirectory,{recursive:false})
  for(const [name,text]of Object.entries(project)){
    writeFileSync(join(outputDirectory,name),text,{flag:'wx'})
  }
  writeFileSync(join(outputDirectory,'EMITTED.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx'})
}
