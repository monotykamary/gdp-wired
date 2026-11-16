/// <reference types="node" />
// One data-only lift pipeline. Emission is not source acceptance: native Lean
// must check the emitted source correspondence and all requested axioms.
import {join} from 'node:path'
import {generateGenericLift,readLiftInput,restoreTermPrelude,writeLiftProject,defaultPartOptions,type GenericLiftManifest,type GenericLiftOptions} from './lift/index.ts'
import {readBoundedData,dataText,sourceStructure,sourceLeanId,sha256} from './lift/source.ts'
import {readLegacyLiftInput,type LegacyIdentity,type LegacyLiftInput} from './lift-legacy.ts'
import {tryEmitBoundInclusion,type BoundInclusionOutput} from './lift-special/index.ts'
import {tryTypedBoundSubstitution,type TypedBoundEmission} from './lift-typed/index.ts'
import {tryRadixSimulation,type RadixSimulationOutput} from './lift-simulation/index.ts'
import {asked} from './axiom-audit.ts'
import {applyLiftTheoremNames,type LiftAliases} from './lift-names.ts'
import type {LiftInput} from './lift/index.ts'

export {emitGenericLift} from './lift/index.ts'
export type {GenericLiftManifest,GenericLiftOptions,GenericLiftSource} from './lift/index.ts'
export {auditLiftLog} from './axiom-audit.ts'
export type LiftManifest=Omit<GenericLiftManifest,'identity'|'sourceProjection'|'parts'>&{
  capsuleSchema:'bapa-native-certificate/v1'|'final29-native-certificate/v1'
  identity:GenericLiftManifest['identity']|LegacyIdentity
  sourceProjection:Omit<GenericLiftManifest['sourceProjection'],'kind'>&{kind:GenericLiftManifest['sourceProjection']['kind']|'bound-inclusion'|'typed-bound-substitution'|'radix-simulation'}
  parts?:GenericLiftManifest['parts']|BoundInclusionOutput['parts']
  transport?:{kind:'bound-inclusion'|'typed-bound-substitution',bound:number}|{kind:'radix-simulation',radix:number,layouts:{map:string,arity:number}[]}
  theoremAliases?:LiftAliases
}
type PreparedLift=({format:'native'}&LiftInput)|LegacyLiftInput
type SpecialResult=BoundInclusionOutput|(TypedBoundEmission&{kind:'typed-bound-substitution'})|RadixSimulationOutput
function readInput(capsule:string,source:string,options:GenericLiftOptions):PreparedLift {
  const outer:unknown=JSON.parse(dataText(readBoundedData(join(capsule,'CAPTURE.json'),1024*1024)))
  if(!outer||typeof outer!=='object'||!('schema'in outer))throw Error('invalid capsule envelope')
  if(outer.schema==='bapa-native-certificate/v1')return {format:'native',...readLiftInput(capsule,source,options)}
  if(outer.schema==='final29-native-certificate/v1')return readLegacyLiftInput(capsule,source,options)
  throw Error('unsupported capsule schema')
}
function specialManifest(input:PreparedLift,result:SpecialResult,options:GenericLiftOptions):LiftManifest {
  const root=result.project['BapaProof.lean']
  if(typeof root!=='string'||result.sourceTheorems.length!==input.source.laws.length||!result.sourceTheorems.length||new Set(result.sourceTheorems).size!==result.sourceTheorems.length)throw Error('incomplete generated source theorem coverage')
  const present=asked(root)
  if(new Set(present).size!==present.length)throw Error('duplicate generated root axiom request')
  const requiredTheorems=[...new Set([result.familyTheorem,...result.sourceTheorems,...result.requiredTheorems,...present])]
  for(const name of requiredTheorems)if(!/^[A-Za-z_][A-Za-z0-9_.']*$/.test(name))throw Error('invalid generated theorem name')
  // Imported modules do not replay #print commands from their .olean files.
  // Ask in the root for every required family, source and auxiliary theorem.
  result.project['BapaProof.lean']=root+'\n'+requiredTheorems.filter(n=>!present.includes(n)).map(n=>'#print axioms '+n).join('\n')+'\n'
  const limits={...defaultPartOptions,...options.parts},files=Object.entries(result.project)
  for(const value of [limits.maxFiles,limits.maxOutputBytes])if(!Number.isSafeInteger(value)||value<1)throw Error('finite positive output limits required')
  if(files.length>limits.maxFiles||files.reduce((n,[,text])=>n+Buffer.byteLength(text),0)>limits.maxOutputBytes)throw Error('complete project output limit exceeded')
  const transport:NonNullable<LiftManifest['transport']>=result.kind==='radix-simulation'
    ?{kind:result.kind,radix:result.plan.radix,layouts:result.plan.layouts}
    :{kind:result.kind,bound:result.kind==='bound-inclusion'?result.bound:result.roles.bound}
  return {schema:'gdp-lift-emission/v1',status:'EMITTED_NOT_CHECKED',inputSha256:input.capsuleSha256,capsuleSha256:input.capsuleSha256,sourceSha256:input.sourceSha256,sourceId:input.source.id,capsuleSchema:input.manifest.schema,identity:input.manifest.identity,route:input.bundle.route,
    projection:{kind:'unqualified',reason:'source correspondence requires the generated Lean transport'},familyTheorem:result.familyTheorem,requiredTheorems,files:Object.fromEntries(files.map(([name,text])=>[name,sha256(text)])),
    sourceProjection:{kind:result.kind,status:'EMITTED_NOT_CHECKED',sourceTheorems:result.sourceTheorems,publicLawNames:input.source.laws.map(l=>l.name),publicLawIndices:result.publicLawIndices},...('parts'in result?{parts:result.parts}:{}),transport,leanVersion:'4.34.0',leanExecuted:false,allSizesProven:false,publicSourceAcceptance:'REQUIRES_LEAN_SOURCE_PROJECTION_CHECK'}
}
function finish(input:PreparedLift,project:Record<string,string>,manifest:LiftManifest,output:string,options:GenericLiftOptions):LiftManifest {
  const named=applyLiftTheoremNames(project,manifest,input.source.theorems),limits={...defaultPartOptions,...options.parts}
  for(const value of [limits.maxFiles,limits.maxOutputBytes])if(!Number.isSafeInteger(value)||value<1)throw Error('finite positive output limits required')
  if(Object.keys(project).length>limits.maxFiles||Object.values(project).reduce((n,text)=>n+Buffer.byteLength(text),0)>limits.maxOutputBytes)throw Error('complete named project output limit exceeded')
  writeLiftProject(output,project,named)
  return named
}
/** One fresh process, one validated input, one term restoration. Candidate
 * rejection is final; a failed transport never falls back to another strategy. */
export function lift(capsuleDirectory:string,sourceFile:string,outputDirectory:string,options:GenericLiftOptions={}):LiftManifest {
  const input=readInput(capsuleDirectory,sourceFile,options)
  restoreTermPrelude(input.bundle.terms,input.metadata)
  if(input.format==='native'&&sourceStructure({machine:input.source.machine,laws:input.source.laws})===sourceStructure(input.bundle.original)){
    const generated=generateGenericLift(input,options),manifest:LiftManifest={...generated.manifest,capsuleSchema:input.manifest.schema}
    return finish(input,generated.project,manifest,outputDirectory,options)
  }
  if('final'in input.bundle){
    const result=tryEmitBoundInclusion({id:sourceLeanId(input.source.id),bundle:input.bundle,providedSourceAST:input.source,options:{...defaultPartOptions,...options.parts}})
    if(result){const manifest=specialManifest(input,result,options);return finish(input,result.project,manifest,outputDirectory,options)}
  }
  // Route labels are validated against the retained provenance graph. They
  // describe proof shapes, not protocol identities. A recognized failure is
  // terminal; it is never caught and tried as a different transformation.
  if('proof'in input.bundle){
    const common={id:sourceLeanId(input.source.id),bundle:input.bundle,providedSourceAST:input.source,options:{...defaultPartOptions,...options.parts}}
    if(input.bundle.route==='witness'){
      const result=tryTypedBoundSubstitution(common)
      if(result){const tagged={...result,kind:'typed-bound-substitution' as const};return finish(input,result.project,specialManifest(input,tagged,options),outputDirectory,options)}
    }else{
      const result=tryRadixSimulation(common)
      if(result)return finish(input,result.project,specialManifest(input,result,options),outputDirectory,options)
    }
  }
  throw Error('unsupported source/capsule transport shape; no source acceptance')
}
