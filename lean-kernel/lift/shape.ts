import type {Machine} from '../../core/machine.ts'
import {inspectProvenance,type NativeBundle} from './proof-capture.ts'
import {proposeWitnessAlpha} from './witness-alpha.ts'
import {sourceStructure} from './source.ts'

export type GenericLiftRoute='alpha'|'counted'|'witness'

/** Dispatch on retained family/provenance and source semantics, never identity. */
export function selectGenericLiftRoute(bundle:NativeBundle):GenericLiftRoute {
  if(bundle.verdict?.proven!==true||bundle.verdict.checked!==true)throw Error('unsupported unverified capsule')
  const source=bundle.original?.machine,laws=bundle.original?.laws
  if(!source||!Array.isArray(laws)||!laws.length)throw Error('unsupported empty source')
  if(source.history||Object.keys(source.sums??{}).length||Object.keys(source.fns??{}).length)throw Error('unsupported source history/sums/functions: separate semantic transport required')
  if(bundle.schema==='bapa-family/v1'&&bundle.route==='counted-family') {
    if(!bundle.final||bundle.final.phase!=='closed-family'||bundle.final.checked!==true||!Object.keys(bundle.final.machine.counts??{}).length)throw Error('unsupported counted capsule without a complete counted family')
    if(laws.some(l=>l.some!==undefined||l.ex!==undefined||l.witness!==undefined||l.stated!==undefined||l.finite!==undefined))throw Error('unsupported counted existential/restated source: separate semantic transport required')
    return 'counted'
  }
  if(bundle.schema!=='bapa-proof/v1')throw Error('unsupported capsule schema/route')
  const found=inspectProvenance(bundle.proof)
  if(found.route!==bundle.route)throw Error('capsule route differs from retained shape')
  if(found.route==='witness'||laws.some(l=>l.some!==undefined||l.ex!==undefined||l.witness!==undefined)) {
    if(found.route!=='witness'||found.counted.length)throw Error('unsupported existential source without a retained usual witness family')
    return 'witness'
  }
  if(found.counted.length||found.usual.length!==1||!['plain','inferred'].includes(found.route))throw Error('unsupported mixed/ambiguous source family')
  if(Object.keys(source.counts??{}).length||Object.keys(found.usual[0]!.machine.counts??{}).length||laws.some(l=>l.stated!==undefined||l.finite!==undefined))throw Error('unsupported source shape: separate semantic transport required')
  return 'alpha'
}

// This syntactic preflight prevents emitting a project for unrelated machine
// transformations. The emitted QAlpha/RowAlpha proofs remain authoritative.
export function assertGenericBridgeShape(bundle:NativeBundle,route:GenericLiftRoute):void {
  if(route==='witness')return // The witness exporter checks every context and parent.
  const source=bundle.original.machine
  const producer=bundle.route==='counted-family'?bundle.final.machine:inspectProvenance(bundle.proof).usual[0]!.machine
  const normalize=(m:Machine):Machine=>JSON.parse(sourceStructure({...m,
    maps:m.maps??{},step:{...m.step,maps:m.step.maps??{}},
    ...(route==='counted'?{counts:undefined}:{})})) as Machine
  if(route==='counted')for(const [name,decl]of Object.entries(source.counts??{})) {
    if(sourceStructure(decl)!==sourceStructure(producer.counts?.[name]))throw Error('unsupported change to source count declaration: '+name)
  }
  try {proposeWitnessAlpha(normalize(source),normalize(producer))}
  catch(error){throw Error('unsupported source-to-family transformation; only exact/alpha rows and count augmentation are generic: '+String(error))}
}
