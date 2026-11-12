// Receipt-only arithmetic; no prover import or new computation grant.
import {WORK_KEYS,recomputeDeltas,rootOK,settledOK,stable} from './pair-checks.ts'
function need(ok:unknown,message:string):asserts ok{if(!ok)throw Error(message)}
function raw(v:any){need(v&&/^(0|[1-9]\d*)$/.test(v.numerator)&&/^[1-9]\d*$/.test(v.denominator),'invalid work rational');return {n:BigInt(v.numerator),d:BigInt(v.denominator)}}
export function checkSingle(v:any,measurement:any,config:any,weights:any){
 const deltas=recomputeDeltas(v),units=BigInt(config.rootRaw),a=raw(v.final.actual),base=raw(v.initial.rootBaseline.actual),reported=raw(measurement.totalCountedUnits)
 const total={n:a.n*base.d-base.n*a.d,d:a.d*base.d}
 const checks={
  complete:v.diagnosticComplete===true&&v.error===null&&v.phase==='returned',
  source:v.identity.sourceCommit===config.source.commit&&v.identity.sourceTree===config.source.tree,
  flags:v.identity.profileSHA256===config.profileSHA256,
  originalModel:v.modelSHA256===config.originalModelSHA256&&v.lawsSHA256===config.originalLawsSHA256,
  root:v.originalRootRaw===config.rootRaw&&v.identity.rootRaw===config.rootRaw,
  weights:stable(v.initial.weights)===stable(weights)&&stable(v.final.weights)===stable(weights),
  verdict:v.rawVerdict!==null&&v.verdict===(v.rawVerdict?.proven&&v.rawVerdict?.checked?'proven':v.rawVerdict?.run?'refuted':'unknown'),
  counters:stable(Object.keys(v.counterDeltas).sort())===stable(WORK_KEYS)&&stable(v.counterDeltas)===stable(deltas),
  accounting:rootOK(v.initial,units)&&rootOK(v.final,units)&&settledOK(v.settled)&&raw(v.final.reserved).n===0n,
  mode:v.mode==='timed'&&v.identity.mode==='timed'&&v.observerInstalled===false&&v.trace===null,
  measurement:measurement.mode==='timed'&&measurement.rootCeilingRaw===config.rootRaw&&stable(measurement.counterDeltas)===stable(deltas)&&reported.n*total.d===total.n*reported.d&&measurement.observedWallNs===v.wallNs&&measurement.wallMeaning==='OBSERVATION_ONLY'&&measurement.referenceConversion?.rhoNew===null&&measurement.qualification===false&&measurement.WClaim===false,
 }
 return {status:Object.values(checks).every(Boolean)?'VALID_TIMED_MEASUREMENT':'TIMED_MEASUREMENT_REJECTED',checks,verdict:v.verdict,totalCountedUnits:measurement.totalCountedUnits,wallNs:v.wallNs,wallMeaning:'OBSERVATION_ONLY',pairComparison:false,qualification:false,WClaim:false,rhoNew:null}
}
