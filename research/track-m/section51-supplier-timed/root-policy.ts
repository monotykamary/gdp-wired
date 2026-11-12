// Measurement planning only. No production imports and no verdict authority.
export const REFERENCE_SECONDS=7200
export const ACCEPTANCE_REFERENCE_SECONDS=600
function need(v:unknown,s:string):asserts v{if(!v)throw Error(s)}
export function positiveRaw(value:unknown):bigint{
 need(typeof value==='string'&&/^[1-9]\d*$/.test(value),'invalid positive raw amount')
 return BigInt(value)
}
export function estimatedRootRaw(rate:{numerator:unknown,denominator:unknown}):string{
 const n=positiveRaw(rate.numerator)*BigInt(REFERENCE_SECONDS),d=positiveRaw(rate.denominator)
 return String((n+d-1n)/d)
}
export function boundRate(b:any):{numerator:string,denominator:string}{
 let n=1n,d=1n
 for(const factor of [b.oldRate,b.assumedInflation,b.margin]){
  need(factor&&typeof factor.sourcePath==='string'&&factor.sourcePath.length>0&&!factor.sourcePath.startsWith('/')&&!factor.sourcePath.split('/').includes('..')&&/^[0-9a-f]{64}$/.test(factor.sourceSHA256),'missing bound factor source')
  n*=positiveRaw(factor.numerator);d*=positiveRaw(factor.denominator)
 }
 need(b.oldRate.assumed===true&&b.assumedInflation.assumed===true&&b.basisType==='PLANNING_ASSUMPTION'&&b.boundProven===false&&b.acceptedCalibration===false&&b.margin.numerator==='2'&&b.margin.denominator==='1','measurement margin must be exactly two')
 const gcd=(a:bigint,c:bigint):bigint=>c===0n?a:gcd(c,a%c),g=gcd(n,d)
 return {numerator:String(n/g),denominator:String(d/g)}
}
export function validateRootPlan(config:any,_allowPending=false):string{
 const b=config.rootBasis
 need(b?.status==='MEASUREMENT_CEILING'&&b.label==='PLANNING_ASSUMPTION_NOMINAL_2H'&&b.referenceSeconds===REFERENCE_SECONDS&&b.acceptanceReferenceSeconds===ACCEPTANCE_REFERENCE_SECONDS&&b.estimated===true&&b.frozenCalibration===false&&b.verdictAuthority===false&&b.rhoNew===null,'invalid measurement-only ceiling policy')
 const rate=boundRate(b)
 need(b.upperUnitsPerReferenceSecond?.numerator===rate.numerator&&b.upperUnitsPerReferenceSecond?.denominator===rate.denominator,'upper rate differs from cited product')
 const rootRaw=estimatedRootRaw(rate)
 need(config.rootRaw===rootRaw,'root differs from ceil(7200 * assumed old rho * assumed inflation * 2)')
 return rootRaw
}
export const requireRootRaw=(config:any):string=>validateRootPlan(config)
