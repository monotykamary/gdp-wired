// Receipt-only conversion after qualified rho_new exists. Never changes a budget.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {referenceSeconds} from './measurement-rows.ts'
const [measurementFile,rateFile,sourceReceipt,output]=process.argv.slice(2)
if(!measurementFile||!rateFile||!sourceReceipt||!output)throw Error('measurement, qualified rate envelope, source receipt and output required')
const rate=JSON.parse(readFileSync(rateFile,'utf8'))
if(rate.schema!=='mldr-qualified-reference-rate/v1'||rate.qualified!==true||rate.status!=='QUALIFIED_RHO_NEW'||!rate.reviewReference)throw Error('qualified rho_new envelope required, never the planning assumption')
const sha=(b:Uint8Array)=>createHash('sha256').update(b).digest('hex')
if(rate.sourceSHA256!==sha(readFileSync(sourceReceipt)))throw Error('calibration receipt hash mismatch')
const source=readFileSync(measurementFile),report=JSON.parse(source.toString())
const unitKeys=new Set(['totalCountedUnits','countedUnits','attributedCountedUnits','sharedOrUnattributedUnits','firstCheckedAtRootUnits','rootStartUnits','rootEndUnits','rootUnits','atRootUnits'])
function converted(value:any):any{
 if(Array.isArray(value))return value.map(converted)
 if(!value||typeof value!=='object')return value
 const out:any={}
 for(const [key,item]of Object.entries(value)){
  out[key]=converted(item)
  if(unitKeys.has(key)&&item&&typeof item==='object'&&'numerator'in item&&'denominator'in item)out[key+'ReferenceSeconds']=referenceSeconds(item as any,rate.rhoNew)
 }
 return out
}
writeFileSync(output,JSON.stringify({schema:'mldr-measurement-reference-conversion/v1',sourceSHA256:sha(source),rateEnvelopeSHA256:sha(readFileSync(rateFile)),calibrationSourceSHA256:rate.sourceSHA256,reviewReference:rate.reviewReference,rhoNew:rate.rhoNew,report:converted(report),qualification:false,WClaim:false,budgetUnchanged:true},null,2)+'\n')
