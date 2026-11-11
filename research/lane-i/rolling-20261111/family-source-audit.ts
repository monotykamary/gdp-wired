// Compare the saved proof's machine and laws with fresh original admission.
// No proof search, added axiom, or mutation of the original rules is allowed.
import {readFileSync} from 'node:fs'
import {alphaEqual} from './alpha-source.ts'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {protocols} from '../../protocols/ic3syn/models.ts'
import {countsDump,guardLaws} from '../../../core/counts.ts'
import {proveRule} from '../../../core/dsl.ts'
import {type Law,type Machine} from '../../../core/machine.ts'
import {discoverLiftedCountGuard} from '../../../core/count-lifted-shape.ts'
import {prepareCountStrategyMachine} from '../../../core/count-strategies.ts'
import {clock,counted,fullRate,withWall} from '../../../kernel/prove.ts'
const file=process.argv[2];if(!file)throw Error('expected gzip proof artifact')
const text=gunzipSync(readFileSync(file)).toString().trim(),data=JSON.parse(text) as {machine:Machine,family:Law[]}
const withoutCounts=(m:Machine)=>{const {counts:_counts,...rest}=m;return rest}
let captured=0
for(const protocol of protocols){
 const rule=protocol.make(),seed=guardLaws(rule.machine),extended={...rule.machine,counts:{...rule.machine.counts,...seed.counts}}
 if(!seed.laws.some(law=>discoverLiftedCountGuard(extended,law,seed.laws)))continue
 const previous=countsDump.on,stop={}
 countsDump.on=(event:object)=>{
  const value=event as {phase?:string,machine:Machine,laws:Law[]};if(value.phase!=='candidates')return
  withWall(performance.now()+30000,()=>counted(fullRate,()=>{
   if(!alphaEqual(withoutCounts(value.machine),withoutCounts(data.machine)))throw Error('original non-count machine semantics changed')
   if(Object.entries(value.machine.counts??{}).some(([name,body])=>!alphaEqual(body,data.machine.counts?.[name],'count')))throw Error('original count definition changed')
   for(const law of data.family){const original=value.laws.find(candidate=>candidate.name===law.name);if(!original||!alphaEqual(original,law,'law'))throw Error('law not from original generated admission: '+law.name)}
   const prepared=prepareCountStrategyMachine(value.machine,data.family,clock()+2000)
   if(!alphaEqual(prepared,data.machine,'machine'))throw Error('prepared machine does not match saved artifact')
   console.log('CLOSED_FAMILY_SOURCE_AUDIT '+JSON.stringify({checked:true,originalLawCount:value.laws.length,retainedLaws:data.family.length,nonCountMachineAlphaEqual:true,originalCountsAlphaEqual:true,preparedMachineAlphaEqual:true,sha256:createHash('sha256').update(text).digest('hex')}))
  },true))
  captured++;throw stop
 }
 try{proveRule(rule,protocol.laws(rule),{search:{ms:60000}})}catch(error){if(error!==stop)throw error}finally{countsDump.on=previous}
}
if(captured!==1)throw Error('missing original admission')
