// Strict single-arm receipt validation only. No prover import, job, or retry.
import {readFileSync,writeFileSync} from 'node:fs'
import {dirname,join} from 'node:path'
import {createHash} from 'node:crypto'
import {bindNativeReceipts} from './receipt-bindings.ts'
import {infrastructureStop} from './infrastructure-stop.ts'
import {stable} from './pair-checks.ts'
import {checkSingle} from './single-checks.ts'
import {requireRootRaw} from './root-policy.ts'
const [receipts,output,input]=process.argv.slice(2)
if(!receipts||!output||!input)throw Error('receipt/output/sealed-input required')
const root=dirname(receipts)
let result:any
try{
 const receiptBytes=readFileSync(receipts),native=JSON.parse(receiptBytes.toString()),config=JSON.parse(readFileSync(join(input,'CONFIG.json'),'utf8'))
 requireRootRaw(config)
 const infrastructure=infrastructureStop(native.rows,config.infrastructureGuard)
 if(infrastructure)result={schema:'s51-timed-measurement/v1',...infrastructure,receiptSHA256:createHash('sha256').update(receiptBytes).digest('hex'),qualification:false,WClaim:false}
 else{
  const dir=join(root,'mldr-3g-timed.files'),bound=bindNativeReceipts(receipts,[join(dir,'verdict.json')],['mldr-3g-timed'])
  const exportedConfig=JSON.parse(readFileSync(join(dir,'CONFIG.json'),'utf8'))
  if(stable(exportedConfig)!==stable(config))throw Error('exported CONFIG differs from sealed input')
  const measurement=JSON.parse(readFileSync(join(dir,'measurement-total.json'),'utf8')),weights=JSON.parse(readFileSync(join(input,'weights.json'),'utf8'))
  result={schema:'s51-timed-measurement/v1',...checkSingle(bound.control,measurement,config,weights),evidence:bound.evidence,measurement,perHelperAndSafety:'UNAVAILABLE: timed arm has no observer',referenceConversion:'PENDING_QUALIFIED_RHO_NEW'}
 }
}catch(e){result={schema:'s51-timed-measurement/v1',status:'INCONCLUSIVE',reason:String(e),verdict:null,qualification:false,WClaim:false}}
writeFileSync(output,JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result))
if(result.status!=='VALID_TIMED_MEASUREMENT')process.exitCode=1
