import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,mkdtempSync,rmSync,appendFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {validatePhaseLedger,calibrationRows,meterKeys} from './contract.ts'
const {restore,command}=await import(resolve('recovery-input/final-gate-common.ts'))
const pin='aeef60912e189573eb24e658af7e915109a971d2',base='b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3'
const repetition=Number(process.argv[2]);assert([1,2,3].includes(repetition))
const bounded=process.argv[3]==='bounded';assert(process.argv[3]===undefined||bounded)
const diagnosticWeights=bounded?Object.fromEntries(meterKeys.slice(12).map(key=>[key,1])):null
const temp=mkdtempSync('/tmp/mini-contract-'),root=join(temp,'source')
const summaries:{id:string,variant:string,repetition:number,events:number,phases:string[],epr:number,fitRows:number,signatureSha256:string}[]=[]
try{
 restore(resolve('recovery-input'),root,base)
 const unpacked=spawnSync('git',['unpack-objects','-q'],{cwd:root,input:readFileSync('strategy-input/calibration-source.pack'),timeout:120000})
 assert.equal(unpacked.status,0,unpacked.stderr.toString())
 appendFileSync(join(root,'.git/shallow'),pin+'\n')
 command('git',['checkout','--detach',pin],root)
 command('bun',['install','--frozen-lockfile'],root,180000)
 const kit=readFileSync('calibration-input/run-mini.sh','utf8'),begin="<<'CHILD'\n",start=kit.indexOf(begin),end=kit.indexOf('\nCHILD\n',start+begin.length)
 assert(start>=0&&end>start)
 const child=kit.slice(start+begin.length,end),path=join(temp,'child.ts');writeFileSync(path,child)
 const {protocols}=await import(join(root,'research/protocols/ic3syn/models.ts'))
 assert.equal(protocols.length,29)
 const meter=await import(join(root,'core/work-meter.ts')),keys=meter.workKeys
 assert.deepEqual([...meter.extraWorkKeys],[...meterKeys.slice(12)])
 assert.deepEqual([...keys],[...meterKeys])
 const env=Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_')))
 env.MINI_PIN=pin
 for(const protocol of protocols)for(const variant of ['original','broken']){
  console.log('MINI_PHASE_CASE_START '+JSON.stringify({id:protocol.id,variant,repetition}))
  const file=join(temp,protocol.id+'-'+variant+'.json.gz')
  const result=spawnSync(process.execPath,[path,root,protocol.id,variant,String(repetition),file,'100000',...(diagnosticWeights?[JSON.stringify(diagnosticWeights)]:[])],{encoding:'utf8',env,timeout:120000,maxBuffer:2*1024*1024})
  assert.equal(result.status,0,JSON.stringify({id:protocol.id,variant,repetition,signal:result.signal,error:result.error?.message,stderr:result.stderr}));assert.equal(result.signal,null)
  const data=JSON.parse(gunzipSync(readFileSync(file)).toString()),audit=validatePhaseLedger(data.raw,data.events)
  assert.equal(data.schema,'mini-calibration-raw/v1');assert.equal(data.source,pin)
  assert.equal(data.work,100000);assert.deepEqual(data.weights,diagnosticWeights);assert.equal(data.noElapsedTimeSearchDeadline,true)
  assert(!/migration pending/.test(data.result.why??''))
  if(variant==='broken')assert.notEqual(data.result.verdict,'proven')
  const rows=calibrationRows(data.raw,data.events)
  const signature={raw:data.raw,result:data.result,events:data.events.map((event:any)=>({id:event.id,parentId:event.parentId,name:event.name,depth:event.depth,completed:event.completed,raw:event.raw,exclusiveRaw:event.exclusiveRaw}))}
  summaries.push({id:protocol.id,variant,repetition,events:audit.events,phases:audit.phaseNames,epr:data.raw.epr,fitRows:rows.length,signatureSha256:createHash('sha256').update(JSON.stringify(signature)).digest('hex')})
  console.log('MINI_PHASE_CASE_COMPLETE '+JSON.stringify(summaries.at(-1)))
 }
 assert.equal(command('git',['status','--porcelain','--untracked-files=no'],root),'')
 console.log('MINI_PHASE_CONTRACT '+JSON.stringify({passed:true,source:pin,repetition,caseCount:summaries.length,kitSha256:createHash('sha256').update(kit).digest('hex'),childSha256:createHash('sha256').update(child).digest('hex'),fixtureAllowance:100000,diagnosticWeights,scope:'174-case format/phase compatibility with explicitly labeled diagnostic weights when present; NOT calibration, W, host qualification, unweighted-path equivalence or full F3',cases:summaries}))
}finally{console.log('MINI_PHASE_PARTIAL '+JSON.stringify({source:pin,repetition,caseCount:summaries.length,cases:summaries}));rmSync(temp,{recursive:true,force:true})}
