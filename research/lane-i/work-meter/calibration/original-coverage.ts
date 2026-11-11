import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,mkdtempSync,rmSync,appendFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync,type SpawnSyncReturns} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gunzipSync,gzipSync} from 'node:zlib'
import {validatePhaseLedger,meterKeys} from './contract.ts'
import {splitPreflight} from './split-preflight.ts'
const {restore,command}=await import(resolve('recovery-input/final-gate-common.ts'))
const pin='cd00524f01093838e9584edc4a20f71e2be10e2a',base='b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3'
const work=Number(process.argv[4]??15000000);assert([15000000,50000000].includes(work))
const phaseDiagnostic=process.argv[5]==='phases'
const id=process.argv[2],repetition=Number(process.argv[3]);assert(id==='consensus'||id==='consensus_epr');assert([1,2].includes(repetition))
const temp=mkdtempSync('/tmp/original-path-'),root=join(temp,'source'),weights=Object.fromEntries(meterKeys.slice(12).map(key=>[key,1])),cases=[]
try{
 restore(resolve('recovery-input'),root,base)
 const unpacked=spawnSync('git',['unpack-objects','-q'],{cwd:root,input:readFileSync('source-input/source.pack'),timeout:120000});assert.equal(unpacked.status,0)
 appendFileSync(join(root,'.git/shallow'),pin+'\n');command('git',['checkout','--detach',pin],root)
 assert.equal(command('git',['rev-parse','HEAD^{tree}'],root),'6d1453342ca15df8bf948465c13cbf9a1aedf8a2')
 const instrumentation=process.argv[6]==='split-small'?splitPreflight(root):undefined
 command('bun',['install','--frozen-lockfile'],root,180000)
 const kit=readFileSync('calibration-input/run-mini.sh','utf8'),marker="<<'CHILD'\n",start=kit.indexOf(marker),end=kit.indexOf('\nCHILD\n',start+marker.length);assert(start>=0&&end>start)
 let child=kit.slice(start+marker.length,end);assert.equal(createHash('sha256').update(child).digest('hex'),'3cfbb94eba2160fa99b0e3e5d4010353090c1be6961a60bb7525557529c1c8ff')
 if(instrumentation){
  const replace=(a:string,b:string)=>{assert.equal(child.split(a).length,2,'unique CHILD anchor');child=child.replace(a,b)}
  replace('const {withWorkLedger}=', 'const {withWorkLedger,workPhase}=')
  replace("const rule=variant==='broken'?protocol.make(protocol.bug):protocol.make(),laws=protocol.laws(rule)","const rule=workPhase('protocol.construct',()=>variant==='broken'?protocol.make(protocol.bug):protocol.make()),laws=workPhase('protocol.laws',()=>protocol.laws(rule))")
  replace('const v=proveRule(rule,laws,{search:{ms:work/250}})',"const v=workPhase('rule.prove',()=>proveRule(rule,laws,{search:{ms:work/250}}))")
  replace('const data={schema:', 'const data={diagnosticInstrumentation:JSON.parse(process.env.LANE_I_PHASE_META!),schema:')
 }
 const script=join(temp,'child.ts');writeFileSync(script,child)
 const env={...Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_'))),MINI_PIN:pin,LANE_I_PHASE_META:JSON.stringify(instrumentation??null)}
 for(const variant of ['original','broken']){
  console.log('ORIGINAL_PATH_START '+JSON.stringify({id,variant,repetition}))
  const file=join(temp,variant+'.json.gz'),result:SpawnSyncReturns<string>=spawnSync(process.execPath,[script,root,id,variant,String(repetition),file,String(work),JSON.stringify(weights)],{encoding:'utf8',env,timeout:300000,maxBuffer:2*1024*1024})
  assert.equal(result.status,0,JSON.stringify({id,variant,repetition,error:result.error?.message,signal:result.signal,stderr:result.stderr}))
  const bytes=gunzipSync(readFileSync(file)),data=JSON.parse(bytes.toString()),audit=validatePhaseLedger(data.raw,data.events)
  assert.equal(data.source,pin);assert.deepEqual(data.weights,weights);assert.equal(data.work,work)
  if(variant==='broken')assert.notEqual(data.result.verdict,'proven')
  const row={id,variant,repetition,source:pin,weights,work:data.work,raw:data.raw,result:data.result,audit,instrumentation,childSha256:createHash('sha256').update(child).digest('hex'),phaseEvents:data.events,receiptGzipBase64:gzipSync(bytes).toString('base64'),sha256:createHash('sha256').update(bytes).digest('hex'),scope:'original input, explicit diagnostic extra weights; no calibration, W or host qualification'}
  cases.push(row);console.log('ORIGINAL_PATH_CASE '+JSON.stringify(row))
 }
 const original=cases.find(row=>row.variant==='original')!
 if(phaseDiagnostic){console.log('ORIGINAL_PHASE_DIAGNOSTIC '+JSON.stringify({id,repetition,work,source:pin,productionPathReached:id==='consensus_epr'?original.raw.epr>0:original.raw.fm>0||original.raw.plainRows>0,coverageClaim:false}));}else assert(id==='consensus_epr'?original.raw.epr>0:original.raw.fm>0||original.raw.plainRows>0,'requested production path was not observed')
 if(!phaseDiagnostic)console.log('ORIGINAL_PATH_COVERAGE '+JSON.stringify({passed:true,id,repetition,source:pin,cases:cases.length}))
}finally{rmSync(temp,{recursive:true,force:true})}
