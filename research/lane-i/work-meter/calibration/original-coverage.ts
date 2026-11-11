import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,mkdtempSync,rmSync,appendFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync,type SpawnSyncReturns} from 'node:child_process'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
import {validatePhaseLedger,meterKeys} from './contract.ts'
const {restore,command}=await import(resolve('recovery-input/final-gate-common.ts'))
const pin='cd00524f01093838e9584edc4a20f71e2be10e2a',base='b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3'
const work=Number(process.argv[4]??15000000);assert([15000000,50000000].includes(work))
const id=process.argv[2],repetition=Number(process.argv[3]);assert(id==='consensus'||id==='consensus_epr');assert([1,2].includes(repetition))
const temp=mkdtempSync('/tmp/original-path-'),root=join(temp,'source'),weights=Object.fromEntries(meterKeys.slice(12).map(key=>[key,1])),cases=[]
try{
 restore(resolve('recovery-input'),root,base)
 const unpacked=spawnSync('git',['unpack-objects','-q'],{cwd:root,input:readFileSync('source-input/source.pack'),timeout:120000});assert.equal(unpacked.status,0)
 appendFileSync(join(root,'.git/shallow'),pin+'\n');command('git',['checkout','--detach',pin],root)
 assert.equal(command('git',['rev-parse','HEAD^{tree}'],root),'6d1453342ca15df8bf948465c13cbf9a1aedf8a2')
 command('bun',['install','--frozen-lockfile'],root,180000)
 const kit=readFileSync('calibration-input/run-mini.sh','utf8'),marker="<<'CHILD'\n",start=kit.indexOf(marker),end=kit.indexOf('\nCHILD\n',start+marker.length);assert(start>=0&&end>start)
 const child=kit.slice(start+marker.length,end);assert.equal(createHash('sha256').update(child).digest('hex'),'3cfbb94eba2160fa99b0e3e5d4010353090c1be6961a60bb7525557529c1c8ff')
 const script=join(temp,'child.ts');writeFileSync(script,child)
 const env={...Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_'))),MINI_PIN:pin}
 for(const variant of ['original','broken']){
  console.log('ORIGINAL_PATH_START '+JSON.stringify({id,variant,repetition}))
  const file=join(temp,variant+'.json.gz'),result:SpawnSyncReturns<string>=spawnSync(process.execPath,[script,root,id,variant,String(repetition),file,String(work),JSON.stringify(weights)],{encoding:'utf8',env,timeout:300000,maxBuffer:2*1024*1024})
  assert.equal(result.status,0,JSON.stringify({id,variant,repetition,error:result.error?.message,signal:result.signal,stderr:result.stderr}))
  const bytes=gunzipSync(readFileSync(file)),data=JSON.parse(bytes.toString()),audit=validatePhaseLedger(data.raw,data.events)
  assert.equal(data.source,pin);assert.deepEqual(data.weights,weights);assert.equal(data.work,work)
  if(variant==='broken')assert.notEqual(data.result.verdict,'proven')
  const row={id,variant,repetition,source:pin,weights,work:data.work,raw:data.raw,result:data.result,audit,sha256:createHash('sha256').update(bytes).digest('hex'),scope:'original input, explicit diagnostic extra weights; no calibration, W or host qualification'}
  cases.push(row);console.log('ORIGINAL_PATH_CASE '+JSON.stringify(row))
 }
 const original=cases.find(row=>row.variant==='original')!
 assert(id==='consensus_epr'?original.raw.epr>0:original.raw.fm>0||original.raw.plainRows>0,'requested production path was not observed')
 console.log('ORIGINAL_PATH_COVERAGE '+JSON.stringify({passed:true,id,repetition,source:pin,cases:cases.length}))
}finally{rmSync(temp,{recursive:true,force:true})}
