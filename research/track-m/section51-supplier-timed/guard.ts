import {readFileSync,lstatSync,readlinkSync,realpathSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join,resolve,relative} from 'node:path'
import {validateRootPlan,requireRootRaw} from './root-policy.ts'
const [operation,inputArg,targetArg]=process.argv.slice(2),input=resolve(inputArg??'.')
const json=(name:string)=>JSON.parse(readFileSync(join(input,name),'utf8'))
const sha=(name:string)=>createHash('sha256').update(readFileSync(join(input,name))).digest('hex')
function need(v:unknown,s:string):asserts v{if(!v)throw Error(s)}
const config=json('CONFIG.json')
need(config.source.commit==='4a07486a73f460a1804df60883e109ae58bb970b'&&config.source.tree==='0ae1cb165dd9ccfb7c5e9ea1d5f5d38c9549ef97','source identity')
validateRootPlan(config)
need(config.infrastructureGuard?.requestedJobTimeoutSeconds===64830&&config.infrastructureGuard.effectivePayloadGuardSeconds===64800&&config.infrastructureGuard.label==='INFRA_HANG_GUARD'&&config.infrastructureGuard.expiryVerdict===null&&config.budgets.driverSeconds===null,'external infrastructure guard contract')
for(const ref of [...config.rootBasis.evidence,...[config.rootBasis.oldRate,config.rootBasis.assumedInflation,config.rootBasis.margin].map((f:any)=>({path:f.sourcePath,sha256:f.sourceSHA256}))]){
 need(typeof ref.path==='string'&&!ref.path.startsWith('/')&&!ref.path.split('/').includes('..')&&sha(ref.path)===ref.sha256,'bound evidence hash mismatch')
}
need(config.resourceContract?.perJobMemoryEnforcement===false&&config.resourceContract.memoryRequestedMiB===28672&&config.resourceContract.requiredAffinityCpuCount===16,'placement-only resource contract')
for(const line of readFileSync(join(input,'INPUTS.sha256'),'utf8').trim().split('\n')){
 const m=/^([0-9a-f]{64})  (.+)$/.exec(line);need(m&&!m[2]!.startsWith('/')&&!m[2]!.split('/').includes('..'),'bad input index')
 need(lstatSync(join(input,m[2]!)).isFile()&&sha(m[2]!)===m[1],'input bytes mismatch: '+m[2])
}
need(sha('active-flags.json')==='a5f077dc8156a7bb550dc0ed279de96b20aa3a167c32fbaaaaad925fc9f8a272','exact profile bytes')
need(sha('source.tar')===config.sourceArchiveSHA256,'source archive digest')
need(sha('gdp-ts.tar')===config.vendors['gdp-ts'].archiveSHA256&&sha('handwired.tar')===config.vendors.handwired.archiveSHA256,'vendor archive digest')
const flags=json('active-flags.json');need(Object.keys(flags).length===22&&flags.GDP_COUNT_G1_OWNED_DEFER==='0'&&flags.GDP_COUNT_REPLAY_FORWARD==='0','exact frozen map')
if(operation==='profile'){for(const [key,value]of Object.entries(flags)){need(/^GDP_[A-Z0-9_]+$/.test(key)&&(value==='0'||value==='1'),'invalid flag');console.log(key+'='+value)}}
else if(operation==='source'){
 need(targetArg,'target absent');const target=realpathSync(targetArg)
 for(const line of readFileSync(join(input,'PROTECTED.tree'),'utf8').split('\0').filter(Boolean)){
  const m=/^(\d+) (blob|commit) ([0-9a-f]{40})\t(.+)$/.exec(line);need(m,'invalid protected tree')
  if(m[2]==='commit')continue
  const path=join(target,m[4]!);need(!relative(target,path).startsWith('..'),'escaped path')
  const data=m[1]==='120000'?Buffer.from(readlinkSync(path)):readFileSync(path)
  const actual=createHash('sha1').update('blob '+data.length+'\0').update(data).digest('hex');need(actual===m[3],'protected source mismatch: '+m[4])
 }
 console.log(JSON.stringify({protected:true,source:config.source}))
}else if(operation==='authorize'){
 const seal=json('SEAL.json'),a=json('AUTHORIZATION.json'),rootRaw=requireRootRaw(config)
 need(seal.rootRaw===rootRaw,'root not bound to seal')
 need(sha('INPUTS.sha256')===seal.inputIndexSHA256,'input index seal')
 need(a.sealSHA256===sha('SEAL.json')&&a.DGo===true&&a.MainScheduled===true,'BLOCKED: exact D GO and Main scheduling required')
 need(typeof a.DReceipt==='string'&&a.DReceipt.length>0&&typeof a.MainReceipt==='string'&&a.MainReceipt.length>0,'missing authorization references')
 if(targetArg){need(createHash('sha256').update(readFileSync(targetArg)).digest('hex')===seal.jobsSHA256,'job manifest changed')}
 console.log(JSON.stringify({authorized:true,source:config.source,sealSHA256:sha('SEAL.json')}))
}else if(operation!=='verify')throw Error('unknown guard operation')
