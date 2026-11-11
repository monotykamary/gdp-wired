// Standalone production admission-prefix capture. No rejection/proof is run.
// Identity capture is not an accepted benchmark until its manifest is frozen.
import {createHash} from 'node:crypto'
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {performance} from 'node:perf_hooks'
import {type Law,type Machine} from '../../../core/machine.ts'
const flags={GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0',GDP_COUNT_FRAMES:'1',GDP_COUNT_REJECTIONS:'1',GDP_COUNT_STRATEGIES:'1',GDP_COUNT_TIERS:'1',GDP_REQUEST_QUOTIENT:'1',GDP_COUNT_ROW_DEFER_CHECKS:'1'} as const
for(const [key,value]of Object.entries(flags))if(process.env[key]!==value)throw Error('wrong generation flag: '+key)
for(const key of Object.keys(process.env))if(key.startsWith('GDP_')&&!Object.hasOwn(flags,key))throw Error('unexpected generation flag: '+key)
const sourcePin=process.env.GENERATION_SOURCE_PIN
if(!sourcePin||!/^[a-f0-9]{40}$/.test(sourcePin))throw Error('exact GENERATION_SOURCE_PIN required')
const args=process.argv.slice(2),option=(name:string)=>{const i=args.indexOf(name);return i<0?undefined:args[i+1]}
const output=option('--out'),expectedPath=option('--expect'),capture=args.includes('--capture')
if(!output||capture===!!expectedPath)throw Error('use --out PATH and exactly one of --capture or --expect FILE')
const expected=expectedPath?JSON.parse(readFileSync(expectedPath,'utf8')) as {sourcePin:string,work:number,count:number,rawSha256:string,orderedAlphaSha256:string}:undefined
const work=225_000_000
if(expected&&(expected.sourcePin!==sourcePin||expected.work!==work||expected.count!==49))throw Error('wrong frozen identity contract')
// Import only after the complete import-time profile has been checked.
const {countsDump}=await import('../../../core/counts.ts')
const {proveRule}=await import('../../../core/dsl.ts')
const {protocols}=await import('../../protocols/ic3syn/models.ts')
const {queryHook}=await import('../../../kernel/prove.ts')
const {rawWork,workKeys}=await import('../../../core/work-meter.ts')
const {strategyLawKey}=await import('../../../core/strategy-premises.ts')
const model=protocols.find(p=>p.id==='mldr')
if(!model)throw Error('missing MLDR model')
const rule=model.make(),stated=model.laws(rule),stop=new Error('completed production generation')
if(countsDump.on||queryHook.on)throw Error('generation capture requires a fresh process')
const captured:{boundary?:{machine:Machine,laws:Law[]}}={}
let queries=0
countsDump.on=event=>{
 const value=event as {phase?:string,machine:Machine,laws:Law[]}
 if(value.phase!=='candidates')return
 if(captured.boundary)throw Error('multiple candidate boundaries')
 captured.boundary={machine:value.machine,laws:value.laws}
 throw stop
}
queryHook.on=()=>{queries++}
const before=rawWork(),start=performance.now()
try{proveRule(rule,stated,{search:{work}})}catch(error){if(error!==stop)throw error}finally{countsDump.on=undefined;queryHook.on=undefined}
const wallMs=performance.now()-start,after=rawWork()
const boundary=captured.boundary
if(!boundary)throw Error('generation did not reach the production candidate boundary')
if(queries)throw Error('generation-only capture executed proof queries')
const family=boundary.laws,raw=JSON.stringify(family),hash=(text:string)=>createHash('sha256').update(text).digest('hex')
const identity={sourcePin,work,count:family.length,rawSha256:hash(raw),orderedAlphaSha256:hash(JSON.stringify(family.map(strategyLawKey)))}
if(family.length!==49)throw Error('expected complete 49-law production generation, got '+family.length)
if(expected&&(identity.rawSha256!==expected.rawSha256||identity.orderedAlphaSha256!==expected.orderedAlphaSha256))throw Error('generation family identity changed')
mkdirSync(output,{recursive:true})
writeFileSync(join(output,'family.json'),raw)
writeFileSync(join(output,'machine.json'),JSON.stringify(boundary.machine))
writeFileSync(join(output,'identity.json'),JSON.stringify(identity,null,2)+'\n')
const record={schema:'mldr-generation-row/v1',id:'mldr',flags,wallMs,stageWalls:{admissionPrefixMs:wallMs,substageWallMs:null},stageWallNote:'No guessed substage walls. D must freeze parent-observer hooks for sampling/cubes/filter/assembly attribution.',start:'public proveRule after model/law construction',stop:'first production countsDump candidates boundary, before admission/rejection',proofQueries:queries,...identity,identityFrozen:!!expected,benchmarkAccepted:!!expected,raw:Object.fromEntries(workKeys.map(key=>[key,after[key]-before[key]])),candidateNames:family.map(law=>law.name)}
writeFileSync(join(output,'receipt.json'),JSON.stringify(record,null,2)+'\n')
console.log('GENERATION_ROW '+JSON.stringify(record))
