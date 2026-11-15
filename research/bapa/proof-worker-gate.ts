// Fresh-process regression control: compare observation ON versus OFF on the
// same trivial protocol, then integrity-read the saved closure without proving.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {installProfile, defaultWork} from './proof-worker.ts'
import {readFamilyCapsule} from './proof-codec.ts'

installProfile(process.env)
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
const read=(name:string)=>JSON.parse(readFileSync(join(out,name),'utf8'))
const positive=read('consensus/result.json'), negative=read('tiny-work/result.json')
if(positive.status!=='captured-unqualified'||!positive.proven||!positive.checked||positive.publicCalls!==1||!positive.retention.complete||positive.allSizesProven||positive.leanExecuted||negative.status!=='not-verified'||negative.publicCalls!==1||negative.proven||negative.checked)throw Error('smoke control failed')
const {manifest,data}=readFamilyCapsule(join(out,'consensus/closure'),positive.retention.manifestSha256,{maxBytes:128*1024*1024,maxNodes:1_000_000,maxStrings:10_000,maxArrayLength:1_000_000,maxShards:32},()=>{})
if(manifest.projection.kind!=='unqualified'||(data as {verdict:{checked:boolean}}).verdict.checked!==true)throw Error('fresh-process capsule read failed')
const [{protocols},{proveRule},{workAdmissionSnapshot}]=await Promise.all([import('../protocols/ic3syn/models.ts'),import('../../core/dsl.ts'),import('../../core/work-admission.ts')])
const p=protocols.find(p=>p.id==='consensus')!,r=p.make(),laws=p.laws(r),before=workAdmissionSnapshot()
const verdict=proveRule(r,laws,{search:{work:defaultWork(p.id)}})
const after=workAdmissionSnapshot(),delta=Object.fromEntries(Object.entries(after.counters).map(([k,v])=>[k,String(BigInt(v)-BigInt(before.counters[k as keyof typeof before.counters]))]))
if(!verdict.proven||!verdict.checked||JSON.stringify(delta)!==JSON.stringify(read('consensus/work.json').counterDeltas))throw Error('capture changes native work counters')
console.log(JSON.stringify({positive:positive.status,negative:negative.status,calls:[positive.publicCalls,negative.publicCalls],capsuleRead:true,observationCounterParity:true,projection:manifest.projection}))
