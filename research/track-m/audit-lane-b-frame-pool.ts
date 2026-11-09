// Reconstruct proposals only, from one retained model. Never calls a prover.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
import {certFor} from '../../core/counts.ts'
import {candidateWork} from '../../core/count-support.ts'
import {type CountInst,type MapRead,mcGoal,termColumn} from '../../kernel/kernel.ts'
import {brokenOf,withWall} from '../../kernel/prove.ts'
import {walkOnce} from '../../core/machine.ts'
import {dirname,join} from 'node:path'
const [captureFile,archivedSource]=process.argv.slice(2)
if(!captureFile||!archivedSource)throw Error('CAPTURE.gz ARCHIVED_COUNTS.ts required')
const data=JSON.parse(gunzipSync(readFileSync(captureFile)).toString('utf8'))
const fragment=(s:string)=>{const a=s.indexOf('export function certFor('),b=s.indexOf('\n// ---',a);assert(a>=0&&b>a);return s.slice(a,b)}
const generator=fragment(readFileSync('core/counts.ts','utf8'))
assert.equal(generator,fragment(readFileSync(archivedSource,'utf8')),'captured generator changed')
for(const [i,t]of data.columns.entries())assert.equal(termColumn(t),`⟦${i}⟧`)
const capture=data.captures.filter((c:any)=>c.phase==='model').at(-1)
assert(capture?.rawGoal&&capture.decls&&capture.certificateRequest)
assert.equal(capture.witness.op,1);assert.equal(capture.witness.i,0);assert.equal(capture.witness.size,3)
const selected=capture.certificateRequest,work=candidateWork()
const full=withWall(performance.now()+7000,()=>certFor(capture.rawGoal,capture.decls,true,1000,work.tick,true))
const key=(r:MapRead)=>JSON.stringify(r.slice(1))
const pre=selected.reads.find((r:MapRead)=>r[1]==='inX$row'&&r[2].op==='var'&&r[2].name==='a$quorum#') as MapRead|undefined
const post=selected.reads.find((r:MapRead)=>r[1]==='inX$row#'&&r[2].op==='var'&&r[2].name==='a$quorum#') as MapRead|undefined
assert(pre&&post)
const indexes=(packet:{reads:MapRead[],insts:CountInst[]},a:MapRead,b:MapRead)=>{
 const reads=new Map(packet.reads.map(r=>[r[0],key(r)]))
 return packet.insts.flatMap((q,i)=>q.unit===0&&q.terms.length===2&&q.terms.some(([n,r])=>n===1&&reads.get(r)===key(a))&&q.terms.some(([n,r])=>n===-1&&reads.get(r)===key(b))?[i]:[])
}
console.log(JSON.stringify({evidenceOnly:true,proofSearch:false,scope:'retained flags-first Inv* op1/i=0 model',generatorSha256:createHash('sha256').update(generator).digest('hex'),generatorMatchesCapture:true,cap:1000,generation:work.state,selectedCount:selected.insts.length,generatedCount:full.insts.length,selectedReads:selected.reads.length,generatedReads:full.reads.length,postMinusPre:{selected:indexes(selected,post,pre),generated:indexes(full,post,pre)},preMinusPost:{selected:indexes(selected,pre,post),generated:indexes(full,pre,post)}}))

// Candidate-local projection of the lazy completion filter, not a selector or proof.
if(process.argv.includes('--completions')){
 const family=JSON.parse(readFileSync(join(dirname(archivedSource),'family.json'),'utf8'))
 assert.deepEqual(family.laws,data.laws)
 const supportNames=new Set(family.support.map((i:number)=>family.laws[i].name))
 const supported=capture.laws.some((l:any)=>supportNames.has(l.name))
 assert.deepEqual(full.reads,selected.reads,'read naming changed')
 const base=mcGoal(capture.rawGoal.hyps,capture.decls,selected)
 assert(base,'captured packet did not reify')
 assert.deepEqual(base.hyps,capture.hyps,'captured encoding changed')
 const baseJudge=brokenOf(base),w=capture.witness
 assert.deepEqual(baseJudge(w),[],'retained model fails original goal')
 const i=indexes(full,post,pre)[0];assert(i!==undefined,'frame no longer generated')
 const occupied=JSON.stringify([capture.rawGoal,capture.decls,selected])
 let serial=0,wit:string
 do{wit=`frame$audit$${serial++}`}while(occupied.includes(JSON.stringify(wit)))
 const candidate={...full.insts[i]!,wit}
 const packet={...selected,insts:[...selected.insts,candidate]}
 const extended=mcGoal(capture.rawGoal.hyps,capture.decls,packet)
 assert(extended,'frame packet did not reify')
 assert.deepEqual(extended.hyps.slice(0,base.hyps.length),base.hyps,'base prefix changed')
 assert.equal(extended.hyps.length,base.hyps.length+1,'frame is not exactly one hypothesis')
 const frame=extended.hyps.length-1,judge=brokenOf(extended),maps=new Set<string>()
 walkOnce(extended.hyps[frame],(o:any)=>{if(o.op==='get')maps.add(o.map)})
 const mps=[...maps],one=Object.fromEntries(mps.map(mp=>[mp,1]))
 const variants=[undefined,one,...mps.map(mp=>({[mp]:1})),...mps.map(mp=>({...one,[mp]:0}))]
 const probe=(strict:boolean)=>{
  const initiallyBroken=judge(w,[frame]).includes(frame)
  if(!initiallyBroken)return {initiallyBroken,completionTrials:0,wouldRemainBroken:false}
  let trials=0
  for(const defaults of strict?[undefined]:variants)for(let x=0;x<16;x++){
   const w2={...w,[wit]:x};trials++
   if(!judge(w2,[frame],false,defaults).includes(frame)){
    const brokenBase=baseJudge(w2,undefined,false,defaults)
    return {initiallyBroken,completionTrials:trials,wouldRemainBroken:false,firstAccepted:{witness:x,defaults:defaults??null,baseStillValid:brokenBase.length===0,brokenBaseCount:brokenBase.length,brokenBasePrefix:brokenBase.slice(0,12)}}
   }
  }
  return {initiallyBroken,completionTrials:trials,wouldRemainBroken:true}
 }
 console.log(JSON.stringify({evidenceOnly:true,proofSearch:false,audit:'candidate-local lazy completion filter',capturePass:capture.pass,supported,selectedInsts:selected.insts.length,baseModelValid:true,frameCandidateIndex:i,frameWitness:wit,frameMaps:mps,default:probe(false),strict:probe(true),notActualSelectorReplay:true}))
}
