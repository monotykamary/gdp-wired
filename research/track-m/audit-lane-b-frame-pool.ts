// Reconstruct proposals only, from one retained model. Never calls a prover.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
import {certFor} from '../../core/counts.ts'
import {candidateWork} from '../../core/count-support.ts'
import {type CountInst,type MapRead,termColumn} from '../../kernel/kernel.ts'
import {withWall} from '../../kernel/prove.ts'
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
