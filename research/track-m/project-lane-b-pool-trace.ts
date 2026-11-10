// Project newly observed runtime pool state; never reconstruct a pool or run search.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {strict as assert} from 'node:assert'
const file=process.argv[2];if(!file)throw Error('CAPTURE.gz required')
const data=JSON.parse(gunzipSync(readFileSync(file)).toString('utf8'))
const entries=data.captures.filter((c:any)=>c.runtimeSelection).map((c:any)=>{
 const runtime=c.runtimeSelection,pool=runtime.pool,reads=c.certificateRequest.reads
 const pre=reads.find((r:any[])=>r[1]==='inX$row'&&r[2].op==='var'&&r[2].name==='a$quorum#')
 const post=reads.find((r:any[])=>r[1]==='inX$row#'&&r[2].op==='var'&&r[2].name==='a$quorum#')
 const json=JSON.stringify,sort=(xs:unknown[])=>xs.map(x=>json(x)).sort()
 const wanted=pre&&post?sort([[1,json(post.slice(1))],[-1,json(pre.slice(1))]]):undefined
 const index=pool&&wanted?pool.keys.findIndex((id:string)=>{
  if(!id.startsWith('i'))return false
  const [terms,unit,below]=JSON.parse(id.slice(1))
  return unit===0&&json(sort(terms))===json(wanted)&&json(below)===json(c.decls.find((d:any)=>d.map===post[1]).below)
 }):null
 return {phase:c.phase,pass:c.pass,hyps:c.hyps.length,selectedInsts:c.certificateRequest.insts.length,wide:runtime.wide,supported:runtime.supported,lazyMode:runtime.lazyMode,poolKeys:pool?.keys.length??null,poolActive:pool?.active.length??null,poolCap:pool?.cap??null,framePoolIndex:index,frameActive:index!==null&&index>=0?pool.active.includes(pool.keys[index]):null,...(c.witness?{operation:c.witness.op,i:c.witness.i,size:c.witness.size}:{})}
})
assert(entries.length>0,'no runtime observation metadata')
console.log(JSON.stringify({evidenceOnly:true,observationOnly:true,newInstrumentedExecution:true,timingComparison:false,law:data.record.law,checked:data.record.checked,entries}))
