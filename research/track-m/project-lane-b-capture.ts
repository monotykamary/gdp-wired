// Read-only projection of captured data; never runs search or mutates a proof.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
const file=process.argv[2];if(!file)throw Error('CAPTURE.json.gz required')
const data=JSON.parse(gunzipSync(readFileSync(file)).toString('utf8')),r=data.record
const counts=(xs:string[])=>Object.fromEntries([...new Set(xs)].map(k=>[k,xs.filter(x=>x===k).length]))
const at=(a:Record<string,unknown[]>|undefined)=>Object.entries(a??{}).map(([law,tuples])=>({law,tuples:tuples.length}))
const queries=(data.captures as any[]).filter(c=>c.rawGoal)
const project=(c:any)=>({phase:c.phase,goal:c.goal,pass:c.pass,hyps:c.hyps?.length,rawHyps:c.rawGoal?.hyps?.length,seedCount:c.seedCount,generation:c.generation,instances:at(c.instances),countInstances:c.certificateRequest?.insts?.length,reads:c.certificateRequest?.reads?.length})
const models=(data.captures as any[]).filter(c=>c.phase==='model')
const last=models.at(-1)
console.log(JSON.stringify({file,law:r.law,checked:r.checked,units:r.units,wallMs:r.wallMs,profile:r.profile,phases:counts(r.events.map((e:any)=>String(e.phase))),queries:queries.map(project),lastModel:last?{...project(last),witness:last.witness,reads:last.certificateRequest?.reads,insts:last.certificateRequest?.insts}:null,target:data.laws.find((l:any)=>l.name===r.law)},null,2))
