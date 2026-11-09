// Read-only projection of an existing frozen capture; not a proof checker.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
const p=JSON.parse(gunzipSync(readFileSync(process.argv[2]!)).toString()),name=process.argv[3]
for(const pass of [0,1]){
 const queries=p.captures.filter((c:any)=>c.pass===pass&&c.phase==='query'&&c.goal?.endsWith('@step'))
 const models=p.captures.filter((c:any)=>c.pass===pass&&c.phase==='model'&&c.goal?.endsWith('@step'))
 if(!queries.length)continue
 const view=(c:any)=>({phase:c.phase,hyps:c.hyps?.length,rawHyps:c.rawGoal?.hyps?.length,seedCount:c.seedCount,sourceTuples:Object.fromEntries(Object.entries(c.instances??{}).filter(([,v]:any)=>v.length)),countReads:c.certificateRequest?.reads,countInstances:c.certificateRequest?.insts,generation:c.generation,witness:c.witness})
 console.log(JSON.stringify({name,pass,law:p.record.law,queryCount:queries.length,modelCount:models.length,first:view(queries[0]),last:view(queries.at(-1)),firstModel:models[0]&&view(models[0]),lastModel:models.at(-1)&&view(models.at(-1))}))
}
