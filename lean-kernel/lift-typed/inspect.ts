import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {isDeepStrictEqual} from 'node:util'
import {readCertificateGraph} from '../lift/proof-codec.ts'
const rows=[]
for(const dir of process.argv.slice(2)) {
 const outer=JSON.parse(readFileSync(join(dir,'CAPTURE.json'),'utf8'))
 const data:any=readCertificateGraph(join(dir,'graph'),outer.graphManifestSha256,{maxBytes:536870912,maxNodes:4000000,maxStrings:200000,maxArrayLength:2000000,maxShards:2048},()=>{})
 const shape=(x:any):any=>x&&typeof x==='object'?{keys:Object.keys(x),schema:x.schema,route:x.route,verdict:x.verdict,result:x.result&&{keys:Object.keys(x.result),proven:x.result.proven,checked:x.result.checked},phase:x.phase,checked:x.checked,original:x.original&&{keys:Object.keys(x.original),machine:x.original.machine&&{keys:Object.keys(x.original.machine),params:x.original.machine.params,inputs:x.original.machine.inputs,maps:Object.keys(x.original.machine.maps??{})},laws:x.original.laws?.length},proof:x.proof&&{keys:Object.keys(x.proof),kind:x.proof.kind},identityEqualsOuter:isDeepStrictEqual(x.identity,outer.identity),terms:x.terms&&{keys:Object.keys(x.terms),length:Array.isArray(x.terms)?x.terms.length:x.terms.terms?.length}}:x
 const nodes:any[]=[];let n=data.proof??data.final?.proof;while(n){nodes.push({kind:n.kind,context:n.context&&{keys:Object.keys(n.context),kind:n.context.kind},laws:n.laws?.length,machine:n.machine&&{params:n.machine.params,inputs:n.machine.inputs,maps:Object.keys(n.machine.maps??{})},proofKeys:Object.keys(n.proof??{})});if(n.kind!=='derived'||n.parents.length!==1)break;n=n.parents[0]}
 rows.push({dir,outer:shape(outer),data:shape(data),final:shape(data.final),nodes})
}
writeFileSync(join(process.env.SUPERCOMPUTER_OUTPUT_DIR??'.','inspection.json'),JSON.stringify(rows,null,2)+'\n')
console.log(JSON.stringify(rows,null,2))
