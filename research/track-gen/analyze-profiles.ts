// Deterministic postprocessing only; no searches are run here.
import {readFileSync,writeFileSync} from 'node:fs'
import {type Law} from '../../core/machine.ts'
const root=process.argv[2]??'runs',probeDir=process.argv[3]??'track-gen-probes-v2',lines=(file:string)=>readFileSync(file,'utf8').split('\n')
function normal(l:Law):string{
 const vars=new Map([l.forall,...l.keys??[]].filter((v):v is string=>!!v).map((v,i)=>[v,`$${i}`]))
 const go=(x:any):any=>{
  if(!x||typeof x!=='object')return x
  if(Array.isArray(x))return x.map(go)
  if(x.op==='var')return {name:vars.get(x.name)??x.name,op:'var'}
  const out:any=Object.fromEntries(Object.keys(x).sort().map(k=>[k,go(x[k])]))
  if(x.op==='and'||x.op==='or')out.xs=out.xs.flatMap((y:any)=>y.op===x.op?y.xs:[y]).sort((a:any,b:any)=>JSON.stringify(a).localeCompare(JSON.stringify(b)))
  if(x.op==='='&&JSON.stringify(out.a)>JSON.stringify(out.b))[out.a,out.b]=[out.b,out.a]
  return out
 }
 return JSON.stringify(go(l.holds))
}
const generation=JSON.parse(readFileSync(`${root}/track-gen-baseline-v1/generation.json`,'utf8'))
let side='',prefix='';const probes:any[]=[]
for(const line of lines(`${root}/${probeDir}/probe-pairs.log`)){
 const marker=/^PROBE side=(\S+) prefix=(.*)/.exec(line)
 if(marker){side=marker[1]!;prefix=marker[2]!}
 else if(line.startsWith('{"mode":"probe"')){
  const row=JSON.parse(line)
  const matches=(row.usage?.laws??[]).map((law:Law)=>({law:law.name,generated:generation.candidates.filter((c:Law)=>normal(c)===normal(law)).map((c:Law)=>c.name)}))
  probes.push({side,prefix,...row,matches})
 }
}
if(probes.length!==10)throw Error(`expected ten probe records, got ${probes.length}`)
for(const key of new Set(probes.map(p=>p.prefix))){
 const pair=probes.filter(p=>p.prefix===key)
 if(pair.length!==2||pair[0].proven!==pair[1].proven||pair[0].checked!==pair[1].checked||pair[0].countedMs!==pair[1].countedMs||JSON.stringify(pair[0].usage)!==JSON.stringify(pair[1].usage))throw Error(`probe differs: ${key}`)
}
writeFileSync(`${root}/${probeDir}/verified.json`,JSON.stringify({identical:true,probes},null,2)+'\n')
console.log(JSON.stringify(probes.map(({side,prefix,proven,checked,countedMs,matches})=>({side,prefix,proven,checked,countedMs,matches}))))
