// Independent aggregate audit of the three complete measurement sets.
import {readFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {auditIntegrity,type IntegrityRun} from './census-integrity-audit.ts'
const dirs=process.argv.slice(2);if(dirs.length!==3)throw new Error('three complete measurement directories required')
const json=(d:string,f:string)=>JSON.parse(readFileSync(join(d,f),'utf8'))
const all:IntegrityRun[]=[],rawMissing:string[]=[]
let input:string|undefined,bun:string|undefined,vm:string|undefined,production:string|undefined
for(const dir of dirs){
 const source=json(dir,'source-manifest.json'),runtime=json(dir,'runtime.json'),runs=json(dir,'measurements.json')
 auditIntegrity(runs,source)
 const signature=JSON.stringify(source.before)
 if(production&&production!==signature)throw new Error('cross-batch source changed');production=signature
 if(input&&input!==runtime.inputSha256)throw new Error('cross-batch input changed');input=runtime.inputSha256
 if(bun&&bun!==runtime.bunRevision)throw new Error('cross-batch runtime changed');bun=runtime.bunRevision
 const places=Object.values(json(dir,'placement.json')) as {vm:string,vcpus:number,exclusive:boolean,co_tenants:number}[]
 if(places.length!==1)throw new Error('not a single VM job')
 const place=places[0]!
 if(!place.exclusive||place.vcpus!==8||place.co_tenants!==0||vm&&place.vm!==vm)throw new Error('placement mismatch');vm=place.vm
 if(runs.length!==8||runs.some((r:any)=>r.skipped))throw new Error('missing planned trial')
 for(const r of runs){all.push({...r,id:dir+'/'+r.id});for(const suffix of ['.log','.stderr.log'])if(!existsSync(join(dir,r.id+suffix)))rawMissing.push(dir+'/'+r.id+suffix)}
}
const rows=auditIntegrity(all,{productionDifferences:[],installedProductionDifferences:[]})
console.log(JSON.stringify({runs:all.length,lawResults:rows.length,checked:rows.length,inputSha256:input,bunRevision:bun,vm,productionEqual:true,countedWorkExact:true,profiledCallCountsExact:true,rawMissing},null,2))
