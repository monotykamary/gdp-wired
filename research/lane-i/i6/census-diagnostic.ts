import {isDeepStrictEqual} from 'node:util'
const failures:{kind:string,actual:unknown,expected?:unknown,label?:unknown}[]=[]
const a=Object.assign((ok:unknown,label?:unknown)=>{if(!ok)failures.push({kind:'condition',actual:ok,label})},{
 equal:(actual:unknown,expected:unknown,label?:unknown)=>{if(actual!==expected)failures.push({kind:'equal',actual,expected,label})},
 notEqual:(actual:unknown,expected:unknown,label?:unknown)=>{if(actual===expected)failures.push({kind:'notEqual',actual,expected,label})},
 deepEqual:(actual:unknown,expected:unknown,label?:unknown)=>{if(!isDeepStrictEqual(actual,expected))failures.push({kind:'deepEqual',actual,expected,label})}
})
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gunzipSync} from 'node:zlib'
const [dir,beforeDir,offDir,source]=process.argv.slice(2)
const old=['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr']
const native=['tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals'],keys=[...old,...native]
const legacy=[2.33,.0123,7.93,.672,.735,.0435,.0765,.599,15.6,.735,.492,7.93]
const read=(path:string)=>{const line=readFileSync(path,'utf8').split('\n').find(s=>s.startsWith('CANDIDATE_RECEIPT '));a(line,path);if(!line)throw Error('missing receipt '+path);const e=JSON.parse(line.slice(18)),b=Buffer.from(e.gzipBase64,'base64');a.equal(createHash('sha256').update(b).digest('hex'),e.sha256,path);return JSON.parse(gunzipSync(b).toString())}
const stable=(v:any):any=>Array.isArray(v)?v.map(stable):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).filter(([k])=>!['wallMs','exclusiveWallMs',...native].includes(k)).map(([k,x])=>[k,stable(x)])):v
const normalize=(r:any)=>stable(Object.fromEntries(Object.entries(r).filter(([k])=>k!=='source'&&k!=='target')))
const near=(x:number,y:number)=>a(Math.abs(x-y)<Math.max(1e-5,Math.abs(x)*1e-11),`${x} != ${y}`)
let proved=0,unknown=0,maxUnits=0;const coverage=Object.fromEntries(native.map(k=>[k,0])),rows=[]
for(const file of readdirSync(dir!).filter(f=>f.startsWith('strict-')&&f.endsWith('.log'))){
 const id=file.slice(7,-4),r=read(join(dir!,file)),before=read(join(beforeDir!,file)),off=read(join(dir!,'off-candidate-'+id+'.log')),oldOff=read(join(offDir!,'off-candidate-'+id+'.log'))
 a.equal(r.source,source);a.equal(off.source,source);a.equal(r.allowance,15000000);a.equal(r.clockReads,0);a.equal(r.knobs.GDP_WORK_FULL,'1');a.equal(off.knobs.GDP_WORK_FULL,'0');a.equal(off.knobs.GDP_WORK_STEPS,'0')
 a.deepEqual(Object.keys(r.raw),keys);a.deepEqual(Object.keys(r.weights),keys.slice(12));for(const x of Object.values(r.weights) as number[])a(Number.isFinite(x)&&x>0)
 a.equal(r.phases.filter((p:any)=>p.parentId===null).length,1)
 for(const k of keys){a(Number.isSafeInteger(r.raw[k])&&r.raw[k]>=0,k);a.equal(r.phases.find((p:any)=>p.parentId===null).raw[k],r.raw[k]);a.equal(r.phases.reduce((n:number,p:any)=>n+p.exclusiveRaw[k],0),r.raw[k]);for(const p of r.phases)a(Number.isSafeInteger(p.exclusiveRaw[k])&&p.exclusiveRaw[k]>=0,k)}
 const units=keys.reduce((n,k,i)=>n+r.raw[k]*(i<12?legacy[i]!:r.weights[k]),0);near(units,r.units)
 for(const k of native){coverage[k]+=r.raw[k];a.equal(off.raw[k],0);a.equal(off.searchRaw[k],0);for(const p of off.phases){a.equal(p.raw[k],0);a.equal(p.exclusiveRaw[k],0)}}
 a.deepEqual(normalize(off),normalize(oldOff),'flags-off drift '+id)
 a(!r.result.error,JSON.stringify(r.result));a.notEqual(r.result.verdict,'refuted');if(before.result.proven){a(r.result.proven&&r.result.checked,id);a.deepEqual(r.result,before.result,id)}
 if(r.result.proven){a(r.result.checked);proved++}else{a.equal(r.result.verdict,'unknown');unknown++}
 a(r.searchUnits<=15001024,JSON.stringify({id,units:r.searchUnits}));maxUnits=Math.max(maxUnits,r.searchUnits)
 rows.push({id,before:before.result.verdict,after:r.result.verdict,units:r.searchUnits,why:r.result.why,native:Object.fromEntries(native.map(k=>[k,r.raw[k]]))})
}
a.equal(rows.length,28);console.log('I6_CENSUS_DIAGNOSTIC '+JSON.stringify({source,failures,eligible:failures.length===0,proved,unknown,maxUnits,slack:Math.max(0,maxUnits-15000000),coverage,flagsOffIdentical:28,rows}))

if(failures.length)process.exitCode=1
