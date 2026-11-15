import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {closeSync,mkdirSync,mkdtempSync,openSync,readFileSync,rmSync,statSync,writeFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawn,spawnSync} from 'node:child_process'
import {gunzipSync} from 'node:zlib'
const input=resolve('port-input'),scratch=mkdtempSync('/tmp/combined-census-')
const source=readFileSync(join(input,'source.txt'),'utf8').trim(),baseline=readFileSync(join(input,'baseline-source.txt'),'utf8').trim()
const out=resolve(process.env.HOME??'.','.sc-artifacts/lane-i-strict-originals',source,'cap28'),ids=JSON.parse(readFileSync(join(input,'ids.json'),'utf8')) as string[]
const profile=JSON.parse(readFileSync(join(input,'flags.json'),'utf8')) as Record<string,string>
const negatives=new Map((JSON.parse(readFileSync(join(input,'cases.json'),'utf8')) as {id:string,actual:number}[]).map(c=>[c.id,c.actual]))
const env={...Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_'))),...profile}
const roots={baseline:join(scratch,'baseline'),candidate:join(scratch,'candidate')}
mkdirSync(out,{recursive:true});for(const root of Object.values(roots))mkdirSync(root)
const hash=(bytes:Buffer)=>createHash('sha256').update(bytes).digest('hex')
const blob=(bytes:Buffer)=>createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')
const fileRecord=(path:string)=>({path,bytes:statSync(path).size,sha256:hash(readFileSync(path))})
function sync(label:string,cmd:string,args:string[],cwd:string){const path=join(out,label+'.log'),fd=openSync(path,'w');const r=spawnSync(cmd,args,{cwd,env,stdio:['ignore',fd,fd],timeout:180000});closeSync(fd);console.log('CENSUS_FILE '+JSON.stringify({label,...fileRecord(path),exit:r.status}));assert.equal(r.status,0,label)}
function identities(target:'baseline'|'candidate'){
 for(const line of readFileSync(join(input,'PROTECTED.tree'),'utf8').trim().split('\n')){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line);assert(m);assert.equal(blob(readFileSync(join(roots[target],m[2]!))),m[1],target+':'+m[2])}
}
const stable=(v:any):any=>Array.isArray(v)?v.map(stable):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).filter(([k])=>!['wallMs','exclusiveWallMs'].includes(k)).map(([k,x])=>[k,stable(x)])):v
const normalize=(r:any)=>stable(Object.fromEntries(Object.entries(r).filter(([k])=>!['source','target','custody'].includes(k))))
function check(r:any,id:string,target:'baseline'|'candidate'){
 assert.equal(r.source,target==='candidate'?source:baseline);assert.equal(r.id,id);assert.equal(r.target,target);assert.equal(r.allowance,15000000)
 assert.deepEqual(r.knobs,profile);assert(r.weights&&typeof r.weights==='object');assert.equal(r.clockReads,undefined);assert(!r.result.error);assert(Number.isFinite(r.searchUnits)&&r.searchUnits>=0)
 for(const value of Object.values(r.weights))assert(Number.isFinite(value)&&Number(value)>=0)
 const root=r.phases.filter((p:any)=>p.parentId===null);assert.equal(root.length,1)
 for(const[key,value]of Object.entries(r.raw)){assert(Number.isSafeInteger(value)&&Number(value)>=0);assert.equal(root[0].raw[key],value);assert.equal(r.phases.reduce((n:number,p:any)=>n+p.exclusiveRaw[key],0),value)}
 if(r.result.proven)assert(r.result.checked)
}
async function measure(id:string,target:'baseline'|'candidate'){
 const path=join(out,id+'-'+target+'.json.gz'),log=join(out,id+'-'+target+'.log'),fd=openSync(log,'w')
 const child=spawn('bun',[join(input,'profiled-measure.ts'),roots[target],id,'15000000',path,target==='candidate'?source:baseline,target],{cwd:roots[target],env,stdio:['ignore',fd,fd],timeout:480000,killSignal:'SIGKILL'})
 const result=await new Promise<{code:number|null,error?:string}>(resolve=>{child.once('error',error=>resolve({code:null,error:String(error)}));child.once('exit',code=>resolve({code}))})
 closeSync(fd);assert.equal(result.code,0,JSON.stringify({id,target,...result,log}))
 const r=JSON.parse(gunzipSync(readFileSync(path)).toString());check(r,id,target)
 return{r,receipt:fileRecord(path),log:fileRecord(log)}
}
const rows:any[]=[],failures:{id:string,error:string}[]=[]
try{
 assert.equal(hash(readFileSync(join(input,'flags.json'))),'253c51b018d77d5c1d441f82b15756ca3cd473b0912f072d436f6f41ec40162b');assert.equal(Object.keys(profile).length,19);assert.equal(baseline,'f81c2c50810052de0a33e50f18900ab12a6a1cc2');assert.equal(negatives.size,16)
 assert.equal(ids.length,28);assert.equal(new Set(ids).size,28);assert(!ids.includes('mldr'));assert(ids.every(id=>/^[a-z0-9_-]+$/.test(id)))
 for(const line of readFileSync(join(input,'SHA256SUMS'),'utf8').trim().split('\n')){const m=/^([a-f0-9]{64})  ([a-z-]+\.tar)$/.exec(line);assert(m);assert.equal(hash(readFileSync(join(input,m[2]!))),m[1],m[2]!)}
 for(const target of ['baseline','candidate'] as const){for(const name of [target==='baseline'?'baseline':'source','gdp-ts','handwired'])sync(target+'-extract-'+name,'tar',['-xf',join(input,name+'.tar'),'-C',roots[target]],roots[target]);identities(target);sync(target+'-install','bun',['install','--frozen-lockfile'],roots[target])}
 let cursor=0
 await Promise.all(Array.from({length:4},async()=>{while(cursor<ids.length){const id=ids[cursor++]!;try{const before=await measure(id,'baseline'),after=await measure(id,'candidate');assert.deepEqual(after.r.custody,before.r.custody);assert.deepEqual(after.r.weights,before.r.weights);assert.deepEqual(after.r.laws,before.r.laws);assert(after.r.searchUnits<=after.r.allowance,id+' remains over cap');if(negatives.has(id)){assert.equal(before.r.searchUnits,negatives.get(id),id+' baseline moved');assert.equal(before.r.result.verdict,'unknown');assert.equal(after.r.result.verdict,'unknown');for(const key of Object.keys(before.r.raw)){assert(after.r.raw[key]<=before.r.raw[key],id+' raw increased:'+key);assert(after.r.searchRaw[key]<=before.r.searchRaw[key],id+' search raw increased:'+key)}}else assert.deepEqual(normalize(after.r),normalize(before.r),id);const row={id,verdict:after.r.result.verdict,units:after.r.units,budgetObservation:{within:after.r.searchUnits<=after.r.allowance,excess:Math.max(0,after.r.searchUnits-after.r.allowance),requested:after.r.allowance,searchUnits:after.r.searchUnits},normalizedSHA256:hash(Buffer.from(JSON.stringify(normalize(after.r)))),baseline:before.receipt,candidate:after.receipt,logs:[before.log,after.log]};rows.push(row);console.log('CENSUS_PAIR '+JSON.stringify(row))}catch(error){const failure={id,error:String(error)};failures.push(failure);console.log('CENSUS_PAIR_FAILURE '+JSON.stringify(failure))}}}))
 identities('baseline');identities('candidate')
 const summary={source,baseline,models:ids.length,exactNormalizedPairs:rows.length,checked:rows.filter(r=>r.verdict==='proven').length,unknown:rows.filter(r=>r.verdict==='unknown').length,rows:rows.sort((a,b)=>a.id.localeCompare(b.id)),failures,withinRequestedCap:rows.every(r=>r.budgetObservation.within),budgetOvershoots:rows.filter(r=>!r.budgetObservation.within).map(r=>({id:r.id,...r.budgetObservation})),profileSHA256:hash(readFileSync(join(input,'flags.json'))),flags:profile,closedNegatives:rows.filter(r=>negatives.has(r.id)).length,scope:'active19 strict-W originals:16 repaired negatives,12 exact previously-in-cap controls; no timing or 1G claim'}
 const path=join(out,'summary.json');writeFileSync(path,JSON.stringify(summary,null,2)+'\n');console.log('CENSUS_SUMMARY '+JSON.stringify({...fileRecord(path),source,baseline,models:28,exactNormalizedPairs:rows.length,failures:failures.length}));assert.equal(failures.length,0);assert.equal(rows.length,28);assert(rows.every(r=>r.budgetObservation.within));assert.equal(rows.filter(r=>negatives.has(r.id)).length,16)
}catch(error){console.log('CENSUS_FAILURE '+JSON.stringify({source,baseline,out,error:String(error)}));process.exitCode=1}
finally{rmSync(scratch,{recursive:true,force:true})}
