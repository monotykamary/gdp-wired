import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {closeSync,mkdirSync,mkdtempSync,openSync,readFileSync,rmSync,statSync,writeFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawn,spawnSync} from 'node:child_process'
import {gunzipSync} from 'node:zlib'
const input=resolve('port-input'),scratch=mkdtempSync('/tmp/combined-census-')
const source=readFileSync(join(input,'source.txt'),'utf8').trim(),baseline=readFileSync(join(input,'baseline-source.txt'),'utf8').trim()
const out=resolve('/home/user/.sc-artifacts/lane-i-strict-originals',source,'off29'),ids=(JSON.parse(readFileSync(join(input,'ids.json'),'utf8')) as string[]).concat('mldr')
const env={...Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_'))),GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0'}
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
 assert.deepEqual(r.knobs,{GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0'});assert.equal(r.weights,undefined);assert.equal(r.clockReads,undefined);assert(!r.result.error)
 const root=r.phases.filter((p:any)=>p.parentId===null);assert.equal(root.length,1)
 for(const[key,value]of Object.entries(r.raw)){assert(Number.isSafeInteger(value)&&Number(value)>=0);assert.equal(root[0].raw[key],value);assert.equal(r.phases.reduce((n:number,p:any)=>n+p.exclusiveRaw[key],0),value)}
 for(const key of ['tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals'])assert.equal(r.raw[key],0)
 if(r.result.proven)assert(r.result.checked)
}
async function measure(id:string,target:'baseline'|'candidate'){
 const path=join(out,id+'-'+target+'.json.gz'),log=join(out,id+'-'+target+'.log'),fd=openSync(log,'w')
 const child=spawn('bun',[join(input,'flags-off-measure.ts'),roots[target],id,'15000000',path,target==='candidate'?source:baseline,target],{cwd:roots[target],env,stdio:['ignore',fd,fd],timeout:480000,killSignal:'SIGKILL'})
 const result=await new Promise<{code:number|null,error?:string}>(resolve=>{child.once('error',error=>resolve({code:null,error:String(error)}));child.once('exit',code=>resolve({code}))})
 closeSync(fd);assert.equal(result.code,0,JSON.stringify({id,target,...result,log}))
 const r=JSON.parse(gunzipSync(readFileSync(path)).toString());check(r,id,target)
 return{r,receipt:fileRecord(path),log:fileRecord(log)}
}
const rows:any[]=[],failures:{id:string,error:string}[]=[]
try{
 assert.equal(ids.length,29);assert.equal(new Set(ids).size,29);assert(ids.includes('mldr'));assert(ids.every(id=>/^[a-z0-9_-]+$/.test(id)))
 for(const line of readFileSync(join(input,'SHA256SUMS'),'utf8').trim().split('\n')){const m=/^([a-f0-9]{64})  ([a-z-]+\.tar)$/.exec(line);assert(m);assert.equal(hash(readFileSync(join(input,m[2]!))),m[1],m[2]!)}
 for(const target of ['baseline','candidate'] as const){for(const name of [target==='baseline'?'baseline':'source','gdp-ts','handwired'])sync(target+'-extract-'+name,'tar',['-xf',join(input,name+'.tar'),'-C',roots[target]],roots[target]);identities(target);sync(target+'-install','bun',['install','--frozen-lockfile'],roots[target])}
 let cursor=0
 await Promise.all(Array.from({length:4},async()=>{while(cursor<ids.length){const id=ids[cursor++]!;try{const before=await measure(id,'baseline'),after=await measure(id,'candidate');assert.deepEqual(after.r.custody,before.r.custody);assert.deepEqual(normalize(after.r),normalize(before.r),id);const row={id,verdict:after.r.result.verdict,units:after.r.units,normalizedSHA256:hash(Buffer.from(JSON.stringify(normalize(after.r)))),baseline:before.receipt,candidate:after.receipt,logs:[before.log,after.log]};rows.push(row);console.log('CENSUS_PAIR '+JSON.stringify(row))}catch(error){const failure={id,error:String(error)};failures.push(failure);console.log('CENSUS_PAIR_FAILURE '+JSON.stringify(failure))}}}))
 identities('baseline');identities('candidate')
 const summary={source,baseline,models:ids.length,exactNormalizedPairs:rows.length,checked:rows.filter(r=>r.verdict==='proven').length,unknown:rows.filter(r=>r.verdict==='unknown').length,rows:rows.sort((a,b)=>a.id.localeCompare(b.id)),failures,strict28Exact:rows.filter(r=>r.id!=='mldr').length,scope:'29 feature-off exact pairs including strict28; not full-W or timing'}
 const path=join(out,'summary.json');writeFileSync(path,JSON.stringify(summary,null,2)+'\n');console.log('CENSUS_SUMMARY '+JSON.stringify({...fileRecord(path),source,baseline,models:29,exactNormalizedPairs:rows.length,failures:failures.length}));assert.equal(failures.length,0);assert.equal(rows.length,29)
}catch(error){console.log('CENSUS_FAILURE '+JSON.stringify({source,baseline,out,error:String(error)}));process.exitCode=1}
finally{rmSync(scratch,{recursive:true,force:true})}
