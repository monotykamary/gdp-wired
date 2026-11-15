import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {closeSync,mkdirSync,mkdtempSync,openSync,readFileSync,rmSync,statSync,writeFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawn,spawnSync} from 'node:child_process'
import {gunzipSync} from 'node:zlib'
const input=resolve('port-input'),root=mkdtempSync('/tmp/original-crossings-'),source=readFileSync(join(input,'source.txt'),'utf8').trim()
const out=resolve(process.env.HOME??'.','.sc-artifacts/lane-i-strict-originals',source,'first-crossings'),cases=JSON.parse(readFileSync(join(input,'cases.json'),'utf8')) as {id:string,actual:number}[]
const profile=JSON.parse(readFileSync(join(input,'flags.json'),'utf8')),env={...Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_'))),...profile}
mkdirSync(out,{recursive:true})
const hash=(b:Buffer|string)=>createHash('sha256').update(b).digest('hex')
const record=(path:string)=>({path,bytes:statSync(path).size,sha256:hash(readFileSync(path))})
function sync(label:string,cmd:string,args:string[]){const path=join(out,label+'.log'),fd=openSync(path,'w');const result=spawnSync(cmd,args,{cwd:root,env,stdio:['ignore',fd,fd],timeout:180000});closeSync(fd);console.log('CROSSING_FILE '+JSON.stringify({...record(path),exit:result.status}));assert.equal(result.status,0,label)}
const patches:{path:string,before:string,after:string}[]=[]
function patch(file:string,old:string,next:string){const path=join(root,file),text=readFileSync(path,'utf8');assert.equal(text.split(old).length,2,file+' anchor');const changed=text.replace(old,next);writeFileSync(path,changed);patches.push({path:file,before:hash(text),after:hash(changed)})}
const rows:any[]=[],failures:any[]=[]
try{
 assert.equal(source,'6115f86a8eade60c58aadf86df525548c04be6b9');assert.equal(cases.length,16)
 for(const row of cases)assert(/^[a-z0-9_-]+$/.test(row.id))
 for(const line of readFileSync(join(input,'SHA256SUMS'),'utf8').trim().split('\n')){const m=/^([a-f0-9]{64})  ([a-z-]+\.tar)$/.exec(line);assert(m);assert.equal(hash(readFileSync(join(input,m[2]!))),m[1])}
 for(const name of ['source','gdp-ts','handwired'])sync('extract-'+name,'tar',['-xf',join(input,name+'.tar'),'-C',root])
 patch('core/work-meter.ts','  n += extraWeights.reachCompiledEvals * coreMeter.reachCompiledEvals\n  return n','  n += extraWeights.reachCompiledEvals * coreMeter.reachCompiledEvals\n  ;(globalThis as any).__gapRead?.(n,rawWork())\n  return n')
 patch('core/work-observe.ts','coreMeter.evals += count; return','coreMeter.evals += count; (globalThis as any).__gapEval?.(coreMeter.evals); return')
 patch('core/meter.ts','tableAdmissionHook.admit?.(count); coreMeter.tableCells += count','tableAdmissionHook.admit?.(count); coreMeter.tableCells += count; (globalThis as any).__gapTable?.(coreMeter.tableCells)')
 patch('kernel/prove.ts','budgetUnitsEnd = Math.min(previous ?? Infinity, workCap, fullWork() + units)','budgetUnitsEnd = Math.min(previous ?? Infinity, workCap, fullWork() + units)\n    ;(globalThis as any).__gapBudget?.(budgetUnitsEnd)')
 writeFileSync(join(out,'instrumentation.json'),JSON.stringify({source,patches,scope:'temporary stack hooks only; not an admission patch or timing measurement'},null,2)+'\n')
 sync('install','bun',['install','--frozen-lockfile'])
 let cursor=0
 await Promise.all(Array.from({length:4},async()=>{while(cursor<cases.length){const item=cases[cursor++]!,path=join(out,item.id+'.json.gz'),log=join(out,item.id+'.log'),fd=openSync(log,'w');try{
  const child=spawn('bun',['--preload',join(input,'probe-preload.ts'),join(input,'profiled-measure.ts'),root,item.id,'15000000',path,source,'baseline'],{cwd:root,env,stdio:['ignore',fd,fd],timeout:600000,killSignal:'SIGKILL'})
  const code=await new Promise<number|null>((res,rej)=>{child.once('error',rej);child.once('exit',res)});closeSync(fd);assert.equal(code,0,item.id)
  const data=JSON.parse(gunzipSync(readFileSync(path)).toString()),line=readFileSync(log,'utf8').split('\n').find(l=>l.startsWith('CAP_GAP_PROBE '));assert(line,item.id+' missing probe')
  const probe=JSON.parse(line.slice('CAP_GAP_PROBE '.length));assert(probe.firstAbove,item.id+' no crossing');assert.equal(probe.rootEnd-probe.rootStart,15000000);assert.equal(data.searchUnits,item.actual,item.id+' instrumentation changed work');assert(data.searchUnits>15000000)
  const row={id:item.id,source,actual:data.searchUnits,overshoot:data.searchUnits-15000000,result:data.result,firstObservedCrossing:probe.firstAbove,polls:probe.polls,reads:probe.reads,largestGaps:probe.top,receipt:record(path),log:record(log)};rows.push(row);console.log('CROSSING_CASE '+JSON.stringify({id:item.id,actual:row.actual,overshoot:row.overshoot,receipt:row.receipt,log:row.log}))
 }catch(error){try{closeSync(fd)}catch{}failures.push({id:item.id,error:String(error),log});console.log('CROSSING_FAILURE '+JSON.stringify(failures.at(-1)))}}}))
 const summary={source,models:16,rows:rows.sort((a,b)=>a.id.localeCompare(b.id)),failures,patches,scope:'baseline-only disposable stack probe; no runtime fix, cap clearance or timing claim'};const path=join(out,'summary.json');writeFileSync(path,JSON.stringify(summary,null,2)+'\n');console.log('CROSSING_SUMMARY '+JSON.stringify(record(path)));assert.equal(failures.length,0);assert.equal(rows.length,16)
}catch(error){console.log('CROSSING_ERROR '+JSON.stringify({error:String(error),out}));process.exitCode=1}finally{rmSync(root,{recursive:true,force:true})}
