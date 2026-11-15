import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {closeSync,existsSync,mkdirSync,mkdtempSync,openSync,readFileSync,rmSync,statSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),root=mkdtempSync('/tmp/rolling-partial-')
const source=readFileSync(join(input,'source.txt'),'utf8').trim()
const out=resolve(process.env.HOME??'.','.sc-artifacts/lane-i-rolling-next',source,'partial-source')
mkdirSync(out,{recursive:true})
const hash=(bytes:Buffer)=>createHash('sha256').update(bytes).digest('hex')
const blob=(bytes:Buffer)=>createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')
function receipt(path:string){return {path,bytes:statSync(path).size,sha256:hash(readFileSync(path))}}
function run(label:string,cmd:string,args:string[],overrides:Record<string,string>={}){
 const file=join(out,label+'.log'),fd=openSync(file,'w')
 const env={...process.env,...overrides}
 const result=spawnSync(cmd,args,{cwd:root,env,stdio:['ignore',fd,fd],timeout:800000})
 closeSync(fd)
 console.log('ROLLING_FILE '+JSON.stringify({label,source,...receipt(file),exit:result.status,signal:result.signal,error:result.error?.message}))
 if(result.error||result.status!==0)throw Error(label+' failed; retained '+file)
}
function identities(){
 const except=new Map(readFileSync(join(input,'exception-target.tree'),'utf8').trim().split('\n').map(line=>{const match=/^\d+ ([a-f0-9]+) \d\t(.+)$/.exec(line);assert(match);return[match[2]!,match[1]!] as const}))
 let unchanged=0,exceptions=0
 for(const line of readFileSync(join(input,'PROTECTED.tree'),'utf8').trim().split('\n')){
  const match=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line);assert(match)
  const path=match[2]!,expected=except.get(path)??match[1]
  assert.equal(blob(readFileSync(join(root,path))),expected,path)
  if(except.has(path))exceptions++;else unchanged++
 }
 assert.equal(exceptions,3)
 const baseline=readFileSync(join(input,'baseline-prover-rows.ts'),'utf8'),candidate=readFileSync(join(root,'kernel/prover-rows.ts'),'utf8')
 const restored=candidate.replace("import {withTableAdmission} from '../core/table-admission.ts'\n",'').replace(/\/\/ One-pass reindex[\s\S]*?(?=export function proverRows\(goal)/,'')
 assert.equal(restored,baseline,'B22 changed existing row materialization or native scope')
 assert(!existsSync(join(root,'core/count-closing-budget.ts')),'older uncommitted closing draft leaked into partial source')
 console.log('ROLLING_IDENTITIES '+JSON.stringify({source,unchanged,explicitB22Exceptions:exceptions,existingRowsUnchanged:true,closingDraftExcluded:true}))
}
try{
 for(const line of readFileSync(join(input,'SHA256SUMS'),'utf8').trim().split('\n')){const match=/^([a-f0-9]{64})  (source|gdp-ts|handwired)\.tar$/.exec(line);assert(match);assert.equal(hash(readFileSync(join(input,match[2]+'.tar'))),match[1],'archive hash')}
 for(const name of ['source','gdp-ts','handwired'])run('extract-'+name,'tar',['-xf',join(input,name+'.tar'),'-C',root])
 identities()
 run('install','bun',['install','--frozen-lockfile'])
 const features={GDP_WORK_STEPS:'0',GDP_COUNT_FRAMES:'1',GDP_COUNT_REJECTIONS:'1',GDP_COUNT_STRATEGIES:'1',GDP_COUNT_TIERS:'1',GDP_REQUEST_QUOTIENT:'1',GDP_COUNT_ROW_DEFER_CHECKS:'1',GDP_COUNT_FINAL_DEFER_CHECKS:'1',GDP_COUNT_LIFTED:'1',GDP_COUNT_LIFTED_PREREQUISITES:'1',GDP_COUNT_LIFTED_REPLACEMENT:'1',GDP_COUNT_DEFER_CHECKS:'1',GDP_COUNT_REINDEX_FACTS_ONLY:'1',GDP_COUNT_EMITTER_FRAME_POOL:'1',GDP_COUNT_C2_LEMMAS:'0'}
 run('legacy-components','bun',['test','kernel/prover-row-cache.test.ts','kernel/prover-rows.test.ts','core/count-case-compose.test.ts','core/count-emitter-frame-pool.test.ts','core/count-lifted-emitter-boundary.test.ts','core/count-lifted-shape.test.ts','core/count-lifted-increment.test.ts','core/count-lifted-transports.test.ts','core/count-deferred-checks.test.ts'],{...features,GDP_WORK_FULL:'0'})
 run('full-cap-components','bun',['test','core/count-reindex-budget.test.ts','core/table-admission.test.ts','core/count-emitter-frame-pool.test.ts','core/count-case-compose.test.ts'],{...features,GDP_WORK_FULL:'1'})
 run('native-family-controls','bun',['research/lane-i/rolling-20261111/family-replay.ts','research/lane-i/rolling-20261111/closed-family-proof.json.gz','--mutations'],{GDP_WORK_FULL:'0'})
 run('types-and-lint','bun',['run','check'])
 identities()
 console.log('ROLLING_PARTIAL_GATE '+JSON.stringify({source,status:'passed',out,scope:'B22/R2 source only; no A composition or calibration admission'}))
}catch(error){console.log('ROLLING_PARTIAL_GATE '+JSON.stringify({source,status:'failed',out,error:String(error)}));process.exitCode=1}
finally{rmSync(root,{recursive:true,force:true})}
