import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {closeSync,mkdirSync,mkdtempSync,openSync,readFileSync,rmSync,statSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),root=mkdtempSync('/tmp/combined-source-'),mode=process.argv[2]??'source'
const source=readFileSync(join(input,'source.txt'),'utf8').trim(),out=resolve('/home/user/.sc-artifacts/lane-i-combined',source,mode)
const clean=Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_')))
const features=JSON.parse(readFileSync(join(input,'profile.json'),'utf8')) as Record<string,string>
mkdirSync(out,{recursive:true})
const hash=(bytes:Buffer)=>createHash('sha256').update(bytes).digest('hex')
const blob=(bytes:Buffer)=>createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')
function run(label:string,cmd:string,args:string[],flags:Record<string,string>={}){
 const path=join(out,label+'.log'),fd=openSync(path,'w')
 const result=spawnSync(cmd,args,{cwd:root,env:{...clean,...flags},stdio:['ignore',fd,fd],timeout:1000000})
 closeSync(fd)
 console.log('COMBINED_FILE '+JSON.stringify({label,source,path,bytes:statSync(path).size,sha256:hash(readFileSync(path)),exit:result.status,signal:result.signal,error:result.error?.message}))
 if(result.error||result.status!==0)throw Error(label+' failed; retained '+path)
}
function tree(path:string){return readFileSync(path,'utf8').trim().split('\n').map(line=>{const match=/^\d+ (?:blob )?([a-f0-9]+)(?: \d)?\t(.+)$/.exec(line);assert(match);return{path:match[2]!,blob:match[1]!}})}
function identities(){
 const exceptions=new Map(tree(join(input,'exception-target.tree')).map(r=>[r.path,r.blob]))
 let unchanged=0,changed=0
 for(const row of tree(join(input,'PROTECTED.tree'))){assert.equal(blob(readFileSync(join(root,row.path))),exceptions.get(row.path)??row.blob,row.path);if(exceptions.has(row.path))changed++;else unchanged++}
 assert.equal(changed,3)
 const adopted=tree(join(input,'ADOPTED-A.tree'))
 for(const row of adopted)assert.equal(blob(readFileSync(join(root,row.path))),row.blob,row.path)
 const baseline=readFileSync(join(input,'baseline-prover-rows.ts'),'utf8'),current=readFileSync(join(root,'kernel/prover-rows.ts'),'utf8')
 assert.equal(current.replace("import {withTableAdmission} from '../core/table-admission.ts'\n",'').replace(/\/\/ One-pass reindex[\s\S]*?(?=export function proverRows\(goal)/,''),baseline)
 console.log('COMBINED_IDENTITIES '+JSON.stringify({source,unchanged,explicitB22Exceptions:changed,exactAdoptedA:adopted.length,existingRowsUnchanged:true,R1Included:false}))
}
try{
 for(const line of readFileSync(join(input,'SHA256SUMS'),'utf8').trim().split('\n')){const match=/^([a-f0-9]{64})  ([a-z-]+\.tar)$/.exec(line);assert(match);assert.equal(hash(readFileSync(join(input,match[2]!))),match[1],match[2]!)}
 for(const name of ['source','gdp-ts','handwired'])run('extract-'+name,'tar',['-xf',join(input,name+'.tar'),'-C',root])
 identities();run('install','bun',['install','--frozen-lockfile'])
 if(mode==='source'){
  run('types-and-lint','bun',['run','check'])
  run('legacy-components','bun',['test','kernel/prover-row-cache.test.ts','kernel/prover-rows.test.ts','core/count-case-compose.test.ts','core/count-emitter-frame-pool.test.ts','core/count-lifted-emitter-boundary.test.ts','core/count-lifted-shape.test.ts','core/count-lifted-increment.test.ts','core/count-lifted-transports.test.ts','core/count-deferred-checks.test.ts'],{...features,GDP_WORK_FULL:'0'})
  run('full-components','bun',['test','core/count-reindex-budget.test.ts','core/table-admission.test.ts','core/count-emitter-frame-pool.test.ts','core/count-case-compose.test.ts','core/count-generation-parent-cap.test.ts','core/count-generation-phase.test.ts','core/count-rejection-budget.test.ts','core/rejection-stage.test.ts','core/rejection-discovery.test.ts','core/rejection-transaction.test.ts','core/count-closing-budget.test.ts','core/count-closing-needs.test.ts','core/count-prerequisite-components.test.ts','core/count-prerequisite-plan.test.ts'],features)
  run('structured-deadline','bun',['test','core/count-structured-deadline.test.ts'],features)
  run('scheduler-public','bun',['test','core/count-prerequisite-public.test.ts'],features)
  run('public-closing','bun',['test','core/public-closing-proposal.test.ts'],features)
  run('a-core-native','bun',['test','core/count-prerequisite-components.test.ts','core/count-prerequisite-plan.test.ts','core/count-prerequisite-unknown.test.ts','core/count-component-budget.test.ts','core/count-prerequisite-expiration.test.ts','core/count-closing-budget.test.ts','core/count-closing-needs.test.ts','core/count-tier-budget.test.ts','core/count-attempt-expiration.test.ts'],{GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'})
  run('a-final-step','bun',['test','core/count-final-step.test.ts'],features)
  run('a-legacy-scope','bun',['test','core/count-proof-scope.test.ts','core/count-tier-integration.test.ts'])
  run('native-family-controls','bun',['research/lane-i/rolling-20261111/family-replay.ts','research/lane-i/rolling-20261111/closed-family-proof.json.gz','--mutations'],{GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0'})
  run('commitlint','bash',[join(input,'commitlint.sh'),input])
 }else if(mode==='endpoint')run('endpoint','bun',['research/lane-i/combined-next/endpoint.ts'],features)
 else throw Error('unknown mode '+mode)
 identities();console.log('COMBINED_GATE '+JSON.stringify({source,mode,status:'passed',out,scope:'source/native/compatibility only; not calibrated W or combined admission'}))
}catch(error){console.log('COMBINED_GATE '+JSON.stringify({source,mode,status:'failed',out,error:String(error)}));process.exitCode=1}
finally{rmSync(root,{recursive:true,force:true})}
