// Generate only the two missing start certificates. Accepted step proofs stay frozen.
import {readFileSync,writeFileSync} from 'node:fs'
import {gzipSync} from 'node:zlib'
import {spawnSync} from 'node:child_process'
import {checkMC,type CountCert} from '../../../kernel/kernel.ts'
import {grow,withWall,withWork,fullWork,clock} from '../../../kernel/prove.ts'
import {frozenStart,sha} from './start-context.ts'
const paths=['kernel/kernel.ts','kernel/prove.ts','research/egraph/historical/proofs/p3-bridge-step.json','research/egraph/historical/proofs/safety-direct-step.json']
const source=Object.fromEntries(paths.map(p=>[p,sha(readFileSync(p))]));if(source['kernel/prove.ts']!=='5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708')throw Error('prover pin')
console.log('SOURCE',JSON.stringify(source));let queries=0
for(const id of ['safety','p3']){
  const started=performance.now(),work=fullWork(),c=frozenStart(id)
  queries++
  const out=withWall(started+25000,()=>withWork(work+2000000,()=>grow(c.goal,new Map(),{nodes:0,until:clock()+25000})))
  if(!('tree'in out)){console.log('START_RESULT',JSON.stringify({id,checked:false,stuck:out.stuck,why:out.why}));process.exitCode=1;continue}
  const cert:CountCert={reads:[],insts:[],picks:[],tree:out.tree},checked=checkMC(c.base.goal.hyps,c.base.decls,cert)
  if(!checked)throw Error('start proof rejected')
  const packet=JSON.stringify({id,inputSha256:c.inputSha256,goalSha256:c.goalSha256,instances:{},cert}),path=`new-${id}-start.json`;writeFileSync(path,packet)
  const cold=spawnSync('bun',['--no-install','research/egraph/historical/starts-cold.ts',path],{encoding:'utf8',timeout:5000}),coldChecked=cold.status===0&&!cold.error&&!cold.signal
  console.log(cold.stdout.trim());if(cold.stderr)console.error(cold.stderr)
  console.log('START_RESULT',JSON.stringify({id,name:c.goal.name,rows:c.goal.hyps.length,goalSha256:c.goalSha256,checked,coldChecked,proofWork:fullWork()-work,outerMs:25000,sharedWorkGuard:2000000}))
  console.log('START_ARTIFACT',JSON.stringify({path,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}));if(!coldChecked)process.exitCode=1
}
if(queries!==2)throw Error('unexpected search count')
for(const p of paths)if(sha(readFileSync(p))!==source[p])throw Error('frozen source/proof changed')
console.log('POSTFLIGHT',JSON.stringify({unchanged:true,newSearchQueries:queries,oldPositiveProofSearches:0}))
