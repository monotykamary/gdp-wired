// Actual original safety-step attempt, with direct focus-instance use ablation.
import {readFileSync,writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import type {E} from '../../../core/machine.ts'
import {assumed,countedObligations,checkMC,mcGoal,type CountCert} from '../../../kernel/kernel.ts'
import {grow,withWall,withWork,fullWork,clock} from '../../../kernel/prove.ts'
import {Meter} from '../match.ts'
import {stableKey} from '../recover-instances.ts'
import {safetyContext,sha} from './safety-context.ts'
const c=safetyContext(),raw=readFileSync('research/egraph/historical/recovery/safety-focus-v6.json')
if(sha(raw)!=='4d7c5adf0d85dd3f32e42ad23b0e1ded8db9b928f44e044e4fd0ae4286891a14')throw Error('candidate pin')
const proposal=JSON.parse(raw.toString()) as {goalSha256:string,lawSha256:string,keys:string[],candidates:{binding:Record<string,E>,sha256:string}[]}
if(proposal.goalSha256!==c.goalSha256||proposal.lawSha256!==sha(JSON.stringify(c.input.law))||proposal.candidates.length>32)throw Error('source candidate mismatch')
const paths=['kernel/kernel.ts','kernel/prove.ts','research/egraph/historical/safety-context.ts','research/egraph/historical/safety-cold-check.ts','research/egraph/historical/safety-focus.ts'],before=Object.fromEntries(paths.map(p=>[p,sha(readFileSync(p))]))
if(before['kernel/prove.ts']!=='5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708')throw Error('prover pin')
console.log('SOURCE',JSON.stringify(before))
for(const enabled of [false,true]){
  const started=performance.now(),work=fullWork(),meter=new Meter(100000,started+1000)
  const additional=proposal.candidates.flatMap(p=>{const at=proposal.keys.map(k=>p.binding[k]!);const rows=assumed([c.input.law],{[c.input.law.name]:at});if(rows.length!==1||sha(stableKey(rows[0],meter))!==p.sha256)throw Error('candidate reconstruction');return at})
  const instances={...c.metadata.instances,[c.input.law.name]:[...(c.metadata.instances[c.input.law.name]??[]),...(enabled?additional:[])]}
  const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
  const goal=mcGoal(base.goal.hyps,base.decls,c.metadata);if(!goal)throw Error('count schema');goal.name=c.original.name
  const available=new Map<string,number>();for(const row of goal.hyps){const key=stableKey(row,meter);available.set(key,(available.get(key)??0)+1)}
  for(const row of c.original.hyps){const key=stableKey(row,meter),n=available.get(key)??0;if(!n)throw Error('original row omitted');available.set(key,n-1)}
  const outcome=withWall(started+25000,()=>withWork(work+2000000,()=>grow(goal,new Map(),{nodes:0,until:clock()+25000})))
  let checked=false,coldChecked:boolean|undefined,removalRejected:boolean|undefined
  if('tree'in outcome){
    const cert:CountCert={reads:c.metadata.reads,insts:c.metadata.insts,picks:c.metadata.picks,tree:outcome.tree}
    checked=checkMC(base.goal.hyps,base.decls,cert)
    if(checked){
      if(enabled)removalRejected=!checkMC(c.base.goal.hyps,c.base.decls,cert)
      const packet=JSON.stringify({goalSha256:c.goalSha256,instances,cert}),path=`safety-focus-${enabled}.json`;writeFileSync(path,packet)
      const cold=spawnSync('bun',['--no-install','research/egraph/historical/safety-cold-check.ts',path],{encoding:'utf8',timeout:5000});coldChecked=cold.status===0&&!cold.error&&!cold.signal
      console.log(cold.stdout.trim());if(cold.stderr)console.error(cold.stderr)
      console.log('ARTIFACT',JSON.stringify({kind:'proof',path,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
    }
  }else if(outcome.witness){
    const packet=JSON.stringify({goalSha256:c.goalSha256,enabled,instances,goal,witness:outcome.witness})
    console.log('ARTIFACT',JSON.stringify({kind:'witness',path:`safety-witness-${enabled}.json`,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
  }
  console.log('SAFETY_FOCUS',JSON.stringify({enabled,goalSha256:c.goalSha256,originalRows:202,rows:goal.hyps.length,addedTuples:enabled?proposal.candidates.length:0,matchingUnits:meter.used,proofWork:fullWork()-work,outerMs:25000,additionalEqualWorkGuard:2000000,checked,coldChecked,removalRejected,stuck:'tree'in outcome?undefined:outcome.stuck,why:'tree'in outcome?undefined:outcome.why,scope:'original safety step and original six-law context; not full M2/native admission'}))
}
for(const p of paths)if(sha(readFileSync(p))!==before[p])throw Error('source drift')
safetyContext();console.log('POSTFLIGHT',JSON.stringify({unchanged:true}))
