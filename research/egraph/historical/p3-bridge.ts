// One justified count-schema proposal, enabled/ablated on the exact P3 context.
import {readFileSync,writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {checkMC,mcGoal,type CountInst,type CountCert} from '../../../kernel/kernel.ts'
import {grow,withWall,withWork,fullWork,clock} from '../../../kernel/prove.ts'
import {Meter} from '../match.ts'
import {stableKey} from '../recover-instances.ts'
import {p3Context,sha} from './p3-context.ts'
const sources=['kernel/kernel.ts','kernel/prove.ts','research/egraph/historical/p3-context.ts','research/egraph/historical/p3-bridge.ts','research/egraph/historical/p3-cold-check.ts'],before=Object.fromEntries(sources.map(p=>[p,sha(readFileSync(p))]))
if(before['kernel/kernel.ts']!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2'||before['kernel/prove.ts']!=='5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708')throw Error('historical engine pin')
console.log('SOURCE',JSON.stringify(before))
const c=p3Context(),source=JSON.stringify([c.input.m,c.input.laws]),all=JSON.stringify(c)
for(const enabled of [false,true]){
  const started=performance.now(),work=fullWork(),meter=new Meter(100000,started+1000)
  const read=(map:string)=>{const rs=c.metadata.reads.filter(r=>{meter.tick();return r[1]===map});if(rs.length!==1)throw Error('ambiguous historical read '+map);return rs[0]!}
  const members=read('members'),missing=read('missing'),votes=read('pubVotes#')
  const d=c.base.decls.find(d=>d.map==='pubVotes#');if(!d)throw Error('missing post-vote declaration')
  let i=0,wit:string;do{meter.tick();wit='w$bridge'+i++}while(all.includes(JSON.stringify(wit)))
  const bridge:CountInst={wit,below:d.below,terms:[[1,members[0]],[-1,missing[0]],[-1,votes[0]]],unit:0}
  stableKey(bridge,meter)
  const insts=enabled?[...c.metadata.insts,bridge]:c.metadata.insts
  if(insts.length>24)throw Error('original wide instance cap')
  const metadata={reads:c.metadata.reads,picks:c.metadata.picks,insts},goal=mcGoal(c.base.goal.hyps,c.base.decls,metadata)
  if(!goal)throw Error('candidate count schema invalid')
  goal.name=c.original.name
  if(JSON.stringify(goal.hyps.slice(0,c.original.hyps.length))!==JSON.stringify(c.original.hyps))throw Error('original ordered hypotheses changed')
  stableKey(goal,meter)
  const outcome=withWall(started+25000,()=>withWork(work+2000000,()=>grow(goal,new Map(),{nodes:0,until:clock()+25000})))
  let checked=false,removalRejected:boolean|undefined,coldChecked:boolean|undefined
  if('tree'in outcome){
    const cert:CountCert={...metadata,tree:outcome.tree}
    checked=checkMC(c.base.goal.hyps,c.base.decls,cert)&&cert.insts.every(x=>!source.includes(JSON.stringify(x.wit)))
    if(enabled&&checked)removalRejected=!checkMC(c.base.goal.hyps,c.base.decls,{...cert,insts:c.metadata.insts})
    const encoded=JSON.stringify({goalSha256:c.goalSha256,enabled,cert}),path=`p3-bridge-${enabled?'enabled':'ablated'}.json`
    if(checked){
      writeFileSync(path,encoded);const cold=spawnSync('bun',['--no-install','research/egraph/historical/p3-cold-check.ts',path],{encoding:'utf8',timeout:5000});coldChecked=cold.status===0&&!cold.error&&!cold.signal
      console.log(cold.stdout.trim());if(cold.stderr)console.error(cold.stderr)
      console.log('ARTIFACT',JSON.stringify({path,sha256:sha(encoded),gzipBase64:gzipSync(encoded).toString('base64')}))
    }
  }
  console.log('P3_BRIDGE',JSON.stringify({enabled,goalSha256:c.goalSha256,originalRows:c.original.hyps.length,rows:goal.hyps.length,instances:insts.length,bridge,matchingUnits:meter.used,proofWork:fullWork()-work,outerMs:25000,additionalEqualWorkGuard:2000000,checked,removalRejected,coldChecked,stuck:'tree'in outcome?undefined:outcome.stuck,why:'tree'in outcome?undefined:outcome.why,scope:'P3 step only under original full six-law context; not a full M2 or native/full-gate result'}))
}
for(const p of sources)if(sha(readFileSync(p))!==before[p])throw Error('source changed')
p3Context();console.log('POSTFLIGHT',JSON.stringify({unchanged:true}))
