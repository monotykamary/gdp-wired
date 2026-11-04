// Native root search (including built-in slicing) on the exact 242-row goal.
import {readFileSync,writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import {checkMC,countedObligations,mcGoal,type CountCert} from '../../../kernel/kernel.ts'
import {grow,widen,eprScope,queryHook,withWall,withWork,fullWork,clock} from '../../../kernel/prove.ts'
import {withProtocolPatterns} from '../pattern-once.ts'
import {focusGoal} from '../focus-goal.ts'
import {Meter} from '../match.ts'
import {stableKey} from '../recover-instances.ts'
import {safetyContext,sha} from './safety-context.ts'
import {directSafety,originalFocusInstances} from './safety-direct-context.ts'
const c=safetyContext(),focus=originalFocusInstances(c),counts=directSafety(c,focus)
const paths=['kernel/kernel.ts','kernel/prove.ts','core/solver.ts','research/egraph/historical/safety-root.ts','research/egraph/historical/safety-direct-context.ts','research/egraph/historical/safety-direct-cold.ts','research/egraph/focus-goal.ts','research/egraph/pattern-once.ts']
const source=Object.fromEntries(paths.map(p=>[p,sha(readFileSync(p))]))
if(source['kernel/prove.ts']!=='5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708')throw Error('prover pin')
console.log('SOURCE',JSON.stringify(source))
for(const patterns of [false,true]){
  const started=performance.now(),work=fullWork(),meter=new Meter(100000,started+1000)
  const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:counts.instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
  const goal=mcGoal(base.goal.hyps,base.decls,counts)!;goal.name=c.original.name
  const root=sha(JSON.stringify(goal));if(root!=='6c361c5022bd5cabfecb7c76aacf992e58459c992c6873c461a001145ce9d354')throw Error('root changed')
  const available=new Map<string,number>();for(const row of goal.hyps){const k=stableKey(row,meter);available.set(k,(available.get(k)??0)+1)}
  for(const row of c.original.hyps){const k=stableKey(row,meter),n=available.get(k)??0;if(!n)throw Error('original row absent');available.set(k,n-1)}
  const view=focusGoal(goal,base.goal.hyps.length-1)
  const run=()=>{
    const path=new Map(),budget={nodes:0,until:clock()+25000},active=eprScope.patterns
    console.log('ROOT_ENTRY',JSON.stringify({patternsRequested:patterns,patternsActive:!!active,resolvedPatterns:active??null,eprEnvironment:process.env.GDP_EPR??null,emptyPath:path.size===0,initialNodes:budget.nodes,fullRootSha256:root,searchViewSha256:sha(JSON.stringify(view))}))
    if(!!active!==patterns)throw Error('requested pattern scope not active or leaked')
    let rootObserved=false
    const previous=queryHook.on
    queryHook.on=q=>{if(q.kind==='grow'&&q.goal===view&&q.depth===0){rootObserved=true;console.log('ROOT_OBSERVED',JSON.stringify({patterns,kind:q.kind,depth:q.depth,work:q.work}))}previous?.(q)}
    let out:ReturnType<typeof grow>
    try{out=grow(view,path,budget)}finally{queryHook.on=previous}
    if(!rootObserved)throw Error('native root pipeline not observed')
    if('tree'in out){const tree=widen(view,goal,out.tree);out=tree?{...out,tree}:{stuck:'unknown',path:new Map(),why:'original-order remapping exhausted shared budget or refused'}}
    return out
  }
  const outcome=withWall(started+25000,()=>withWork(work+2000000,()=>patterns?withProtocolPatterns(c.input.m,c.input.laws,counts.instances,view,run):run()))
  let checked=false,coldChecked:boolean|undefined,packageRemovalRejected:boolean|undefined
  if('tree'in outcome){
    const cert:CountCert={reads:counts.reads,insts:counts.insts,picks:counts.picks,tree:outcome.tree}
    checked=checkMC(base.goal.hyps,base.decls,cert)
    if(checked){
      const ablated=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:focus},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
      packageRemovalRejected=!checkMC(ablated.goal.hyps,ablated.decls,{reads:c.metadata.reads,insts:c.metadata.insts,picks:c.metadata.picks,tree:outcome.tree})
      const packet=JSON.stringify({goalSha256:c.goalSha256,directEnabled:true,instances:counts.instances,cert}),path=`safety-root-${patterns}.json`;writeFileSync(path,packet)
      const cold=spawnSync('bun',['--no-install','research/egraph/historical/safety-direct-cold.ts',path],{encoding:'utf8',timeout:5000});coldChecked=cold.status===0&&!cold.error&&!cold.signal
      console.log(cold.stdout.trim());if(cold.stderr)console.error(cold.stderr)
      console.log('ARTIFACT',JSON.stringify({kind:'proof',path,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
      if(!coldChecked)process.exitCode=1
    }
  }else if(outcome.witness){
    const packet=JSON.stringify({goalSha256:c.goalSha256,fullRootSha256:root,patterns,goal,instances:counts.instances,counts,witness:outcome.witness})
    console.log('ARTIFACT',JSON.stringify({kind:'witness',path:`safety-root-witness-${patterns}.json`,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
  }
  console.log('SAFETY_ROOT',JSON.stringify({patterns,originalRows:202,rows:goal.hyps.length,fullRootSha256:root,matchingUnits:meter.used,proofWork:fullWork()-work,outerMs:25000,additionalEqualWorkGuard:2000000,checked,coldChecked,packageRemovalRejected,stuck:'tree'in outcome?undefined:outcome.stuck,why:'tree'in outcome?undefined:outcome.why,scope:'original safety step only; no full M2/native claim'}))
}
for(const p of paths)if(sha(readFileSync(p))!==source[p])throw Error('source drift')
safetyContext();console.log('POSTFLIGHT',JSON.stringify({unchanged:true}))
