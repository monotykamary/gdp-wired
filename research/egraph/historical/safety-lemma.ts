// Same admitted 242-row context, count-lemma arithmetic-cut guidance versus ablation.
import {readFileSync,writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {gzipSync} from 'node:zlib'
import type {E} from '../../../core/machine.ts'
import {assumed,countedObligations,check,checkMC,mcGoal,type CountCert} from '../../../kernel/kernel.ts'
import {grow,widen,withWall,withWork,fullWork,clock} from '../../../kernel/prove.ts'
import {directSafety} from './safety-direct-context.ts'
import {lemmaCuts} from '../lemma-cuts.ts'
import {focusGoal} from '../focus-goal.ts'
import {decisionAction,guidedSplit} from '../guided-split.ts'
import {Meter} from '../match.ts'
import {stableKey} from '../recover-instances.ts'
import {safetyContext,sha} from './safety-context.ts'
const c=safetyContext(),raw=readFileSync('research/egraph/historical/recovery/safety-focus-v6.json')
if(sha(raw)!=='4d7c5adf0d85dd3f32e42ad23b0e1ded8db9b928f44e044e4fd0ae4286891a14')throw Error('candidate pin')
const proposal=JSON.parse(raw.toString()) as {goalSha256:string,lawSha256:string,keys:string[],candidates:{binding:Record<string,E>,sha256:string}[]}
if(proposal.goalSha256!==c.goalSha256||proposal.lawSha256!==sha(JSON.stringify(c.input.law))||proposal.candidates.length>32)throw Error('source candidate mismatch')
const paths=['kernel/kernel.ts','kernel/prove.ts','research/egraph/historical/safety-context.ts','research/egraph/historical/safety-direct-cold.ts','research/egraph/historical/safety-lemma.ts','research/egraph/lemma-cuts.ts','research/egraph/historical/safety-direct-context.ts','research/egraph/focus-goal.ts','research/egraph/guided-split.ts'],before=Object.fromEntries(paths.map(p=>[p,sha(readFileSync(p))]))
if(before['kernel/prove.ts']!=='5e4232da2abe25c1153edf790af4b339d2be8482c5630b0740315c79f60ce708')throw Error('prover pin')
console.log('SOURCE',JSON.stringify(before))
const decisionGuard=c.input.m.step.flags?.decides
const action=decisionAction(decisionGuard),hint={split:{op:1,'1':-action},yes:{split:{op:-1,'1':action}}}
console.log('GUIDANCE',JSON.stringify({action,decisionGuard,hint}))
for(const enabled of [false,true]){
  const started=performance.now(),work=fullWork(),meter=new Meter(100000,started+1000)
  const additional=proposal.candidates.flatMap(p=>{const at=proposal.keys.map(k=>p.binding[k]!);const rows=assumed([c.input.law],{[c.input.law.name]:at});if(rows.length!==1||sha(stableKey(rows[0],meter))!==p.sha256)throw Error('candidate reconstruction');return at})
  const focusInstances={...c.metadata.instances,[c.input.law.name]:[...(c.metadata.instances[c.input.law.name]??[]),...additional]}
  const counts=directSafety(c,focusInstances)
  const instances=counts.instances
  const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
  const goal=mcGoal(base.goal.hyps,base.decls,counts);if(!goal)throw Error('count schema');goal.name=c.original.name
  const available=new Map<string,number>();for(const row of goal.hyps){const key=stableKey(row,meter);available.set(key,(available.get(key)??0)+1)}
  for(const row of c.original.hyps){const key=stableKey(row,meter),n=available.get(key)??0;if(!n)throw Error('original row omitted');available.set(key,n-1)}
  if(sha(JSON.stringify(goal))!=='6c361c5022bd5cabfecb7c76aacf992e58459c992c6873c461a001145ce9d354')throw Error('242-row root changed')
  const names=['w$directBridge','w$directDisjoint0','w$296','w$directDisjoint2']
  const indices=names.map(name=>{const i=counts.insts.findIndex(x=>x.wit===name);if(i<0)throw Error('missing count lemma');return goal.hyps.length-counts.insts.length+i})
  const plan=lemmaCuts(goal,indices,hint)
  console.log('LEMMA_CUTS',JSON.stringify({enabled,names,cuts:plan.cuts}))
  let branchIndex=0
  const budget={nodes:0,until:clock()+25000}
  const outcome=withWall(started+25000,()=>withWork(work+2000000,()=>guidedSplit(goal,enabled?plan.hint:hint,(g,p)=>{
    const beforeWork=fullWork(),view=focusGoal(g,enabled?plan.focusIndex(p,base.goal.hyps.length-1):base.goal.hyps.length-1)
    let out=grow(view,p,budget)
    if('tree'in out){
      const tree=widen(view,g,out.tree,{},p,p)
      out=tree?{...out,tree}:{stuck:'unknown',path:p,why:'permutation remapping refused or exhausted shared budget'}
    }
    const checked='tree'in out&&check(g,out.tree,p)
    if('tree'in out&&!checked)throw Error('branch kernel rejection')
    console.log('GUIDED_BRANCH',JSON.stringify({path:[...p.values()],checked,returnedTree:'tree'in out,stuck:'tree'in out?undefined:out.stuck,work:fullWork()-beforeWork}))
    if('tree'in out){
      const packet=JSON.stringify({goalSha256:c.goalSha256,contextSha256:sha(JSON.stringify(g)),source:before,goal:g,path:[...p],tree:out.tree})
      console.log('ARTIFACT',JSON.stringify({kind:'conditional-branch',path:`safety-lemma-${enabled}-branch-${branchIndex++}.json`,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
    }
    return out
  })))
  let checked=false,coldChecked:boolean|undefined,packageRemovalRejected:boolean|undefined
  if('tree'in outcome){
    const cert:CountCert={reads:counts.reads,insts:counts.insts,picks:counts.picks,tree:outcome.tree}
    checked=checkMC(base.goal.hyps,base.decls,cert)
    if(checked){
      if(enabled){
        const ablated=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:focusInstances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
        packageRemovalRejected=!checkMC(ablated.goal.hyps,ablated.decls,{reads:c.metadata.reads,insts:c.metadata.insts,picks:c.metadata.picks,tree:outcome.tree})
      }
      const packet=JSON.stringify({goalSha256:c.goalSha256,directEnabled:true,instances,cert}),path=`safety-lemma-${enabled}.json`;writeFileSync(path,packet)
      const cold=spawnSync('bun',['--no-install','research/egraph/historical/safety-direct-cold.ts',path],{encoding:'utf8',timeout:5000});coldChecked=cold.status===0&&!cold.error&&!cold.signal
      console.log(cold.stdout.trim());if(cold.stderr)console.error(cold.stderr)
      console.log('ARTIFACT',JSON.stringify({kind:'proof',path,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
    }
  }else if(outcome.witness){
    const packet=JSON.stringify({goalSha256:c.goalSha256,enabled,instances,goal,witness:outcome.witness})
    console.log('ARTIFACT',JSON.stringify({kind:'witness',path:`safety-lemma-witness-${enabled}.json`,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
  }
  console.log('SAFETY_LEMMA',JSON.stringify({enabled,goalSha256:c.goalSha256,originalRows:202,rows:goal.hyps.length,fullRootSha256:sha(JSON.stringify(goal)),addedTuples:proposal.candidates.length+counts.addedLawTuples,countInstances:counts.insts.length,countReads:counts.reads.length,matchingUnits:meter.used,proofWork:fullWork()-work,outerMs:25000,additionalEqualWorkGuard:2000000,checked,coldChecked,packageRemovalRejected,stuck:'tree'in outcome?undefined:outcome.stuck,why:'tree'in outcome?undefined:outcome.why,scope:'original safety step and original six-law context; not full M2/native admission'}))
}
for(const p of paths)if(sha(readFileSync(p))!==before[p])throw Error('source drift')
safetyContext();console.log('POSTFLIGHT',JSON.stringify({unchanged:true}))
