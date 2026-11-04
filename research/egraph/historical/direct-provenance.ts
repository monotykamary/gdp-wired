// Retain the v16 package's exact source/binding map; certificate construction only, no prover.
import {readFileSync} from 'node:fs'
import {gzipSync} from 'node:zlib'
import {countedObligations,mcGoal} from '../../../kernel/kernel.ts'
import {safetyContext,sha} from './safety-context.ts'
import {directSafety,originalFocusInstances} from './safety-direct-context.ts'
const c=safetyContext(),focus=originalFocusInstances(c),d=directSafety(c,focus)
const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:d.instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
const goal=mcGoal(base.goal.hyps,base.decls,d)!;goal.name=c.original.name
const root=sha(JSON.stringify(goal));if(root!=='6c361c5022bd5cabfecb7c76aacf992e58459c992c6873c461a001145ce9d354')throw Error('not v16 augmented root')
const tuples=c.input.laws.flatMap(l=>{
  const names=[l.forall,...(l.keys??[])].filter((s):s is string=>!!s),old=focus[l.name]??[],now=d.instances[l.name]??[]
  if(JSON.stringify(now.slice(0,old.length))!==JSON.stringify(old))throw Error('lost old tuple')
  const out=[];for(let i=old.length;i<now.length;i+=names.length)out.push({law:l,lawSha256:sha(JSON.stringify(l)),bindings:Object.fromEntries(names.map((n,j)=>[n,now[i+j]!]))})
  return out
})
const readSource=(name:string)=>{const read=d.reads.find(r=>r[0]===name)!;return {read,declaration:base.decls.find(x=>x.map===read[1])!}}
const countInstances=d.insts.slice(c.metadata.insts.length).map(instance=>({instance,reads:instance.terms.map(([,name])=>readSource(name))}))
const paths=['kernel/kernel.ts','kernel/prove.ts','research/egraph/historical/safety-direct-context.ts','research/egraph/historical/inputs/m2/one-value-decided.json.gz','research/egraph/historical/recovery/safety-v11.json','research/egraph/historical/recovery/safety-focus-v6.json']
const packet=JSON.stringify({origin:'v16',source:Object.fromEntries(paths.map(p=>[p,sha(readFileSync(p))])),originalGoalSha256:c.goalSha256,fullRootSha256:root,goal,originalMetadata:c.metadata,priorFocusInstances:focus,instances:d.instances,reads:d.reads,insts:d.insts,picks:d.picks,newLawTuples:tuples,newCountInstances:countInstances,newReads:d.reads.slice(c.metadata.reads.length).map(r=>readSource(r[0])),completeProof:false})
console.log('DIRECT_PROVENANCE',JSON.stringify({root,newLawTuples:tuples.length,newCountInstances:countInstances.length,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
