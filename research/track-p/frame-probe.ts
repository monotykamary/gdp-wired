// Check the exact direct-frame packet with and without optional quantified flags.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {frameContext} from './frame-context.ts'
import {bareRangeMap} from '../../core/count-support.ts'
import {certFor} from '../../core/counts.ts'
import {type Instances,countedObligations,checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,grow,withWall,withDeadline} from '../../kernel/prove.ts'
const dir=process.argv[2]!,data=JSON.parse(readFileSync(dir+'/production.json','utf8')) as {machine:Machine,laws:Law[]},m=data.machine,all=data.laws,sample=JSON.parse(readFileSync(dir+'/frame-case.json','utf8'))
const targets=all.filter(l=>l.keys?.length===2&&l.name.includes('Vote[')&&l.name.includes('Proposal[')&&l.name.includes('is 0'));if(targets.length!==1)throw Error('ambiguous research target')
const target=targets[0]!,support=new Set(all.filter(l=>l.name.startsWith('carry:')||l.name.startsWith('scan-prefix:'))),laws=frameContext(m,all,target,support),types=new Set(laws.filter(l=>bareRangeMap(m,l)).map(l=>l.name)),initial=sample.first.instances as Instances
for(const variant of ['all','no-flags','direct'])for(const ms of [387,1500]){
 const at=Object.fromEntries(Object.entries(initial).filter(([name])=>variant==='all'||variant==='no-flags'&&!name.startsWith('?')||variant==='direct'&&(name===target.name||types.has(name))))
 const started=performance.now(),result=withWall(started+4800,()=>counted(fullRate,()=>withDeadline(clock()+ms,()=>{
  const raw=countedObligations(m,laws,{[target.name]:at},laws.indexOf(target)).at(-1)!,cert=certFor(raw.goal,raw.decls,false,10),g=mcGoal(raw.goal.hyps,raw.decls,cert)!,q=grow(g,new Map(),{nodes:0,until:clock()+ms})
  return {hyps:g.hyps.length,insts:cert.insts.length,status:'tree'in q?'tree':q.stuck,checked:'tree'in q&&checkMC(raw.goal.hyps,raw.decls,{...cert,tree:q.tree})}
 }),true))
 console.log(JSON.stringify({variant,budget:ms,ms:performance.now()-started,...result}))
}
