// Direct tree search on exact packets captured from the production attempt.
import {readFileSync} from 'node:fs'
import {type Law,type Machine} from '../../core/machine.ts'
import {definitionContext} from './definition-context.ts'
import {frameContext} from './frame-context.ts'
import {countedObligations,checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,grow,withWall,withDeadline} from '../../kernel/prove.ts'
const dir=process.argv[2]!,data=JSON.parse(readFileSync(dir+'/production.json','utf8')) as {machine:Machine,laws:Law[]},m=data.machine,all=data.laws,samples=JSON.parse(readFileSync(dir+'/frame-cases.json','utf8')),support=new Set(all.filter(l=>l.name.startsWith('carry:')||l.name.startsWith('scan-prefix:'))),late=new Set<string>(JSON.parse(readFileSync(dir+'/late-context.json','utf8'))),target=all.find(l=>l.keys?.length===2&&l.name.includes('Vote[')&&l.name.includes('Proposal[')&&l.name.includes('is 0'))!
for(const sample of samples){
 const base=sample.label.startsWith('late')?all.filter(l=>late.has(l.name)):all,laws=sample.label==='frame'?frameContext(m,base,target,support):sample.label.includes('definition')?definitionContext(m,base,target,support):base,at=sample.first.instances,c=sample.first.certificateRequest,started=performance.now()
 const out=withWall(started+4800,()=>counted(fullRate,()=>{const until=clock()+387;return withDeadline(until,()=>{const raw=countedObligations(m,laws,{[target.name]:at},laws.indexOf(target)).at(-1)!,g=mcGoal(raw.goal.hyps,raw.decls,c);if(!g)return {status:'invalid'};const q=grow(g,new Map(),{nodes:0,until});return {hyps:g.hyps.length,status:'tree'in q?'tree':q.stuck,checked:'tree'in q&&checkMC(raw.goal.hyps,raw.decls,{...c,tree:q.tree})}})},true))
 console.log(JSON.stringify({label:sample.label,ms:performance.now()-started,...out}))
}
