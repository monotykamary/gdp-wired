import {readdirSync, readFileSync} from 'node:fs'
import {relevantGoals} from '../../core/relevance.ts'
import {type Goal, check} from '../../kernel/kernel.ts'
import {clock, counted, fullRate, fullWork, grow, widen, withDeadline, withWall} from '../../kernel/prove.ts'
const dir=process.argv[2]!, shard=Number(process.argv[3]??0), shards=Number(process.argv[4]??1), ms=Number(process.env.REPLAY_MS??1500)
const files=readdirSync(dir).filter(f=>f.endsWith('.json')).sort()
const rows=files.map(f=>({f,...JSON.parse(readFileSync(`${dir}/${f}`,'utf8'))})).filter(d=>d.outcome==='unknown'&&d.goal.hyps.length>=100)
const selected=rows.filter((_,i)=>i%shards===shard).slice(0,12)
for(const d of selected) for(const mode of (process.env.REPLAY_MODES??'full,relevant').split(',')) {
 const goal:Goal=d.goal,t=performance.now(),w=fullWork();let size=goal.hyps.length,lifted=false
 const out=withWall(performance.now()+ms*2,()=>counted(fullRate,()=>withDeadline(clock()+ms,()=>{
  const until=clock()+ms
  if(mode==='relevant') for(const part of relevantGoals(goal)) {
   const q=grow(part,new Map(),{nodes:0,until:Math.min(until,clock()+ms/4)})
   if('tree'in q){const tree=widen(part,goal,q.tree);if(tree){size=part.hyps.length;lifted=true;return {...q,tree}}}
  }
  return grow(goal,new Map(),{nodes:0,until})
 }),true))
 console.log(JSON.stringify({file:d.f,mode,was:d.kind,hyps:goal.hyps.length,part:size,lifted,outcome:'tree'in out?'tree':out.stuck,why:'tree'in out?undefined:out.why,checked:'tree'in out?check(goal,out.tree):undefined,ms:Math.round(performance.now()-t),work:Math.round(fullWork()-w)}))
}
