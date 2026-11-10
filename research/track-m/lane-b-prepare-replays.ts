// Prepare a bounded, deduplicated set of unchanged production root queries.
import {readFileSync,writeFileSync,readdirSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const [input,out]=process.argv.slice(2);if(!input||!out)throw Error('INPUT OUT')
const files:string[]=[];function walk(p:string){for(const d of readdirSync(p,{withFileTypes:true})){const f=join(p,d.name);if(d.isDirectory())walk(f);else if(d.name.endsWith('.json'))files.push(f)}}walk(input)
const items=new Map<string,any>(),skipped:{file:string,reason:string}[]=[]
for(const f of files){const q=JSON.parse(readFileSync(f,'utf8'));if(!q.goal?.hyps||q.outcome==='tree')continue
 if(JSON.stringify(q.goal).includes('⟦')){skipped.push({file:f,reason:'opaque column registry not captured'});continue}
 const id=createHash('sha256').update(JSON.stringify(q.goal)).digest('hex').slice(0,16),prior=items.get(id),source={file:f,kind:q.kind,priorOutcome:q.outcome,priorWall:q.ms,priorWork:q.work}
 if(prior)prior.sources.push(source);else items.set(id,{id,goal:q.goal,sources:[source]})
}
const selected=[...items.values()].sort((a,b)=>Math.max(...b.sources.map((s:any)=>s.priorWall??0))-Math.max(...a.sources.map((s:any)=>s.priorWall??0))).slice(0,96)
mkdirSync(join(out,'goals'),{recursive:true});for(const q of selected)writeFileSync(join(out,'goals',q.id+'.json'),JSON.stringify(q)+'\n')
const jobs=selected.flatMap(q=>['default','core','no-units'].map(mode=>({name:q.id+'-'+mode,cmd:'bun install --frozen-lockfile >/dev/null && timeout -s KILL 12 bun research/track-m/lane-b-replay.ts replays/goals/'+q.id+'.json '+mode,cpu:2,memory:4096,timeout:90})))
writeFileSync(join(out,'jobs.json'),JSON.stringify(jobs,null,1)+'\n');writeFileSync(join(out,'manifest.json'),JSON.stringify({rawFiles:files.length,unique:items.size,selected:selected.map(q=>({id:q.id,name:q.goal.name,hyps:q.goal.hyps.length,sources:q.sources})),skipped,jobs:jobs.length},null,1)+'\n')
console.log(JSON.stringify({rawFiles:files.length,unique:items.size,selected:selected.length,jobs:jobs.length,skipped:skipped.length}))
