// Candidate cell frames: an update expression and the old cell at the end of
// its fallback chain. These are proposals only; callers must prove equality.
import {type E,walkOnce} from '../../core/machine.ts'
import {type Path} from '../../kernel/kernel.ts'
import {walkLive} from './live-dependencies.ts'
export function fieldFrames(bodies:E[],targets:E[],root:Path):{after:E,before:E}[]{
 const wanted=new Set(targets.map(e=>JSON.stringify(e))),seen=new Set<string>(),out:{after:E,before:E}[]=[]
 for(const body of bodies)walkLive(body,root,(o:any)=>{
  if(o.op!=='if')return
  let before:E=o
  while(before.op==='if')before=before.else
  const id=JSON.stringify(before);if(!wanted.has(id)||seen.has(id))return
  let member=false;walkOnce(o,(e:any)=>{if(e.op==='var'&&e.name==='$member')member=true})
  if(member)return
  seen.add(id);out.push({after:o,before})
 })
 return out.slice(0,4)
}
