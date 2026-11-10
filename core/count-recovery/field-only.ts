// Weaken only premises: discard counted conjuncts when the conclusion is a
// field claim. The resulting tree is transported back to the full obligation.
import {type C,type Machine} from '../machine.ts'
import {type CountCert,type Goal,type Path} from '../../kernel/kernel.ts'
import {walkLive} from './live-dependencies.ts'
export function fieldOnlyGoal(g:Goal,m:Machine,cert:Pick<CountCert,'reads'|'insts'>,claim?:C,path:Path=new Map()):Goal|undefined{
 const counted=new Set(cert.reads.map(r=>r[0])),maps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(i=>i.wit))
 const hasCount=(c:C)=>{let hit=false;walkLive(c,path,(o:any)=>{if(o.op==='get'&&(maps.has(o.map)||m.counts?.[o.map.replace(/#$/,'')])||o.op==='var'&&(counted.has(o.name)||wits.has(o.name)))hit=true});return hit}
 const end=g.hyps.length-cert.insts.length,original=g.hyps.slice(0,end)
 const conclusion=claim??original.at(-1),index=original.findIndex(c=>c===conclusion)
 if(!conclusion||index<0||hasCount(conclusion))return undefined
 const weaker=(c:C):C|undefined=>{
  if(c.op==='and'){const xs=c.xs.flatMap(child=>{const next=weaker(child);return next?[next]:[]});return xs.length?{op:'and',xs}:undefined}
  return hasCount(c)?undefined:c
 }
 return {...g,hyps:original.filter((_,i)=>i!==index).flatMap(c=>{const next=weaker(c);return next?[next]:[]}).concat(conclusion)}
}
