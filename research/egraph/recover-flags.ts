// Templates come from countedObligations, not an assumed new law. Every recovered
// flag row must still occur in the original context and rebuilt machine goal.
import type {Law,Machine,E} from '../../core/machine.ts'
import {countedObligations,boundOf,type Goal,type Instances} from '../../kernel/kernel.ts'
import {recoverInstances} from './recover-instances.ts'
import {Meter} from './match.ts'
export function recoverFlags(goal:Goal,m:Machine,laws:Law[],focus:string,initial:Instances,meter:Meter){
  const index=laws.findIndex(l=>l.name===focus);if(index<0)throw Error('unknown focus')
  const make=(instances:Instances)=>{
    const out=countedObligations(m,laws,{[focus]:instances},index).find(x=>x.goal.name.endsWith('@step'))
    if(!out)throw Error('missing step');return out
  }
  const taken=new Set<string>()
  const walk=(o:unknown,visit:(q:Record<string,unknown>)=>void):void=>{meter.tick();if(!o||typeof o!=='object')return;visit(o as Record<string,unknown>);for(const v of Object.values(o))if(v&&typeof v==='object')walk(v,visit)}
  walk([goal,m,laws],q=>{if(q.op==='var'&&typeof q.name==='string')taken.add(q.name)})
  let serial=0;const templates:Law[]=[]
  for(const [flag,q] of Object.entries(m.step.flags??{})){
    meter.tick();if(q.op!=='all')continue
    const names=boundOf(q).map(()=>{let name:string;do{meter.tick();name=`__astra_flag_hole_${serial++}__`}while(taken.has(name));taken.add(name);return name})
    const holes:E[]=names.map(name=>({op:'var',name})),built=make({...initial,['?'+flag]:[...(initial['?'+flag]??[]),...holes]})
    const containing=built.goal.hyps.filter(row=>{let found=false;walk(row,r=>{if(r.op==='var'&&names.includes(String(r.name)))found=true});return found})
    if(containing.length!==1)throw Error('ambiguous flag template '+flag)
    templates.push({name:'?'+flag,forall:names[0]!,keys:names.slice(1),holds:containing[0]!})
  }
  // These Law-shaped objects are matching templates only; no prover receives them.
  const recovered=recoverInstances(goal,templates,meter),instances={...initial,...recovered.instances},base=make(instances)
  return {instances,records:recovered.records,templates:templates.length,base}
}
