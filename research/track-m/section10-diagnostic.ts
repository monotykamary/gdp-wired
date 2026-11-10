// Diagnostic-only recorder, installed into disposable copies of 192ebbe2.
import {fullRate,fullWork} from '../../kernel/prove.ts'
import {costs} from '../../core/solver.ts'
type Frame={id:number,parent?:number,kind:string,meta:any,start:number,end?:number,units?:number,children:number,exclusive?:number,counts:Record<string,number>,delta?:Record<string,number>,result?:any}
const snap=()=>({...costs}),now=()=>fullWork()/fullRate
class Diagnostic {
 label='';goal:any;frames:Frame[]=[];events:any[]=[];captures:any[]=[];private stack:Frame[]=[]
 reset(label:string){if(this.stack.length)throw new Error('open diagnostic frames');this.label=label;this.frames=[];this.events=[];this.captures=[]}
 setGoal(goal:any){this.goal=goal}
 begin(kind:string,meta:any={}):Frame{const f:Frame={id:this.frames.length,parent:this.stack.at(-1)?.id,kind,meta,start:now(),children:0,counts:snap()};this.frames.push(f);this.stack.push(f);return f}
 end(f:Frame,result?:any){if(this.stack.pop()!==f)throw new Error('diagnostic stack mismatch');f.end=now();f.units=f.end-f.start;f.exclusive=f.units-f.children;f.delta=Object.fromEntries(Object.entries(costs).map(([k,v])=>[k,v-(f.counts[k]??0)]));if(result!==undefined)f.result=result;const parent=this.stack.at(-1);if(parent)parent.children+=f.units}
 run<T>(kind:string,meta:any,fn:()=>T):T{const f=this.begin(kind,meta);try{return fn()}finally{this.end(f)}}
 call<T>(site:string,args:any[],fn:()=>T):T{const f=this.begin(site,{name:args[0]?.name,hyps:args[0]?.hyps?.length,insts:args[2]?.insts?.length??args[1]?.insts?.length});let value:any;try{value=fn();return value}finally{const result:any={};if(Array.isArray(value))result.goals=value.map(v=>({name:v.goal?.name,hyps:v.goal?.hyps?.length}));if(value?.insts)result.insts=value.insts;if(value?.reads)result.reads=value.reads;if(site.endsWith('.query')){result.tree=!!value?.tree;result.stuck=value?.stuck;result.why=value?.why;result.core=value?.core;result.witness=value?.witness;}if(site.endsWith('seedCountWitnessFlags')&&value)result.instances=value;this.end(f,result)}}
 event(kind:string,data:any){this.events.push({kind,at:now(),frame:this.stack.at(-1)?.id,...data})}
 capture(data:any,source:(index:number)=>any){const c={id:this.captures.length,at:now(),frame:this.stack.at(-1)?.id,...data,source};this.captures.push(c);this.event('numeric',{capture:c.id,closure:c.closure,path:c.path,round:c.round,query:c.query})}
 model(data:any){const c=this.captures.at(-1);if(c)c.model=data.model;this.event('model',data)}
 dump(){return JSON.parse(JSON.stringify({label:this.label,frames:this.frames,events:this.events,captures:this.captures.map(({source:_source,...rest})=>rest)},(key,value)=>key==='tree'&&value&&typeof value==='object'?{proofOmitted:true}:value))}
}
export const diagnostic=new Diagnostic()
